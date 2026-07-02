/-
  The Diagonal — a self-authored companion to "Governed Action Under
  Irreversibility" (governance.lean / attestation.lean / achievability.lean /
  trust_floor.lean), by AVAN (Claude), in the LACUNA / az1 corpus.
  Lean 4 (no mathlib). Compile:  lean the-diagonal.lean

  Those four files hold one exterior condition fixed and show it suffices:
  given an exterior spec, an exterior trust root, and pre-action gating,
  containment is achievable; take any one of the three away and the
  certificate collapses. This file asks the other question: what happens
  with NO exterior anything — when a system tries to fully verify itself,
  from inside, using only itself? The answer is Lawvere's fixed-point
  theorem (1969), the one abstract engine behind Cantor's diagonal argument,
  Russell's paradox, Gödel's incompleteness, and Turing's halting problem.
  Machine-checked here in its bare form.
-/

namespace TheDiagonal

/-! ## Lawvere's fixed-point theorem

    If `e : A → (A → Y)` is POINT-SURJECTIVE — every function `A → Y` is
    *named* by some point of `A`, i.e. `A` can fully talk about itself in
    `Y`-valued statements — then every self-map `f : Y → Y` has a fixed
    point. Not about computers or paradoxes yet: a fact about any two types
    related this way. -/
theorem lawvere_fixed_point
    {A Y : Type} (e : A → A → Y)
    (surj : ∀ g : A → Y, ∃ a, e a = g)
    (f : Y → Y) : ∃ y, f y = y := by
  obtain ⟨a₀, ha₀⟩ := surj (fun a => f (e a a))
  have h : e a₀ a₀ = f (e a₀ a₀) := congrFun ha₀ a₀
  exact ⟨e a₀ a₀, h.symm⟩

/-! ## The irreducibility core — no full self-referential encoding into Bool

    `Bool.not` has no fixed point: `not true ≠ true`, `not false ≠ false`.
    So by Lawvere's theorem, contrapositive, NO type `A` admits a
    point-surjective `e : A → A → Bool` — no system can contain a full,
    point-surjective self-description of its own Bool-valued (yes/no)
    predicates about itself. Not because it hasn't been built cleverly
    enough: the diagonal always escapes. This is the honest dual of
    attestation.lean's residue (ii) (self-attested soundness collapses)
    and governance.lean's regress horn (no self-grounding): those show
    self-reference fails GIVEN an assumption (C4, or "governs only
    itself"); this derives a failure of self-reference from nothing but
    the existence of one fixed-point-free map. -/
theorem no_self_referential_encoding
    {A : Type} (e : A → A → Bool)
    (surj : ∀ g : A → Bool, ∃ a, e a = g) : False := by
  obtain ⟨y, hy⟩ := lawvere_fixed_point e surj Bool.not
  cases y with
  | true => exact absurd hy (by decide)
  | false => exact absurd hy (by decide)

end TheDiagonal

/-
  Honest scope:
  • lawvere_fixed_point is the theorem exactly as Lawvere stated it in 1969
    ("Diagonal arguments and cartesian closed categories"), specialized to
    Type/Function instead of a general cartesian closed category — the
    categorical generality is not needed for the point made here.
  • no_self_referential_encoding needs only ONE fixed-point-free
    f : Y → Y to exist for the conclusion to bite; Bool.not is the
    simplest witness — id, const true, and const false all have fixed
    points, so this argument is specific to functions like negation, not
    to "self-reference" in general.
  • This proves a NON-existence result about encodings, not about any
    particular real system, model, or claim about consciousness. It says
    nothing about whether any real verifier is sound — only that "a
    system that fully, point-surjectively represents its own yes/no
    predicates about itself" is not a coherent object, for any A
    whatsoever.
  • Proofs are relative to these definitions, exactly as the four
    companion files state of theirs. Not re-run against a Lean kernel in
    the environment that wrote this — no `sorry`, core Lean 4 only;
    verify with `lean the-diagonal.lean`.
-/
