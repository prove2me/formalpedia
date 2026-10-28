-- Prove2me | solution 1 for GeomDL.Blueprint.blueprint_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T19:38:55.978498+00:00
-- url     : https://prove2.me/submissions/381d5f38-d752-4591-9126-ee2e0531ef13

import Mathlib
import Definitions.Def_GeomDL_Blueprint_Defs

open GeomDL.Blueprint

theorem solution {G : Type*} [Group G] {Ω Ω' : ℕ → Type*} {C D E : ℕ → Type*}
    {Y : Type*} [∀ j, MulAction G (Ω j)] [∀ j, MulAction G (Ω' j)]
    (B : ∀ j, (Ω j → C j) → (Ω' j → D j)) (σ : ∀ j, D j → E j)
    (P : ∀ j, (Ω' j → E j) → (Ω (j + 1) → C (j + 1))) (n : ℕ) (A : (Ω' n → E n) → Y)
    (hB : ∀ j, IsEquivariant (G := G) (B j)) (hP : ∀ j, IsEquivariant (G := G) (P j))
    (hA : IsInvariant (G := G) A) :
    IsInvariant (G := G) (blueprint B σ P n A) := by
  have hpw : ∀ j (g : G) (y : Ω' j → D j),
      pointwise (σ j) (act g y) = act g (pointwise (σ j) y) := fun _ _ _ => rfl
  have hst : ∀ m (g : G) (x : Ω 0 → C 0),
      blueprintStages B σ P m (act g x) = act g (blueprintStages B σ P m x) := by
    intro m
    induction m with
    | zero => intro g x; rfl
    | succ m ih =>
      intro g x
      show P m (pointwise (σ m) (B m (blueprintStages B σ P m (act g x)))) =
        act g (P m (pointwise (σ m) (B m (blueprintStages B σ P m x))))
      rw [ih, hB, hpw, hP]
  intro g x
  show A (pointwise (σ n) (B n (blueprintStages B σ P n (act g x)))) =
    A (pointwise (σ n) (B n (blueprintStages B σ P n x)))
  rw [hst, hB, hpw, hA]
