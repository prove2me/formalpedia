-- Prove2me | solution 1 for HunterPDE.Sobolev.iteratedPartial_mul
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T17:59:55.418352+00:00
-- url     : https://prove2.me/submissions/b2af8b4c-b79c-4bab-a6ed-cb93b5a163d4

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Theorems.Thm_ContDiff_ordered_directional_mul

open HunterPDE.Sobolev
set_option autoImplicit false

theorem solution {n : ℕ}
    (u v : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (β : Fin n → ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    iteratedPartial β (fun y => u y * v y) x =
      ∑ γ ∈ Finset.Iic β, (∏ i, (Nat.choose (β i) (γ i) : ℝ)) *
        (iteratedPartial (fun i => β i - γ i) u x * iteratedPartial γ v x) := by
  exact ContDiff.ordered_directional_mul
    (fun i => EuclideanSpace.single i 1) β u v hu hv x
