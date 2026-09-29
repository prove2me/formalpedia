-- Prove2me | solution 1 for GribovRegion.region_convex_body
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T05:46:00.769532+00:00
-- url     : https://prove2.me/submissions/39de31b8-5683-49b2-88a7-aafb14decd07

import Definitions.Def_gribov_region_model
import Theorems.Thm_GribovRegion_zero_mem_region
import Theorems.Thm_GribovRegion_convex_region
import Theorems.Thm_GribovRegion_region_bounded_along_rays
import Theorems.Thm_GribovRegion_region_isBounded

set_option autoImplicit false

open GribovRegion

theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (m : FPModel V n)
    (hinj : Function.Injective m.lin) :
    (0 : V) ∈ region m ∧
      Convex ℝ (region m) ∧
      (∀ A : V, A ≠ 0 → ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ l : ℝ, l₀ ≤ l → l • A ∉ region m) ∧
      Bornology.IsBounded (region m) := by
  refine ⟨GribovRegion.zero_mem_region m, GribovRegion.convex_region m, ?_,
          GribovRegion.region_isBounded m hinj⟩
  intro A hA
  -- `m.lin` is linear and injective, so `A ≠ 0` gives `m.lin A ≠ 0`
  have hlin : m.lin A ≠ 0 := by
    intro h0
    exact hA (hinj (h0.trans (map_zero m.lin).symm))
  exact GribovRegion.region_bounded_along_rays m A hlin

#print axioms solution
