-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.chartHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/fdafc1d1-e977-57f5-a1e1-88bd33d9e200

import Definitions.Def_ModularCurve_UVCrossingChart
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_C_mul_of_chartHom_eq_zero
import Theorems.Thm_ModularCurve_UVCrossingModel_chartHom_C
import Theorems.Thm_ModularCurve_UVCrossingModel_const_mem_nonZeroDivisors
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_chartHom_injective

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] {π : W} (hπ : π ∈ nonZeroDivisors W) (hsep : ∀ x : W, (∀ n : ℕ, π ^ n ∣ x) → x = 0) :
    Function.Injective (chartHom π) :=
  by
  have hcancel := ModularCurve.UVCrossingModel.const_mem_nonZeroDivisors (W := W) hπ

  have iter : ∀ {f : PowerSeries W}, chartHom π f = 0 → ∀ n : ℕ,
      ∃ g : PowerSeries W, f = PowerSeries.C π ^ n * g ∧ chartHom π g = 0 := by
    intro f hf n
    induction n with
    | zero => exact ⟨f, by rw [pow_zero, one_mul], hf⟩
    | succ n ih =>
      obtain ⟨g, hg, hg0⟩ := ih
      obtain ⟨g₁, hg₁⟩ := ModularCurve.UVCrossingModel.exists_C_mul_of_chartHom_eq_zero hg0
      refine ⟨g₁, by rw [hg, hg₁, pow_succ]; ring, ?_⟩
      have h2 : chartHom π g₁ * const π π = 0 := by
        rw [mul_comm, ← ModularCurve.UVCrossingModel.chartHom_C, ← map_mul, ← hg₁, hg0]
      exact (mem_nonZeroDivisors_iff.mp hcancel).2 _ h2
  refine (injective_iff_map_eq_zero _).mpr fun f hf => ?_
  refine PowerSeries.ext fun m => ?_
  rw [map_zero]
  refine hsep _ fun n => ?_
  obtain ⟨g, hg, -⟩ := iter hf n
  rw [hg, ← map_pow, PowerSeries.coeff_C_mul]
  exact dvd_mul_right _ _

end S_ModularCurve_UVCrossingModel_chartHom_injective
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_chartHom_injective (solution)
