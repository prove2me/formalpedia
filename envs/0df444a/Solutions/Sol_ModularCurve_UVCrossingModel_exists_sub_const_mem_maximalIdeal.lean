-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_sub_const_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/9c8d517c-91ba-5dbb-9a35-3e4254a4035f

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_maximalIdeal_eq_map_maximalIdeal_sup_span_pair
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_sub_const_mem_maximalIdeal

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel

theorem solution
    {W : Type*} [CommRing W] [IsLocalRing W] {π : W} (hπu : ¬IsUnit π) [IsLocalRing (UVCrossingModel W π)]
    (x : UVCrossingModel W π) :
    ∃ w : W, x - const π w ∈ IsLocalRing.maximalIdeal (UVCrossingModel W π) := by
  classical
  obtain ⟨f, rfl⟩ := mk_surjective π x

  refine ⟨MvPowerSeries.constantCoeff f, ?_⟩
  rw [maximalIdeal_eq_map_maximalIdeal_sup_span_pair hπu]
  apply Ideal.mem_sup_right

  set g : MvPowerSeries (Fin 2) W := f - MvPowerSeries.C (MvPowerSeries.constantCoeff f) with hg
  have hsub : mk π f - const π (MvPowerSeries.constantCoeff f) = mk π g := by
    simp only [hg, map_sub, const]
  rw [hsub]

  have hUV : Ideal.span ({U π, V π} : Set (UVCrossingModel W π)) =
      (Ideal.span ({MvPowerSeries.X 0, MvPowerSeries.X 1} : Set (MvPowerSeries (Fin 2) W))).map (mk π) := by
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    rfl
  rw [hUV]
  refine Ideal.mem_map_of_mem _ ?_

  have hg0 : MvPowerSeries.constantCoeff g = 0 := by
    simp [hg]

  let g₁ : MvPowerSeries (Fin 2) W := fun m => if m 0 = 0 then g m else 0
  have h1 : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W) ∣ g₁ := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm1
    change (if m 0 = 0 then g m else 0) = 0
    split_ifs with hm0
    · have hm : m = 0 := by
        ext i
        fin_cases i
        · exact hm0
        · exact hm1
      subst hm

      exact hg0
    · rfl
  have h0 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) ∣ (g - g₁) := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm0
    change g m - (if m 0 = 0 then g m else 0) = 0
    simp [hm0]
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := h1
  have hdec : g = MvPowerSeries.X 0 * a + MvPowerSeries.X 1 * b := by
    have : g = (g - g₁) + g₁ := by ring
    rw [this, ha, hb]
  rw [hdec]
  exact Ideal.add_mem _
    (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))

end S_ModularCurve_UVCrossingModel_exists_sub_const_mem_maximalIdeal
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_sub_const_mem_maximalIdeal (solution)
