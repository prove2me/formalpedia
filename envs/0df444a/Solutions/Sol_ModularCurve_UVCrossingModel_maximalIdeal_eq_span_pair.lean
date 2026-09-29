-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.maximalIdeal_eq_span_pair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c2d29fca-e8c2-534b-be16-10dae7bc23d6

import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_U_mul_V
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_maximalIdeal_eq_span_pair

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "UVCrossingModel UVCrossingModel.U_mul_V"
p2m_open "ModularCurve"

namespace PortB3

p2m_open "IsLocalRing ModularCurve.UVCrossingModel"

universe u

theorem mem_span_X_pair_of_constantCoeff_eq_zero {W : Type u} [CommRing W]
    {f : MvPowerSeries (Fin 2) W} (hf : MvPowerSeries.constantCoeff f = 0) :
    f ∈ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1} := by
  classical

  obtain ⟨g, hg⟩ : ∃ g : MvPowerSeries (Fin 2) W,
      g = fun m => if m 0 = 0 then MvPowerSeries.coeff m f else 0 := ⟨_, rfl⟩
  have hgcoeff : ∀ m : Fin 2 →₀ ℕ, MvPowerSeries.coeff m g =
      if m 0 = 0 then MvPowerSeries.coeff m f else 0 := by
    intro m
    simp only [hg, MvPowerSeries.coeff_apply]

  have h0 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) ∣ f - g := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [map_sub, hgcoeff m, if_pos hm, sub_self]

  have h1 : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W) ∣ g := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [hgcoeff m]
    by_cases hm0 : m 0 = 0
    · rw [if_pos hm0]
      have hmz : m = 0 := by
        ext i
        fin_cases i
        · simpa using hm0
        · simpa using hm
      rw [hmz, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact hf
    · rw [if_neg hm0]

  have hsplit : f = (f - g) + g := by ring
  rw [hsplit]
  refine Ideal.add_mem _ ?_ ?_
  · obtain ⟨c, hc⟩ := h0
    rw [hc]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
  · obtain ⟨c, hc⟩ := h1
    rw [hc]
    exact Ideal.mul_mem_right _ _
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem maximalIdeal_mvPowerSeries_fin_two {W : Type u} [CommRing W] [IsLocalRing W] {ϖ : W}
    (hW : maximalIdeal W = Ideal.span {ϖ}) :
    maximalIdeal (MvPowerSeries (Fin 2) W) =
      Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1,
        MvPowerSeries.C ϖ} := by
  apply le_antisymm
  ·
    intro f hf
    rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff] at hf
    have hcc : MvPowerSeries.constantCoeff f ∈ Ideal.span {ϖ} := by
      rw [← hW, mem_maximalIdeal, mem_nonunits_iff]
      exact hf
    rw [Ideal.mem_span_singleton'] at hcc
    obtain ⟨c, hc⟩ := hcc
    have hsplit : f = (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) +
        MvPowerSeries.C c * MvPowerSeries.C ϖ := by
      rw [← map_mul, hc]
      ring
    rw [hsplit]
    refine Ideal.add_mem _ ?_ ?_
    ·
      refine Ideal.span_mono
        (Set.insert_subset_insert (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))) ?_
      apply mem_span_X_pair_of_constantCoeff_eq_zero
      rw [map_sub, MvPowerSeries.constantCoeff_C, sub_self]
    ·
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))
  ·
    rw [Ideal.span_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have hϖ : ¬IsUnit ϖ := by
      have hϖm : ϖ ∈ maximalIdeal W := by
        rw [hW]
        exact Ideal.subset_span rfl
      rwa [mem_maximalIdeal, mem_nonunits_iff] at hϖm
    rcases hx with rfl | rfl | rfl
    · rw [SetLike.mem_coe, mem_maximalIdeal, mem_nonunits_iff,
        MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X]
      exact not_isUnit_zero
    · rw [SetLike.mem_coe, mem_maximalIdeal, mem_nonunits_iff,
        MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X]
      exact not_isUnit_zero
    · rw [SetLike.mem_coe, mem_maximalIdeal, mem_nonunits_iff,
        MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_C]
      exact hϖ

variable {W : Type u} [CommRing W]

theorem const_pow (π : W) (w : W) (n : ℕ) : const π (w ^ n) = const π w ^ n := by
  show mk π (MvPowerSeries.C (w ^ n)) = mk π (MvPowerSeries.C w) ^ n
  rw [map_pow, map_pow]

theorem maximalIdeal_eq_span [IsLocalRing W] {ϖ : W} (hW : maximalIdeal W = Ideal.span {ϖ})
    (π : W) [IsLocalRing (UVCrossingModel W π)] :
    maximalIdeal (UVCrossingModel W π) = Ideal.span {U π, V π, const π ϖ} := by
  have hmap := map_maximalIdeal_of_surjective (mk π) (mk_surjective π)
  rw [← hmap, maximalIdeal_mvPowerSeries_fin_two hW, Ideal.map_span]
  congr 1
  rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  rfl

theorem U_mem_maximalIdeal [IsLocalRing W] (π : W) [IsLocalRing (UVCrossingModel W π)] :
    U π ∈ maximalIdeal (UVCrossingModel W π) := by
  rw [← map_maximalIdeal_of_surjective (mk π) (mk_surjective π)]
  refine Ideal.mem_map_of_mem _ ?_
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
    MvPowerSeries.constantCoeff_X]
  exact not_isUnit_zero

end PortB3

end ModularCurve

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_UVCrossingModel_maximalIdeal_eq_span_pair.ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] [IsLocalRing W] {π : W} (hW : IsLocalRing.maximalIdeal W = Ideal.span {π}) [IsLocalRing (UVCrossingModel W π)] :
    IsLocalRing.maximalIdeal (UVCrossingModel W π) = Ideal.span {U π, V π} :=
  by
  rw [ModularCurve.PortB3.maximalIdeal_eq_span hW π, ← ModularCurve.UVCrossingModel.U_mul_V π]

  apply le_antisymm
  · rw [Ideal.span_le]
    rintro x (rfl | rfl | rfl)
    · exact Ideal.subset_span (by simp)
    · exact Ideal.subset_span (by simp)
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · exact Ideal.span_mono (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp)

end S_ModularCurve_UVCrossingModel_maximalIdeal_eq_span_pair
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_maximalIdeal_eq_span_pair (solution)
