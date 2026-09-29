-- Prove2me | solution 1 for NumberField.InfinitePlace.natCard_units_completion_quotient_range_powMonoidHom_of_isReal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/dec9f6de-1f60-5317-b932-2f09ee349cbe

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfinitePlace_natCard_units_completion_quotient_range_powMonoidHom_of_isReal

set_option autoImplicit false

theorem P2mS26ArchPowR.index_range_powMonoidHom_congr {G H : Type*} [CommGroup G] [CommGroup H] (φ : G ≃* H) (n : ℕ) :
    (powMonoidHom n : G →* G).range.index = (powMonoidHom n : H →* H).range.index := by
  rw [← Subgroup.index_map_of_bijective (f := φ.toMonoidHom) φ.bijective, ← MonoidHom.range_comp]
  have hc : φ.toMonoidHom.comp (powMonoidHom n) = (powMonoidHom n).comp φ.toMonoidHom := by
    ext x; simp
  rw [hc, MonoidHom.range_comp, MonoidHom.range_eq_top.2 φ.surjective, ← MonoidHom.range_eq_map]

theorem P2mS26ArchPowR.range_powMonoidHom_real_units_eq_top_of_odd {n : ℕ} (hn : Odd n) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range = ⊤ := by
  have hn0 : n ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hn
  rw [eq_top_iff]
  rintro u -
  rcases le_or_gt 0 (u : ℝ) with hu | hu
  · have hy : ((u : ℝ) ^ ((n : ℝ)⁻¹)) ^ n = u := Real.rpow_inv_natCast_pow hu hn0
    have hy0 : (u : ℝ) ^ ((n : ℝ)⁻¹) ≠ 0 := by
      intro h; rw [h, zero_pow hn0] at hy; exact u.ne_zero hy.symm
    exact ⟨Units.mk0 _ hy0, Units.ext (by simp [hy])⟩
  · have hu' : 0 ≤ -(u : ℝ) := by linarith
    have hy : (-((-(u : ℝ)) ^ ((n : ℝ)⁻¹))) ^ n = u := by
      rw [Odd.neg_pow hn, Real.rpow_inv_natCast_pow hu' hn0, neg_neg]
    have hy0 : -((-(u : ℝ)) ^ ((n : ℝ)⁻¹)) ≠ 0 := by
      intro h; rw [h, zero_pow hn0] at hy; exact u.ne_zero hy.symm
    exact ⟨Units.mk0 _ hy0, Units.ext (by simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, hy])⟩

theorem P2mS26ArchPowR.range_powMonoidHom_real_units_eq_posSubgroup {n : ℕ} (hn : Even n) (hn0 : n ≠ 0) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range = Units.posSubgroup ℝ := by
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    simp only [Units.mem_posSubgroup, powMonoidHom_apply, Units.val_pow_eq_pow_val]
    exact hn.pow_pos v.ne_zero
  · intro hu
    rw [Units.mem_posSubgroup] at hu
    have hy : ((u : ℝ) ^ ((n : ℝ)⁻¹)) ^ n = u := Real.rpow_inv_natCast_pow hu.le hn0
    have hy0 : (u : ℝ) ^ ((n : ℝ)⁻¹) ≠ 0 := by
      intro h; rw [h, zero_pow hn0] at hy; exact u.ne_zero hy.symm
    exact ⟨Units.mk0 _ hy0, Units.ext (by simp [hy])⟩

theorem P2mS26ArchPowR.index_posSubgroup_real : (Units.posSubgroup ℝ).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨-1, fun b => ?_⟩
  simp only [Units.mem_posSubgroup, Units.val_neg, mul_neg, mul_one]
  rcases lt_or_gt_of_ne b.ne_zero with h | h
  · exact Or.inl ⟨by linarith, by linarith⟩
  · exact Or.inr ⟨h, by linarith⟩

theorem P2mS26ArchPowR.index_range_powMonoidHom_real_units {n : ℕ} (hn : 0 < n) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range.index = if Even n then 2 else 1 := by
  split_ifs with h
  · rw [range_powMonoidHom_real_units_eq_posSubgroup h hn.ne', index_posSubgroup_real]
  · rw [range_powMonoidHom_real_units_eq_top_of_odd (Nat.not_even_iff_odd.1 h), Subgroup.index_top]

theorem solution {K : Type*} [Field K]
    (w : NumberField.InfinitePlace K) (hw : w.IsReal) {n : ℕ} (hn : 0 < n) :
    Nat.card ((w.Completion)ˣ ⧸ (powMonoidHom n : (w.Completion)ˣ →* (w.Completion)ˣ).range)
      = if Even n then 2 else 1 := by
  rw [← Subgroup.index_eq_card,
    P2mS26ArchPowR.index_range_powMonoidHom_congr
      (Units.mapEquiv (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).toMulEquiv) n,
    P2mS26ArchPowR.index_range_powMonoidHom_real_units hn]

end S_NumberField_InfinitePlace_natCard_units_completion_quotient_range_powMonoidHom_of_isReal
end P2MW
export P2MW.S_NumberField_InfinitePlace_natCard_units_completion_quotient_range_powMonoidHom_of_isReal (solution)
