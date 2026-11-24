-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QLTop.nrm_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:57:47.434604+00:00
-- url     : https://prove2.me/submissions/75a41ddc-d876-40e9-b935-62e664d45112

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBalls
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLTop
namespace GlobalTheory.CompanionTheory.QLTop
theorem _root_.solution {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ} (h : LF O ϖ nrm q) :
    1 < q ∧ ∀ x : F, nrm x ≤ 1 ↔ x ∈ O := by
  have hq : 1 < q := by rw [h.card]; exact Finite.one_lt_card
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  refine ⟨hq, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hv : ValuativeRel.valuation F ϖ < 1 := (h.lt_one ϖ).mpr ⟨1, O.one_mem, (mul_one _).symm⟩
  have hv0 : 0 < ValuativeRel.valuation F ϖ := zero_lt_iff.mpr (by simpa using h.ne)
  have hx0 : 0 < ValuativeRel.valuation F x := zero_lt_iff.mpr (by simpa using hx)
  haveI : MulArchimedean (ValuativeRel.ValueGroupWithZero F) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  have hw : 1 < (ValuativeRel.valuation F ϖ)⁻¹ := (one_lt_inv₀ hv0).mpr hv
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℤ, (ValuativeRel.valuation F ϖ)⁻¹ ^ n < ValuativeRel.valuation F x ∧
      ValuativeRel.valuation F x ≤ (ValuativeRel.valuation F ϖ)⁻¹ ^ (n + 1) := by
    obtain ⟨a, ha⟩ := exists_pow_lt₀ hv (Units.mk0 _ hx0.ne')
    obtain ⟨b, hb⟩ := exists_pow_lt₀ hv (Units.mk0 _ (inv_pos.mpr hx0).ne')
    simp only [Units.val_mk0] at ha hb
    obtain ⟨m, hm, hmin⟩ := Int.exists_least_of_bdd
      (P := fun z : ℤ => ValuativeRel.valuation F x ≤ (ValuativeRel.valuation F ϖ)⁻¹ ^ z)
      ⟨-(a : ℤ), fun z hz => by
        have h1 : (ValuativeRel.valuation F ϖ)⁻¹ ^ (-(a : ℤ)) < (ValuativeRel.valuation F ϖ)⁻¹ ^ z := by
          refine lt_of_lt_of_le ?_ hz
          simpa using ha
        exact ((zpow_lt_zpow_iff_right₀ hw).mp h1).le⟩
      ⟨(b : ℤ), by
        rw [zpow_natCast, inv_pow]
        exact ((lt_inv_comm₀ (pow_pos hv0 b) hx0).mp hb).le⟩
    refine ⟨m - 1, ?_, by simpa using hm⟩
    by_contra hc
    have := hmin _ (not_lt.mp hc)
    omega
  rw [_root_.inv_zpow] at hn1 hn2
  have hp : ∀ m : ℤ, 0 < ValuativeRel.valuation F ϖ ^ m := fun m => zpow_pos hv0 m
  have hy : ValuativeRel.valuation F (x * ϖ ^ (n + 1)) = 1 := by
    have hle : ValuativeRel.valuation F (x * ϖ ^ (n + 1)) ≤ 1 := by
      rw [map_mul, map_zpow₀]
      rwa [← one_mul (_ ⁻¹), le_mul_inv_iff₀ (hp _)] at hn2
    by_contra hne
    obtain ⟨o, ho, he⟩ := (h.lt_one _).mp (lt_of_le_of_ne hle hne)
    rw [zpow_add_one₀ h.ne, ← mul_assoc, mul_comm ϖ o] at he
    have he' := mul_right_cancel₀ h.ne he
    rw [← he', h.O_eq, Valuation.mem_integer_iff, map_mul, map_zpow₀] at ho
    rw [← one_mul (_ ⁻¹), mul_inv_lt_iff₀ (hp _)] at hn1
    exact absurd ho (not_le.mpr hn1)
  have hn := h.nrm_unit _ hy
  rw [map_mul, map_zpow₀, h.nrm_pi, _root_.inv_zpow, mul_inv_eq_one₀ (zpow_ne_zero _ (by positivity))] at hn
  rw [map_mul, map_zpow₀] at hy
  have hy' : ValuativeRel.valuation F x = (ValuativeRel.valuation F ϖ)⁻¹ ^ (n + 1) := by
    rw [_root_.inv_zpow]; exact eq_inv_of_mul_eq_one_left hy
  rw [hn, h.O_eq, Valuation.mem_integer_iff, hy', zpow_le_one_iff_right₀ hq1, zpow_le_one_iff_right₀ hw]
end GlobalTheory.CompanionTheory.QLTop
