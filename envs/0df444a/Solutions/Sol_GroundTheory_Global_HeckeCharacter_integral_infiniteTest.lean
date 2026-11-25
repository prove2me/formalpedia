-- Prove2me | solution 1 for GroundTheory.Global.HeckeCharacter.integral_infiniteTest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:56:26.597416+00:00
-- url     : https://prove2.me/submissions/49614393-b016-4f43-9dac-2f91ee48058e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Gaussian
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplex
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_EulerFactorsArch
import Theorems.Thm_GroundTheory_Global_integral_infinitePlaceUnitsMeasure_of_isReal
import Theorems.Thm_GroundTheory_Global_integral_infinitePlaceUnitsMeasure_of_isComplex
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_infiniteWeight_of_isReal
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_infiniteComponent_eq
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_toIdele_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteComponent
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_standardOpenSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_unitsToUnits
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteComponent_finiteUnitsSingle
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toFinite_ofFinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toInfinite_ofFinite
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_coe_circleToUnits
import Theorems.Thm_GroundTheory_Global_integral_complexGaussian_mul_zpow_mul_cpow
import Theorems.Thm_GroundTheory_Global_integral_realGaussianOdd_mul_sign_mul_abs_cpow
import Theorems.Thm_GroundTheory_Global_integral_realGaussian_mul_abs_cpow
import Theorems.Thm_GroundTheory_Global_realGaussian_eq_ofReal
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.HeckeCharacter.toIdele_diagonal
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteComponent
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_standardOpenSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_unitsToUnits
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteComponent_finiteUnitsSingle
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.toFinite_ofFinite
attribute [local simp] GroundTheory.Global.IdeleGroup.toInfinite_ofFinite
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.coe_circleToUnits
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf



set_option autoImplicit false
open NumberField InfinitePlace InfinitePlace.Completion MeasureTheory Complex ComplexConjugate
open scoped Real
open GroundTheory GroundTheory.Global
noncomputable section
open GroundTheory.Global.HeckeCharacter
variable {K : Type*} [Field K] [NumberField K] (χ : HeckeCharacter K)
namespace GroundTheory.Global.HeckeCharacter
theorem _root_.solution (w : InfinitePlace K) {s : ℂ} (hs : 0 < s.re) :
    ∫ a : (w.Completion)ˣ, χ.infiniteTest w a * χ.infiniteComponent w a *
      ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ s ∂infinitePlaceUnitsMeasure w =
      infiniteConst w * χ.infiniteGamma w s := by
  set h : w.Completion → ℂ := fun x ↦ χ.infiniteTest w x *
      (extensionEmbedding w x / (‖x‖ : ℂ)) ^ χ.infiniteWeight w *
      (((‖x‖ ^ w.mult : ℝ) : ℂ) ^ ((χ.infiniteTau w : ℂ) * I) * ((‖x‖ ^ w.mult : ℝ) : ℂ) ^ s) with hh
  have hfun : (fun a : (w.Completion)ˣ ↦ χ.infiniteTest w a * χ.infiniteComponent w a *
      ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ s) = fun a : (w.Completion)ˣ ↦ h a := by
    funext a
    simp only [h, χ.infiniteComponent_eq]
    ring
  have hs' : 0 < (s + χ.infiniteTau w * I).re := by simpa using hs
  rw [hfun]
  by_cases hw : w.IsReal
  · rw [integral_infinitePlaceUnitsMeasure_of_isReal hw, infiniteConst, infiniteGamma, if_pos hw,
      if_pos hw, one_mul]
    obtain ⟨hm0, hm2⟩ := χ.infiniteWeight_of_isReal hw
    set e := isometryEquivRealOfIsReal hw
    have hι : ∀ x : ℝ, extensionEmbedding w (e.symm x) = (x : ℂ) := fun x ↦ by
      rw [← extensionEmbeddingOfIsReal_apply hw]
      exact congrArg (fun y : ℝ ↦ (y : ℂ)) (e.apply_symm_apply x)
    have hn : ∀ x : ℝ, ‖e.symm x‖ = |x| := fun x ↦ by
      rw [← Real.norm_eq_abs, ← e.symm.isometry.norm_map_of_map_zero]
      change (ringEquivRealOfIsReal hw).symm 0 = 0
      exact map_zero _
    have hmult : (w.mult : ℝ) = 1 := by rw [mult, if_pos hw, Nat.cast_one]
    have hmult' : w.mult = 1 := by rw [mult, if_pos hw]
    rcases (show χ.infiniteWeight w = 0 ∨ χ.infiniteWeight w = 1 by omega) with h0 | h1
    · rw [h0, Int.cast_zero, add_zero, ← integral_realGaussian_mul_abs_cpow hs']
      refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
      by_cases hx : x = 0
      · simp [hx]
      have hx' : (0 : ℝ) < |x| := abs_pos.2 hx
      simp only [h, infiniteTest, h0, hn, hmult', pow_one, zpow_zero, mul_one,
        Int.natAbs_zero, pow_zero, one_mul, realGaussian_eq_ofReal, sq_abs]
      rw [← cpow_add _ _ (by exact_mod_cast hx'.ne')]
      ring_nf
    · rw [h1, Int.cast_one, ← integral_realGaussianOdd_mul_sign_mul_abs_cpow (by linarith)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
      by_cases hx : x = 0
      · simp [hx]
      have hx' : (0 : ℝ) < |x| := abs_pos.2 hx
      simp only [h, infiniteTest, h1, hι, hn, hmult', pow_one, zpow_one,
        Int.natAbs_one, if_pos zero_lt_one, conj_ofReal, realGaussianOdd, sq_abs]
      rw [← cpow_add _ _ (by exact_mod_cast hx'.ne'), ofReal_div_abs_eq_sign hx, ofReal_exp]
      push_cast
      ring_nf
  · have hc := not_isReal_iff_isComplex.1 hw
    rw [integral_infinitePlaceUnitsMeasure_of_isComplex hc, infiniteConst, infiniteGamma, if_neg hw,
      if_neg hw]
    set e := isometryEquivComplexOfIsComplex hc
    have hι : ∀ z : ℂ, extensionEmbedding w (e.symm z) = z := fun z ↦ e.apply_symm_apply z
    have hn : ∀ z : ℂ, ‖e.symm z‖ = ‖z‖ := fun z ↦ by
      rw [← e.symm.isometry.norm_map_of_map_zero]
      change (ringEquivComplexOfIsComplex hc).symm 0 = 0
      exact map_zero _
    have hmult : (w.mult : ℝ) = 2 := by rw [mult, if_neg hw, Nat.cast_ofNat]
    have hmult' : w.mult = 2 := by rw [mult, if_neg hw]
    have hs'' : 0 < (s + χ.infiniteTau w * I).re + ((-χ.infiniteWeight w).natAbs : ℝ) / 2 := by
      positivity
    have key := integral_complexGaussian_mul_zpow_mul_cpow (-χ.infiniteWeight w) hs''
    rw [Int.natAbs_neg, neg_neg] at key
    rw [← key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
    by_cases hz : z = 0
    · simp [hz]
    have hz' : (0 : ℝ) < ‖z‖ ^ 2 := by positivity
    have htest : χ.infiniteTest w (e.symm z) = complexGaussian (-χ.infiniteWeight w) z := by
      simp only [infiniteTest, hι, hn, hmult, complexGaussian, Int.natAbs_neg]
      have hexp : ((Real.exp (-(π * 2 * ‖z‖ ^ 2)) : ℝ) : ℂ) =
          Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2) := by
        rw [ofReal_exp]; push_cast; ring_nf
      rw [hexp]
      congr 1
      by_cases hm0 : 0 < χ.infiniteWeight w
      · rw [if_pos hm0, if_neg (by omega)]
      · rw [if_neg hm0, if_pos (by omega)]
    simp only [h, htest, hι, hn, hmult']
    rw [← cpow_add _ _ (by exact_mod_cast hz'.ne')]
    ring_nf
end GroundTheory.Global.HeckeCharacter
