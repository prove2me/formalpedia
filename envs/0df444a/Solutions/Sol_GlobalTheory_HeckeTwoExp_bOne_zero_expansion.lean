-- Prove2me | solution 1 for GlobalTheory.HeckeTwoExp.bOne_zero_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:38:42.877583+00:00
-- url     : https://prove2.me/submissions/bee99ba6-278b-4d4e-9290-289e91bf70f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformSigmaZeroEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHilbertEisensteinWeightTwoQSeriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinWeightTwoQExpansion
import Theorems.Thm_GlobalTheory_HeckeTwoExp_fTerm_zero
import Theorems.Thm_GlobalTheory_HeckeTwoExp_dF_pos
import Theorems.Thm_GlobalTheory_HeckeTwoExp_kFac_zero_mul
import Theorems.Thm_GlobalTheory_HeckeTwoExp_nrm_ne_zero
import Theorems.Thm_GlobalTheory_HeckeTwoExp_tsum_qClass_eq
import Theorems.Thm_GlobalTheory_LipschitzTR_remb_apply
import Theorems.Thm_GlobalTheory_T_summable_hilbertEisensteinWeightTwoQSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LipschitzTR.remb_apply



set_option autoImplicit false
noncomputable section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open GlobalTheory GlobalTheory.HeckeTwoExp
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeTwoExp
theorem _root_.solution [IsTotallyReal F] (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (hz : z ∈ upperHalf F) :
    Summable (qClass 𝔞 𝔟 2 z) ∧
      (cK F 2 : ℂ) * (kFac F 0 * (omegaFactor 𝔞 : ℂ) * bOne 𝔞 𝔟 0 z) / (omegaFactor 𝔞 : ℂ) ^ 2 =
        ∑' c, qClass 𝔞 𝔟 2 z c := by
  have hS := GlobalTheory.T.summable_hilbertEisensteinWeightTwoQSeries F 𝔞 𝔟 z hz
  refine ⟨hS, ?_⟩
  have hn : (nrm 𝔞 : ℂ) ≠ 0 := by exact_mod_cast nrm_ne_zero 𝔞
  have hs : ((dF F ^ ((1 : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (dF_pos (F := F)) _).ne'
  have hcK : (cK F 2 : ℂ) = ((dF F ^ ((1 : ℝ) / 2) : ℝ) : ℂ) := by
    unfold cK; norm_num
  have hL : (cK F 2 : ℂ) * (kFac F 0 * (omegaFactor 𝔞 : ℂ) * bOne 𝔞 𝔟 0 z) / (omegaFactor 𝔞 : ℂ) ^ 2 =
      (kFac F 0 / (nrm 𝔞 : ℂ)) * bOne 𝔞 𝔟 0 z := by
    rw [hcK, omegaFactor]; push_cast
    push_cast at hs
    field_simp
  rw [hL, bOne, ← tsum_mul_left, tsum_qClass_eq 𝔞 𝔟 z hS]
  refine tsum_congr fun c => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun ν => ?_
  rw [fTerm_zero hz c.out.2.2 ν.2.2]
  split_ifs with hc
  · have hk := kFac_zero_mul (F := F)
    unfold qTerm
    simp only [show (2:ℕ) - 1 = 1 from rfl, pow_one, Complex.ofReal_div]
    linear_combination (((|(Algebra.norm ℚ ν.1 : ℝ)| : ℝ) : ℂ) / (nrm 𝔞 : ℂ) * qPow (ν.1 * c.out.1) z) * hk
  · rw [mul_zero]
end GlobalTheory.HeckeTwoExp
