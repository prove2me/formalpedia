-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.FactorBound.norm_iteratedFDeriv_eRe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:09:43.878818+00:00
-- url     : https://prove2.me/submissions/ac255382-600d-4c9e-a4f6-ef3d5f9f351a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivHeckeFourierFactorLe
import Theorems.Thm_GlobalTheory_HeckeTwo_FactorBound_contDiff_eChar
import Theorems.Thm_GlobalTheory_HeckeTwo_FactorBound_norm_iteratedFDeriv_eChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.FactorBound
namespace GlobalTheory.HeckeTwo.FactorBound
theorem _root_.solution (a : ℝ) (i : ℕ) (w : ℂ) :
    ‖iteratedFDeriv ℝ i (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((a * w.re : ℝ) : ℂ))) w‖ ≤
      (2 * Real.pi * |a|) ^ i := by
  set L : ℂ →L[ℝ] ℝ := a • Complex.reCLM
  have hf : (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((a * w.re : ℝ) : ℂ))) =
      (fun x : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * (x : ℂ))) ∘ L := by
    funext w; simp [L]
  rw [hf, L.iteratedFDeriv_comp_right contDiff_eChar w le_top]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_eChar, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hL : ‖L‖ ≤ |a| := by
    simp only [L]
    refine (norm_smul_le _ _).trans ?_
    simp [Complex.reCLM_norm]
  rw [mul_pow (2 * Real.pi) |a| i]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hL i) (pow_nonneg (mul_nonneg zero_le_two Real.pi_pos.le) _)
end GlobalTheory.HeckeTwo.FactorBound
