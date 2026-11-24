-- Prove2me | solution 1 for GlobalTheory.HeckeTwoAB.bound_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:19:49.825123+00:00
-- url     : https://prove2.me/submissions/eb391d99-1638-4512-863f-0d255a731fda

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABDifferentiableOnSigma
import Theorems.Thm_GlobalTheory_HeckeTwoAB_norm_F
import Theorems.Thm_GlobalTheory_HeckeTwoAB_bound_exp
import Theorems.Thm_GlobalTheory_HeckeTwoC_lg_nonneg


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
open GlobalTheory GlobalTheory.HeckeTwoAB
open MeasureTheory GlobalTheory.HeckeTwoC
namespace GlobalTheory.HeckeTwoAB
theorem _root_.solution {ε M : ℝ} (hε : 0 < ε) (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) {σ : ℂ}
    (hc : 1 + 2 * ε ≤ (a + b : ℝ) + 2 * σ.re) (hM : (a + b : ℝ) + 2 * σ.re ≤ M) (t : ℝ) :
    ‖F a b ν y σ t‖ ≤ Real.exp (M * |Real.log (abs y)|) * Real.exp (-(1 + ε) * lg (t / y)) := by
  rw [norm_F a b ν hy]
  have hD := lg_nonneg (t / y)
  have h := bound_exp (L0 := Real.log |y|) hc hM hD hε
  have h2 : Real.exp (-(ε * lg (t / y))) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  calc Real.exp (-((a + b : ℝ) + 2 * σ.re) * L y t)
      ≤ Real.exp (M * |Real.log (abs y)|) * Real.exp (-(1 + ε) * lg (t / y)) * Real.exp (-(ε * lg (t / y))) := h
    _ ≤ Real.exp (M * |Real.log (abs y)|) * Real.exp (-(1 + ε) * lg (t / y)) * 1 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := mul_one _
end GlobalTheory.HeckeTwoAB
