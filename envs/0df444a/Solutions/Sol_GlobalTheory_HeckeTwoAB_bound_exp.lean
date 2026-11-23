-- Prove2me | solution 1 for GlobalTheory.HeckeTwoAB.bound_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:32.875805+00:00
-- url     : https://prove2.me/submissions/d965aec8-42fe-4c4a-a33b-0e57df696a20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABDifferentiableOnSigma

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
theorem _root_.solution {ε M c L0 D : ℝ} (hc : 1 + 2 * ε ≤ c) (hM : c ≤ M) (hD : 0 ≤ D) (hε : 0 < ε) :
    Real.exp (-c * (L0 + D)) ≤ Real.exp (M * |L0|) * Real.exp (-(1 + ε) * D) * Real.exp (-(ε * D)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 := le_abs_self L0
  have h2 := neg_abs_le L0
  have h3 := abs_nonneg L0
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ c) (by linarith : 0 ≤ |L0| + L0),
    mul_nonneg (by linarith : 0 ≤ M - c) h3, mul_nonneg (by linarith : 0 ≤ c - 1 - 2 * ε) hD]
end GlobalTheory.HeckeTwoAB
