-- Prove2me | solution 1 for GlobalTheory.HeckeTwoAB.hasDerivAt_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:23:08.486872+00:00
-- url     : https://prove2.me/submissions/90187aa9-407c-4c3b-8f42-330ea854bef8

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
theorem _root_.solution (a b : ℕ) (ν y : ℝ) (σ : ℂ) (t : ℝ) :
    HasDerivAt (fun s => F a b ν y s t) (F' a b ν y σ t) σ := by
  unfold F F'
  have h : HasDerivAt (fun s : ℂ => (L y t : ℂ) * (-2 * s)) ((L y t : ℂ) * (-2)) σ := by
    exact (((hasDerivAt_id σ).const_mul (-2 : ℂ)).const_mul (L y t : ℂ)).congr_deriv (by ring)
  exact (h.cexp.const_mul _).mul_const _
end GlobalTheory.HeckeTwoAB
