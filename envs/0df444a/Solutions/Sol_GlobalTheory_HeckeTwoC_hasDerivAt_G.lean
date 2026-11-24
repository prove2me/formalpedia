-- Prove2me | solution 1 for GlobalTheory.HeckeTwoC.hasDerivAt_G
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:23:15.438+00:00
-- url     : https://prove2.me/submissions/800dd77a-38ed-47d2-991c-03999f8f9e61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn

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
open GlobalTheory GlobalTheory.HeckeTwoC
open MeasureTheory
namespace GlobalTheory.HeckeTwoC
theorem _root_.solution (σ : ℂ) (t : ℝ) : HasDerivAt (fun s => G s t) (G' σ t) σ := by
  unfold G G'
  have h : HasDerivAt (fun s : ℂ => (lg t : ℂ) * (-2 * s)) ((lg t : ℂ) * (-2)) σ := by
    exact (((hasDerivAt_id σ).const_mul (-2 : ℂ)).const_mul (lg t : ℂ)).congr_deriv (by ring)
  exact h.cexp.const_mul _
end GlobalTheory.HeckeTwoC
