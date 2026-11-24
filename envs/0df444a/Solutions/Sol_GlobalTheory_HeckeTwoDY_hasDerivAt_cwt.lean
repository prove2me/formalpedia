-- Prove2me | solution 1 for GlobalTheory.HeckeTwoDY.hasDerivAt_cwt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:24:51.421986+00:00
-- url     : https://prove2.me/submissions/9ce86e48-5f2d-48d5-8d94-e8e918f96666

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABHasDerivAtY
import Theorems.Thm_GlobalTheory_HeckeTwoDY_conj_wt

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
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoDY
open MeasureTheory
namespace GlobalTheory.HeckeTwoDY
theorem _root_.solution (t y : ℝ) : HasDerivAt (fun y' : ℝ => (starRingEnd ℂ) (wt t y')) (-I) y := by
  have : (fun y' : ℝ => (starRingEnd ℂ) (wt t y')) = fun y' : ℝ => (t : ℂ) + (y' : ℂ) * (-I) := by
    funext y'; exact conj_wt t y'
  rw [this]
  simpa using ((hasDerivAt_id y).ofReal_comp.mul_const (-I)).const_add (t : ℂ)
end GlobalTheory.HeckeTwoDY
