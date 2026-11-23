-- Prove2me | solution 1 for GlobalTheory.HeckeTwoDY.conj_wt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:15.844032+00:00
-- url     : https://prove2.me/submissions/5190dc31-a98b-494a-a773-271e4dfc6195

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABHasDerivAtY

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
open GlobalTheory GlobalTheory.HeckeTwoDY
open MeasureTheory
namespace GlobalTheory.HeckeTwoDY
theorem _root_.solution (t y : ℝ) : (starRingEnd ℂ) (wt t y) = (t : ℂ) + (y : ℂ) * (-I) := by
  simp [wt, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
end GlobalTheory.HeckeTwoDY
