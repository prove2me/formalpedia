-- Prove2me | solution 1 for GlobalTheory.HeckeTwoDY.conj_wt_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:04:32.6728+00:00
-- url     : https://prove2.me/submissions/1a18efba-6db0-4899-94a3-2e51edfd3082

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABHasDerivAtY
import Theorems.Thm_GlobalTheory_HeckeTwoDY_wt_ne

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
theorem _root_.solution {t y : ℝ} (hy : y ≠ 0) : (starRingEnd ℂ) (wt t y) ≠ 0 := by
  rw [map_ne_zero]; exact wt_ne hy
end GlobalTheory.HeckeTwoDY
