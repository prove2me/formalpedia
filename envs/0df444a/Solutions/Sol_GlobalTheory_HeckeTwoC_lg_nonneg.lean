-- Prove2me | solution 1 for GlobalTheory.HeckeTwoC.lg_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:18.615875+00:00
-- url     : https://prove2.me/submissions/2a2f7d8a-f12e-4ff5-b8b8-723d32f11dda

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
import Theorems.Thm_GlobalTheory_HeckeTwoC_sq_norm_tI

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
theorem _root_.solution (t : ℝ) : 0 ≤ lg t := by
  apply Real.log_nonneg
  have h := sq_norm_tI t
  nlinarith [norm_nonneg ((t : ℂ) + I), sq_nonneg ‖t‖]
end GlobalTheory.HeckeTwoC
