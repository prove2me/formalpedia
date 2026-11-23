-- Prove2me | solution 1 for GlobalTheory.HeckeTwoC.continuous_lg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:30.997795+00:00
-- url     : https://prove2.me/submissions/9a5cdbc5-9b4c-4679-bf6b-3307e9e25aeb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
import Theorems.Thm_GlobalTheory_HeckeTwoC_tI_ne

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
theorem _root_.solution : Continuous lg := by
  unfold lg
  exact (Continuous.norm (by fun_prop)).log (fun t => (norm_pos_iff.2 (tI_ne t)).ne')
end GlobalTheory.HeckeTwoC
