-- Prove2me | solution 1 for GlobalTheory.T.heckePhiFourierConstantAtZero_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:39:31.353691+00:00
-- url     : https://prove2.me/submissions/d911e1e1-0c89-4d11-989f-f0ca2a2029f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOnStatement
import Theorems.Thm_GlobalTheory_HeckeTwo_cConst_differentiableOn


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : DifferentiableOn ℂ GlobalTheory.HeckeTwo.cConst GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane := by
  first | exact @GlobalTheory.HeckeTwo.cConst_differentiableOn | exact GlobalTheory.HeckeTwo.cConst_differentiableOn | (intros; apply GlobalTheory.HeckeTwo.cConst_differentiableOn <;> assumption)
end _root_.GlobalTheory.T
