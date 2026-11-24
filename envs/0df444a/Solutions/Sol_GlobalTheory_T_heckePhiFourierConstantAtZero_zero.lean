-- Prove2me | solution 1 for GlobalTheory.T.heckePhiFourierConstantAtZero_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:12:14.971385+00:00
-- url     : https://prove2.me/submissions/da490045-bb6f-4708-81c9-d7d5f6c1ad20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroZeroStatement
import Theorems.Thm_GlobalTheory_HeckeTwo_cConst_zero


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
theorem _root_.solution : GlobalTheory.HeckeTwo.cConst 0 = 0 := by
  first | exact @GlobalTheory.HeckeTwo.cConst_zero | exact GlobalTheory.HeckeTwo.cConst_zero | (intros; apply GlobalTheory.HeckeTwo.cConst_zero <;> assumption)
end _root_.GlobalTheory.T
