-- Prove2me | solution 1 for GlobalTheory.T.heckeEisensteinNonconstantFourierSum_smoothHolomorphic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:02:58.661827+00:00
-- url     : https://prove2.me/submissions/b54299aa-3517-4b59-82f6-9b31aabf19cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinNonconstantFourierSumSmoothHolomorphic
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinNonconstantFourierSumSmoothHolomoStatement
import Theorems.Thm_GlobalTheory_HeckeTwo_bOne_isGood


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), GlobalTheory.HeckeTwo.IsGood (GlobalTheory.HeckeTwo.bOne 𝔞 𝔟) := by
  first | exact @GlobalTheory.HeckeTwo.bOne_isGood | exact GlobalTheory.HeckeTwo.bOne_isGood | (intros; apply GlobalTheory.HeckeTwo.bOne_isGood <;> assumption)
end _root_.GlobalTheory.T
