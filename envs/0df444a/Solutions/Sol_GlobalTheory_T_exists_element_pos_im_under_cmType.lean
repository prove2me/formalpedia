-- Prove2me | solution 1 for GlobalTheory.T.exists_element_pos_im_under_cmType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:06:51.080911+00:00
-- url     : https://prove2.me/submissions/3ba7c881-f158-46b2-a470-355644192c11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsElementPosImUnderCmType
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsElementPosImUnderCmTypeStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∃ θ : E, ∀ i, 0 < (φ i θ).im := by
  first | exact @GlobalTheory.CMTypeImPos.exists_im_pos | exact GlobalTheory.CMTypeImPos.exists_im_pos | (intros; apply GlobalTheory.CMTypeImPos.exists_im_pos <;> assumption)
end _root_.GlobalTheory.T
