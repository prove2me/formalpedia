-- Prove2me | solution 1 for GlobalTheory.FrameCompletion.isInt_gramQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:17:37.662495+00:00
-- url     : https://prove2.me/submissions/227d9e5a-4847-4f56-bcbf-4105cfa32a93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DoubledLatticePrimitiveIsotropicFrameCompletion
import Theorems.Thm_GlobalTheory_FrameCompletion_isInt_neg
import Theorems.Thm_GlobalTheory_FrameCompletion_isInt_antiJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.FrameCompletion
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
namespace GlobalTheory.FrameCompletion
theorem _root_.solution {n : ℕ} : IsInt (gramQ L n) := by
  rintro (i | i) (j | j)
  · exact isInt_antiJ i j
  · exact zero_mem _
  · exact zero_mem _
  · exact isInt_neg isInt_antiJ i j
end GlobalTheory.FrameCompletion
