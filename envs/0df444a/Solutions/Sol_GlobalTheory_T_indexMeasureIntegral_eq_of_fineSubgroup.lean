-- Prove2me | solution 1 for GlobalTheory.T.indexMeasureIntegral_eq_of_fineSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:53:44.296935+00:00
-- url     : https://prove2.me/submissions/b0518c89-b91f-413e-b084-3ef61c89984c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralEqOfFineSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralEqOfFineSubgroupStatement
import Theorems.Thm_GlobalTheory_IdxInt_cint_eq_of_fine


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.IdxInt
open scoped Pointwise Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {W : Type} [AddCommGroup W] (A B : AddSubgroup W) (φ : W → ℂ), Fine A φ B → cint A φ = (∑ᶠ c : W ⧸ B, φ c.out) / (B.relIndex A : ℂ) := by
  first | exact @GlobalTheory.IdxInt.cint_eq_of_fine | exact GlobalTheory.IdxInt.cint_eq_of_fine | (intros; apply GlobalTheory.IdxInt.cint_eq_of_fine <;> assumption)
end _root_.GlobalTheory.T
