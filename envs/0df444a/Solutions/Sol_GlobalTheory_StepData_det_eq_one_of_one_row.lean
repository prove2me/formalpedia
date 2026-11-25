-- Prove2me | solution 1 for GlobalTheory.StepData.det_eq_one_of_one_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:12:43.834873+00:00
-- url     : https://prove2.me/submissions/121eaf39-a865-4d59-ab48-14a042d36a9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IteratedDepthOneLevelCharOfOneRowFirstBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open GlobalTheory GlobalTheory.StepData
namespace GlobalTheory.StepData
theorem _root_.solution {k n : Type*} [Field k] [Fintype n] [DecidableEq n] (M : Matrix n n k) (i : n)
    (h : ∀ a b, a ≠ i → M a b = (1 : Matrix n n k) a b) (hii : M i i = 1) : M.det = 1 := by
  have e : M = 1 + replicateCol Unit (Pi.single i (1 : k)) * replicateRow Unit (M i - Pi.single i (1 : k)) := by
    ext a b
    by_cases ha : a = i
    · subst ha
      by_cases hb : b = a
      · subst hb; simp [Matrix.mul_apply, hii]
      · simp [Matrix.mul_apply, Matrix.one_apply, Pi.single_apply, hb, Ne.symm hb]
    · simp [Matrix.mul_apply, h a b ha, Pi.single_apply, ha]
  rw [e, det_one_add_replicateCol_mul_replicateRow]
  simp [hii]
end GlobalTheory.StepData
