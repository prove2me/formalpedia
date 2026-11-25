-- Prove2me | solution 1 for GlobalTheory.IdxInt.Model.sum_refine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:26:23.260115+00:00
-- url     : https://prove2.me/submissions/b3acbeb8-2f53-48e3-a73d-bc2fe6f056d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumRefine
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CintTranslate
import Theorems.Thm_GlobalTheory_SumRefinement_sum_refine


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open GlobalTheory GlobalTheory.IdxInt GlobalTheory.IdxInt.Model
open GlobalTheory.IdxInt
variable {W : Type} [AddCommGroup W]
namespace GlobalTheory.IdxInt.Model
theorem _root_.solution {A B C : AddSubgroup W} {φ : W → ℂ} (h : Fine A φ B) (hC : C ≤ B)
    (hi : C.relIndex B ≠ 0) :
    (∑ᶠ c : W ⧸ C, φ c.out) = (C.relIndex B : ℂ) * ∑ᶠ c : W ⧸ B, φ c.out := by
  first
  | exact @_root_.GlobalTheory.SumRefinement.sum_refine
  | exact _root_.GlobalTheory.SumRefinement.sum_refine
  | (apply _root_.GlobalTheory.SumRefinement.sum_refine <;> assumption)
  | (intros; apply _root_.GlobalTheory.SumRefinement.sum_refine <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SumRefinement.sum_refine <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SumRefinement.sum_refine ..)
end GlobalTheory.IdxInt.Model
