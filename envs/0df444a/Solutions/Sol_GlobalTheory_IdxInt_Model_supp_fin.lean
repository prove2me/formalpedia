-- Prove2me | solution 1 for GlobalTheory.IdxInt.Model.supp_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:47:28.710889+00:00
-- url     : https://prove2.me/submissions/479e4aad-ac27-4fad-8827-b966a1069177

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumRefine
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CintTranslate

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
theorem _root_.solution {A B : AddSubgroup W} {φ : W → ℂ} (h : Fine A φ B) :
    (Function.support fun c : W ⧸ B => φ c.out).Finite := by
  refine h.2.2.2.subset ?_
  intro c hc
  exact ⟨c.out, hc, QuotientAddGroup.out_eq' c⟩
end GlobalTheory.IdxInt.Model
