-- Prove2me | solution 1 for GlobalTheory.IdxInt.Model.fine_ind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:46:03.01116+00:00
-- url     : https://prove2.me/submissions/23d41aad-7a1d-440d-b791-4a504de681c9

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
theorem _root_.solution {A B : AddSubgroup W} (hB : B ≤ A) (hi : B.relIndex A ≠ 0) :
    Fine A (ind (· ∈ B)) B := by
  refine ⟨hB, hi, ?_, ?_⟩
  · intro w b hb
    simp [ind, B.add_mem_cancel_right hb]
  · refine (Set.finite_singleton (0 : W ⧸ B)).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    have : w ∈ B := by simpa [ind] using hw
    simpa using this
end GlobalTheory.IdxInt.Model
