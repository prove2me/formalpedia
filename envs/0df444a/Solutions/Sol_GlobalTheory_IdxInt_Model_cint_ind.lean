-- Prove2me | solution 1 for GlobalTheory.IdxInt.Model.cint_ind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:50:55.653663+00:00
-- url     : https://prove2.me/submissions/71c5cfb9-bb87-47ea-8071-1f7ce2bd8098

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumRefine
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CintTranslate
import Theorems.Thm_GlobalTheory_IdxInt_Model_out_mk
import Theorems.Thm_GlobalTheory_IdxInt_Model_cint_eq
import Theorems.Thm_GlobalTheory_IdxInt_Model_fine_ind

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
    cint A (ind (· ∈ B)) = 1 / (B.relIndex A : ℂ) := by
  rw [cint_eq (fine_ind hB hi)]
  congr 1
  rw [finsum_eq_single _ (0 : W ⧸ B)]
  · have := out_mk (fine_ind hB hi).2.2.1 0
    simp only [QuotientAddGroup.mk_zero] at this
    rw [this]; simp [ind]
  · intro c hc
    have : c.out ∉ B := fun hm => hc (by
      rw [← QuotientAddGroup.out_eq' c]; exact (QuotientAddGroup.eq_zero_iff _).2 hm)
    simp [ind, this]
end GlobalTheory.IdxInt.Model
