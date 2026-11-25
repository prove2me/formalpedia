-- Prove2me | solution 1 for GlobalTheory.SignedLengthOrdFracDet.signedLength_of_common
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:50:40.747599+00:00
-- url     : https://prove2.me/submissions/cc164d0b-3278-4f43-8104-21d262b0902b

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthSpanEqOrdFracDet
import Theorems.Thm_GlobalTheory_SignedLengthOrdFracDet_relLength_chain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SignedLengthOrdFracDet
open Module Submodule
namespace GlobalTheory.SignedLengthOrdFracDet
theorem _root_.solution {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    {A B C : Submodule R V} (hA : C ≤ A) (hB : C ≤ B) {m n : ℕ} (hm : relLength A C = m)
    (hn : relLength B C = n) :
    LengthCommensurable A B ∧ signedLength A B = (m : ℤ) - n := by
  have h1 := relLength_chain (inf_le_left : A ⊓ B ≤ A) (le_inf hA hB)
  have h2 := relLength_chain (inf_le_right : A ⊓ B ≤ B) (le_inf hA hB)
  rw [relLength_inf_right, hm] at h1
  rw [relLength_inf_right', hn] at h2
  unfold LengthCommensurable signedLength
  generalize relLength A B = x at *
  generalize relLength B A = y at *
  generalize relLength (A ⊓ B) C = z at *
  cases x with
  | top => simp at h1
  | coe x =>
  cases y with
  | top => simp at h2
  | coe y =>
  cases z with
  | top => simp at h2
  | coe z =>
  norm_cast at h1 h2
  refine ⟨⟨by simp, by simp⟩, ?_⟩
  simp only [ENat.toNat_natCast]
  omega
end GlobalTheory.SignedLengthOrdFracDet
