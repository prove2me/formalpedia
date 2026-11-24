-- Prove2me | solution 1 for GlobalTheory.SignedLengthMapLogDet.signedLength_of_common
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:01:34.643564+00:00
-- url     : https://prove2.me/submissions/4fd40f60-e530-4e1c-9893-2b97eb50ab1a

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthMapEqLogOrdFracDet
import Theorems.Thm_GlobalTheory_SignedLengthMapLogDet_relLength_chain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3
open GlobalTheory GlobalTheory.SignedLengthMapLogDet
open Module
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
namespace GlobalTheory.SignedLengthMapLogDet
theorem _root_.solution {A B C : Submodule R V} (hA : C ≤ A) (hB : C ≤ B) {m n : ℕ}
    (hm : relLength A C = m) (hn : relLength B C = n) :
    LengthCommensurable A B ∧ signedLength A B = (m : ℤ) - n := by
  rw [relLength_chain (inf_le_left : A ⊓ B ≤ A) (le_inf hA hB), relLength_inf_right] at hm
  rw [relLength_chain (inf_le_right : A ⊓ B ≤ B) (le_inf hA hB), relLength_inf_right'] at hn
  unfold LengthCommensurable signedLength
  generalize relLength A B = x at *
  generalize relLength B A = y at *
  generalize relLength (A ⊓ B) C = w at *
  cases x <;> cases y <;> cases w <;> try simp at hm hn
  norm_cast at hm hn
  refine ⟨by simp, ?_⟩
  simp only [ENat.toNat_coe]
  omega
end GlobalTheory.SignedLengthMapLogDet
