-- Prove2me | solution 1 for GlobalTheory.BI.mem_virt_iff_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:31:31.83498+00:00
-- url     : https://prove2.me/submissions/2a89cdf5-2f3f-4f72-89fb-c9d4433d1083

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldZeroAndAddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MemVirtualCharactersIffSubCharacters
import Theorems.Thm_GlobalTheory_T_isCharacterOverSubfield_zero_and_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
theorem _root_.solution (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (f : G → L) :
    f ∈ Virt K L G ↔ ∃ a b : G → L, IsChar K L a ∧ IsChar K L b ∧ f = a - b := by
  obtain ⟨h0, hadd⟩ := GlobalTheory.T.isCharacterOverSubfield_zero_and_add K L G
  unfold Virt
  constructor
  · intro hf
    induction hf using AddSubgroup.closure_induction with
    | mem x hx => exact ⟨x, 0, hx, h0, (sub_zero x).symm⟩
    | zero => exact ⟨0, 0, h0, h0, (sub_zero 0).symm⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨a, b, ha, hb, rfl⟩ := ihx
      obtain ⟨c, d, hc, hd, rfl⟩ := ihy
      exact ⟨a + c, b + d, hadd a c ha hc, hadd b d hb hd, by abel⟩
    | neg x _ ih =>
      obtain ⟨a, b, ha, hb, rfl⟩ := ih
      exact ⟨b, a, hb, ha, by abel⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact AddSubgroup.sub_mem _ (AddSubgroup.subset_closure ha) (AddSubgroup.subset_closure hb)
end GlobalTheory.BI
