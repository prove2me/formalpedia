-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ProfiniteInteger.eq_multiples_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:43:38.980586+00:00
-- url     : https://prove2.me/submissions/bd184f1f-5e49-4e97-8650-9cdbcbbc3375

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_mem_multiples
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_index_multiples

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open GroundTheory.LocalField.Abstract.ProfiniteInteger
namespace GroundTheory.LocalField.Abstract.ProfiniteInteger
theorem _root_.solution {H : AddSubgroup ℤ̂} (hH : H.index ≠ 0) : H = multiples H.index := by
  have hle : multiples H.index ≤ H := by
    intro x hx
    obtain ⟨y, rfl⟩ := mem_multiples.1 hx
    exact H.nsmul_index_mem y
  have hidx := AddSubgroup.relIndex_mul_index hle
  have hm := index_multiples ⟨H.index, Nat.pos_of_ne_zero hH⟩
  simp only [PNat.mk_coe] at hm
  rw [hm] at hidx
  have h1 : (multiples H.index).relIndex H = 1 := (Nat.mul_eq_right hH).1 hidx
  exact le_antisymm (AddSubgroup.relIndex_eq_one.1 h1) hle
end GroundTheory.LocalField.Abstract.ProfiniteInteger
