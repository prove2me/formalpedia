-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ProfiniteInteger.index_range_powMonoidHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:06:08.403263+00:00
-- url     : https://prove2.me/submissions/d80d3ae9-f578-469d-87e1-62ce4724f090

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_RelIndexSup
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_index_multiples
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_mem_multiples
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk



set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open GroundTheory.LocalField.Abstract.ProfiniteInteger
namespace GroundTheory.LocalField.Abstract.ProfiniteInteger
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : Multiplicative ℤ̂ →* Multiplicative ℤ̂).range.index = n := by
  have h : Subgroup.toAddSubgroup' (powMonoidHom n : Multiplicative ℤ̂ →* Multiplicative ℤ̂).range =
      multiples n := by
    ext x
    rw [mem_multiples]
    change Multiplicative.ofAdd x ∈ (powMonoidHom n).range ↔ _
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨Multiplicative.toAdd y, ?_⟩
      rw [← toAdd_pow, ← powMonoidHom_apply, hy, toAdd_ofAdd]
    · rintro ⟨y, rfl⟩
      exact ⟨Multiplicative.ofAdd y, by rw [powMonoidHom_apply, ← ofAdd_nsmul]⟩
  have hi := index_multiples ⟨n, Nat.pos_of_ne_zero hn⟩
  simp only [PNat.mk_coe] at hi
  rw [← h] at hi
  exact hi
end GroundTheory.LocalField.Abstract.ProfiniteInteger
