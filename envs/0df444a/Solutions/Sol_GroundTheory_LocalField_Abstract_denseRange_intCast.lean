-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.denseRange_intCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:20:52.662069+00:00
-- url     : https://prove2.me/submissions/6a3a526a-4f40-4e4a-9e66-6eef356ebcc6

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_eq_multiples_index
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_proj_eq_zero_iff
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
open ProfiniteInteger
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution : DenseRange (Int.cast : ℤ → ℤ̂) := by
  intro x
  rw [mem_closure_iff]
  intro U hU hxU
  obtain ⟨W, hW⟩ := ProfiniteGrp.exist_openNormalAddSubgroup_sub_open_nhds_of_zero
    (hU.preimage (continuous_const_add x)) (by simpa using hxU)
  have : Finite (ℤ̂ ⧸ W.toAddSubgroup) :=
    AddSubgroup.quotient_finite_of_isOpen W.toAddSubgroup W.isOpen'
  have hfi : W.toAddSubgroup.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  have hm : W.toAddSubgroup.index ≠ 0 := hfi.index_ne_zero
  have hWm := eq_multiples_index hm
  set m : ℕ+ := ⟨W.toAddSubgroup.index, Nat.pos_of_ne_zero hm⟩ with hmdef
  refine ⟨((((proj m x).val : ℕ) : ℤ) : ℤ̂), ?_, Set.mem_range_self _⟩
  have hk : ((((proj m x).val : ℕ) : ℤ) : ℤ̂) - x ∈ W.toAddSubgroup := by
    rw [hWm]
    have := (proj_eq_zero_iff (n := m) (x := ((((proj m x).val : ℕ) : ℤ) : ℤ̂) - x)).1 (by
      rw [map_sub, map_intCast, Int.cast_natCast, ZMod.natCast_zmod_val, sub_self])
    simpa [hmdef] using this
  have := hW hk
  simpa using this
end GroundTheory.LocalField.Abstract
