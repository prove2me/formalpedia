-- Prove2me | solution 1 for GlobalTheory.BI.pair_self_of_isIrrChar_algClosed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:13:54.486522+00:00
-- url     : https://prove2.me/submissions/f449d27c-de87-45e6-ab10-5a5671807492

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingSelfIrreducibleAlgClos

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
theorem _root_.solution (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (G : Type) [Group G] [Finite G]
    (χ : G → L) (h : IsIrrChar L L χ) : pair χ χ = 1 := by
  classical
  obtain ⟨n, ρ, hρ, hχ⟩ := h
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : L) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : ρ.IsIrreducible := hρ

  have key := ρ.card_inv_mul_sum_char_mul_char_eq_finrank ρ
  rw [Representation.IsIrreducible.finrank_intertwiningMap_self] at key
  unfold pair
  rw [finsum_eq_sum_of_fintype]
  simp only [hχ, Algebra.algebraMap_self, RingHom.id_apply]
  simpa using key
end GlobalTheory.BI
