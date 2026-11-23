-- Prove2me | solution 1 for GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:13:55.845972+00:00
-- url     : https://prove2.me/submissions/072b968b-4d83-4a1a-ad36-98d38121d9e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingEqZeroOfDistinctIrredu

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
theorem _root_.solution : ∀ (G : Type) [Group G] [Finite G] (a b : G → ℂ),
    IsIrrChar ℂ ℂ a → IsIrrChar ℂ ℂ b → a ≠ b → pair a b = 0 := by
  intro G _ _ a b ha hb hab
  obtain ⟨n, ρ, hρ, ha⟩ := ha
  obtain ⟨m, σ, hσ, hb⟩ := hb
  have := hρ
  have := hσ
  have := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have ha' : a = ρ.character := funext fun g => by simp [ha]
  have hb' : b = σ.character := funext fun g => by simp [hb]
  have hne : ¬ Nonempty (Representation.Equiv σ ρ) := by
    rintro ⟨φ⟩
    exact hab (by rw [ha', hb', Representation.char_iso φ])
  have h := Representation.char_orthonormal ρ σ
  rw [if_neg hne] at h
  unfold pair
  rw [finsum_eq_sum_of_fintype, ha', hb']
  simpa using h
end GlobalTheory.BI
