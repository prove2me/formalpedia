-- Prove2me | solution 1 for GlobalTheory.Nef.coeff_max_mul_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:03:52.846075+00:00
-- url     : https://prove2.me/submissions/dabda905-0e43-4860-a855-92e057aef5c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NrmCoeffProdLinear
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef
open Polynomial
namespace GlobalTheory.Nef
theorem _root_.solution {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ)
    (p : F[X]) (N : Γ) (α β : F) (h1 : ∀ i, v (p.coeff i) ≤ N) (h2 : ∃ i, v (p.coeff i) = N) :
    (∀ i, v (((C α + C β * X) * p).coeff i) ≤ max (v α) (v β) * N) ∧
      ∃ i, v (((C α + C β * X) * p).coeff i) = max (v α) (v β) * N := by
  classical
  have c0 : ((C α + C β * X) * p).coeff 0 = α * p.coeff 0 := by
    simp [add_mul, mul_assoc]
  have cs : ∀ i, ((C α + C β * X) * p).coeff (i + 1) = α * p.coeff (i + 1) + β * p.coeff i := by
    intro i
    simp [add_mul, mul_assoc, coeff_X_mul]
  have hle : ∀ i, v (((C α + C β * X) * p).coeff i) ≤ max (v α) (v β) * N := by
    intro i
    cases i with
    | zero =>
      rw [c0, map_mul]
      exact mul_le_mul' (le_max_left _ _) (h1 _)
    | succ i =>
      rw [cs]
      refine v.map_add_le ?_ ?_
      · rw [map_mul]; exact mul_le_mul' (le_max_left _ _) (h1 _)
      · rw [map_mul]; exact mul_le_mul' (le_max_right _ _) (h1 _)
  refine ⟨hle, ?_⟩
  by_cases hz : max (v α) (v β) * N = 0
  · exact ⟨0, le_antisymm (hle 0) (hz ▸ zero_le')⟩
  have hM : max (v α) (v β) ≠ 0 := left_ne_zero_of_mul hz
  have hN : N ≠ 0 := right_ne_zero_of_mul hz
  rcases le_or_gt (v β) (v α) with h | h
  · rw [max_eq_left h] at hM ⊢
    have hs := Nat.find_spec h2
    have hm := fun j => @Nat.find_min _ _ h2 j
    refine ⟨Nat.find h2, ?_⟩
    generalize Nat.find h2 = i at hs hm
    cases i with
    | zero => rw [c0, map_mul, hs]
    | succ i =>
      have hlt : v (p.coeff i) < N := lt_of_le_of_ne (h1 i) (hm i (Nat.lt_succ_self i))
      rw [cs, v.map_add_eq_of_lt_left, map_mul, hs]
      rw [map_mul, map_mul, hs]
      calc v β * v (p.coeff i) ≤ v α * v (p.coeff i) := mul_le_mul' h le_rfl
        _ < v α * N := mul_lt_mul_of_pos_left hlt (zero_lt_iff.2 hM)
  · rw [max_eq_right h.le]
    obtain ⟨i, hi⟩ := h2
    refine ⟨i + 1, ?_⟩
    rw [cs, v.map_add_eq_of_lt_right, map_mul, hi]
    rw [map_mul, map_mul, hi]
    calc v α * v (p.coeff (i + 1)) ≤ v α * N := mul_le_mul' le_rfl (h1 _)
      _ < v β * N := mul_lt_mul_of_pos_right h (zero_lt_iff.2 hN)
end GlobalTheory.Nef
