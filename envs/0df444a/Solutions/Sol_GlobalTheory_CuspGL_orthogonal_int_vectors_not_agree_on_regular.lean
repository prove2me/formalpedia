-- Prove2me | solution 1 for GlobalTheory.CuspGL.orthogonal_int_vectors_not_agree_on_regular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:57:47.460433+00:00
-- url     : https://prove2.me/submissions/f708424d-f2fb-41dc-8daa-6dca30019a0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ParsevalBoundIntegerVectorSmallFourierSupportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardNonregularResiduesModPowSubOneLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SeparationNumericalIneqCuspidalGLStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_NoNormEightOfFourierVanishingOrderFifteenStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_NoNormTwelveOrderSixtythreeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OrthogonalIntVectorsNotAgreeOnRegular
import Theorems.Thm_GlobalTheory_T_card_nonregular_residues_mod_pow_sub_one_le
import Theorems.Thm_GlobalTheory_T_false_of_sum_sq_eq_12_of_fourier_vanish_order_63
import Theorems.Thm_GlobalTheory_T_false_of_sum_sq_eq_eight_of_fourier_vanish_order_15
import Theorems.Thm_GlobalTheory_T_parseval_bound_integerVector_smallFourierSupport
import Theorems.Thm_GlobalTheory_T_separation_numerical_ineq_cuspidalGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.CuspGL
private lemma abs_sum_le_sum_sq_int (s : Finset ℕ) (a : ℕ → ℤ) :
    |∑ k ∈ s, a k| ≤ ∑ k ∈ s, a k ^ 2 := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rcases eq_or_ne (a k) 0 with h | h
  · simp [h]
  · have h1 : 1 ≤ |a k| := Int.one_le_abs h
    nlinarith [sq_abs (a k)]
end GlobalTheory.CuspGL
end

set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution :
    ∀ (q n : ℕ) (ω : ℂ) (a b : ℕ → ℤ), 2 ≤ q → 0 < n → IsPrimitiveRoot ω (q ^ n - 1) → ∑ k ∈ Finset.range (q ^ n - 1), a k ^ 2 = n → ∑ k ∈ Finset.range (q ^ n - 1), b k ^ 2 = n → ∑ k ∈ Finset.range (q ^ n - 1), a k * b k = 0 → 0 < (∑ k ∈ Finset.range (q ^ n - 1), a k) * (∑ k ∈ Finset.range (q ^ n - 1), b k) → (∀ j : ℕ, (∀ e : ℕ, 0 < e → e < n → ¬ j * q ^ e ≡ j [MOD q ^ n - 1]) → ∑ k ∈ Finset.range (q ^ n - 1), (a k : ℂ) * ω ^ (j * k) = ∑ k ∈ Finset.range (q ^ n - 1), (b k : ℂ) * ω ^ (j * k)) → False := by
  intro q n ω a b hq hn hω ha2 hb2 hab hpos hreg
  have hN : 0 < q ^ n - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hn.ne' (by omega))
  have hc2 : ∑ k ∈ Finset.range (q ^ n - 1), (a k - b k) ^ 2 = 2 * (n : ℤ) := by
    have e : ∀ k, (a k - b k) ^ 2 = a k ^ 2 + b k ^ 2 - 2 * (a k * b k) := fun k => by ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ha2, hb2, hab]
    ring
  have hcoef : ∀ j : ℕ, (∀ e : ℕ, 0 < e → e < n → ¬ j * q ^ e ≡ j [MOD q ^ n - 1]) →
      ∑ k ∈ Finset.range (q ^ n - 1), (((a k - b k : ℤ)) : ℂ) * ω ^ (j * k) = 0 := by
    intro j hj
    simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib, hreg j hj, sub_self]
  by_cases hexc : q = 2 ∧ (n = 4 ∨ n = 6)
  · obtain ⟨rfl, rfl | rfl⟩ := hexc
    · refine GlobalTheory.T.false_of_sum_sq_eq_eight_of_fourier_vanish_order_15 ω (fun k => a k - b k) (by simpa using hω) (by simpa using hc2)
        (fun j hj h5 => by
          simpa using hcoef j (fun e he1 he2 => by
            revert h5
            interval_cases j <;> interval_cases e <;> decide))
    · refine GlobalTheory.T.false_of_sum_sq_eq_12_of_fourier_vanish_order_63 ω (fun k => a k - b k) (by simpa using hω) (by simpa using hc2)
        (fun j hj h21 h9 => by
          simpa using hcoef j (fun e he1 he2 => by
            revert h21 h9
            interval_cases j <;> interval_cases e <;> decide))
  · have hsum : |∑ k ∈ Finset.range (q ^ n - 1), (a k - b k)| ≤ (n : ℤ) - 1 := by
      rw [Finset.sum_sub_distrib]
      have hA := abs_le.mp ((abs_sum_le_sum_sq_int _ a).trans ha2.le)
      have hB := abs_le.mp ((abs_sum_le_sum_sq_int _ b).trans hb2.le)
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        exact abs_le.mpr ⟨by omega, by omega⟩
    have h1 := GlobalTheory.T.parseval_bound_integerVector_smallFourierSupport n (q ^ n - 1) ω (fun k => a k - b k)
      ((Finset.Ioo 0 (q ^ n - 1)).filter
        (fun j => ∃ e ∈ Finset.Ioo 0 n, j * q ^ e ≡ j [MOD q ^ n - 1]))
      hn hN hω hc2 hsum (fun j hj0 hjN hjS => by
        refine hcoef j (fun e he1 he2 he => hjS ?_)
        simp only [Finset.mem_filter, Finset.mem_Ioo]
        exact ⟨⟨hj0, hjN⟩, e, ⟨he1, he2⟩, he⟩)
    have h2 := GlobalTheory.T.card_nonregular_residues_mod_pow_sub_one_le q n hq hn
    have h3 := GlobalTheory.T.separation_numerical_ineq_cuspidalGL q n hq hn hexc
    exact absurd (lt_of_le_of_lt (h1.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ h2) _)) h3)
      (lt_irrefl _)
end GlobalTheory.CuspGL
