-- Prove2me | solution 1 for GlobalTheory.BinaryFormUniversal.binary_form_universal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:02:45.164358+00:00
-- url     : https://prove2.me/submissions/fbaa690c-68ba-4690-9ed3-e4492d679b9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_BinaryFormUniversal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.BinaryFormUniversal
open Polynomial
namespace GlobalTheory.BinaryFormUniversal
theorem _root_.solution {k : Type u_1} [Field k] [Finite k] {a n : k}
    (hD : a ^ (2 : ℕ) - (4 : k) * n ≠ (0 : k)) (u : k) :
    ∃ (r : k) (s : k), r ^ (2 : ℕ) + a * r * s + n * s ^ (2 : ℕ) = u := by
  classical
  by_cases h2 : ringChar k = 2
  · obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two h2 u
    exact ⟨r, 0, by rw [hr]; ring⟩
  · letI := Fintype.ofFinite k
    have hodd : Fintype.card k % 2 = 1 := FiniteField.odd_card_of_char_ne_two h2
    have h2' : (2 : k) ≠ 0 := Ring.two_ne_zero h2
    have hD' : -(a ^ 2 - 4 * n) ≠ 0 := neg_ne_zero.mpr hD
    have hf : degree (X ^ 2 : k[X]) = 2 := by simp
    have hg : degree (C (-(a ^ 2 - 4 * n)) * X ^ 2 + C 0 * X + C (-(4 * u)) : k[X]) = 2 :=
      degree_quadratic hD'
    obtain ⟨x, s, h⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
    simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C] at h
    refine ⟨(x - a * s) / 2, s, ?_⟩
    field_simp
    linear_combination h
end GlobalTheory.BinaryFormUniversal
