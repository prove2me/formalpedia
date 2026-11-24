-- Prove2me | solution 1 for GlobalTheory.ClassFin.log_sq_le_tangent_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:12:03.40696+00:00
-- url     : https://prove2.me/submissions/a752225b-ef96-4477-b48d-ace5f77875a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LogSqLeTangentAddSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin
namespace GlobalTheory.ClassFin
theorem _root_.solution :
    ∀ a : ℝ, 0 < a → ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, a ≤ x → a ≤ y →
      (Real.log y) ^ 2 ≤ (Real.log x) ^ 2 + 2 * Real.log x / x * (y - x) + C * (y - x) ^ 2 := by
  intro a ha
  refine ⟨(2 + 2 * |Real.log a|) / a ^ 2, by positivity, ?_⟩
  intro x y hx hy
  have hx0 : 0 < x := lt_of_lt_of_le ha hx
  have hy0 : 0 < y := lt_of_lt_of_le ha hy
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = Real.log y - Real.log x := ⟨_, rfl⟩
  have hlogy : Real.log y = Real.log x + d := by rw [hd]; ring
  have hup : d ≤ (y - x) / x := by
    have h := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    rw [Real.log_div hy0.ne' hx0.ne'] at h
    have e : y / x - 1 = (y - x) / x := by field_simp
    rw [hd]; linarith
  have hlow : (y - x) / y ≤ d := by
    have h := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
    rw [Real.log_div hx0.ne' hy0.ne'] at h
    have e : (y - x) / y = 1 - x / y := by field_simp
    rw [hd, e]; linarith
  have hxy : a ^ 2 ≤ x * y := by nlinarith
  have hxx : a ^ 2 ≤ x ^ 2 := by nlinarith
  have hyy : a ^ 2 ≤ y ^ 2 := by nlinarith
  have ha2 : 0 < a ^ 2 := by positivity
  have hK0 : 0 ≤ (y - x) ^ 2 / a ^ 2 := by positivity
  have hgap : (y - x) / x - d ≤ (y - x) ^ 2 / a ^ 2 := by
    have e : (y - x) / x - (y - x) / y = (y - x) ^ 2 / (x * y) := by
      field_simp
    have h : (y - x) ^ 2 / (x * y) ≤ (y - x) ^ 2 / a ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) ha2 hxy
    linarith
  have hq2 : ((y - x) / x) ^ 2 ≤ (y - x) ^ 2 / a ^ 2 := by
    rw [div_pow]; exact div_le_div_of_nonneg_left (sq_nonneg _) ha2 hxx
  have hp2 : ((y - x) / y) ^ 2 ≤ (y - x) ^ 2 / a ^ 2 := by
    rw [div_pow]; exact div_le_div_of_nonneg_left (sq_nonneg _) ha2 hyy
  have hd2 : d ^ 2 ≤ 2 * ((y - x) ^ 2 / a ^ 2) := by
    rcases le_total 0 d with h | h
    · nlinarith [sq_nonneg ((y - x) / y)]
    · nlinarith [sq_nonneg ((y - x) / x)]
  have hu : -Real.log x ≤ |Real.log a| := by
    have := Real.log_le_log ha hx
    have := neg_le_abs (Real.log a)
    linarith
  have hL0 : 0 ≤ |Real.log a| := abs_nonneg _
  have he0 : 0 ≤ (y - x) / x - d := by linarith
  have h3 : -Real.log x * ((y - x) / x - d) ≤ |Real.log a| * ((y - x) ^ 2 / a ^ 2) :=
    le_trans (mul_le_mul_of_nonneg_right hu he0) (mul_le_mul_of_nonneg_left hgap hL0)
  have e1 : 2 * Real.log x / x * (y - x) = 2 * Real.log x * ((y - x) / x) := by ring
  have e2 : (2 + 2 * |Real.log a|) / a ^ 2 * (y - x) ^ 2
      = (2 + 2 * |Real.log a|) * ((y - x) ^ 2 / a ^ 2) := by ring
  rw [hlogy, e1, e2]
  nlinarith [h3, hd2]
end GlobalTheory.ClassFin
