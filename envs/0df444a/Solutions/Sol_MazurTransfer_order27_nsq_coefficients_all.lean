-- Prove2me | solution 1 for MazurTransfer.order27_nsq_coefficients_all
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T16:02:37.371326+00:00
-- url     : https://prove2.me/submissions/ea786852-5db7-442a-b924-135a4fe4e55f

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/
import Definitions.Def_MazurTransfer_Order27NSqCoefficientData
open Polynomial
namespace MazurTransfer.Order27NSqPolynomial

theorem coeff_table_p_tlN0 (f : ℚ) (n : ℕ) :
 (p_tlN0 f).coeff n = c_tlN0 f n := by
 simp only [p_tlN0, c_tlN0, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlN1 (f : ℚ) (n : ℕ) :
 (p_tlN1 f).coeff n = c_tlN1 f n := by
 simp only [p_tlN1, c_tlN1, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlN2 (f : ℚ) (n : ℕ) :
 (p_tlN2 f).coeff n = c_tlN2 f n := by
 simp only [p_tlN2, c_tlN2, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlN3 (f : ℚ) (n : ℕ) :
 (p_tlN3 f).coeff n = c_tlN3 f n := by
 simp only [p_tlN3, c_tlN3, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlT0 (f : ℚ) (n : ℕ) :
 (p_tlT0 f).coeff n = c_tlT0 f n := by
 simp only [p_tlT0, c_tlT0, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlT1 (f : ℚ) (n : ℕ) :
 (p_tlT1 f).coeff n = c_tlT1 f n := by
 simp only [p_tlT1, c_tlT1, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlT2 (f : ℚ) (n : ℕ) :
 (p_tlT2 f).coeff n = c_tlT2 f n := by
 simp only [p_tlT2, c_tlT2, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlT3 (f : ℚ) (n : ℕ) :
 (p_tlT3 f).coeff n = c_tlT3 f n := by
 simp only [p_tlT3, c_tlT3, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNSqP3c0 (f : ℚ) (n : ℕ) :
 (p_tlNSqP3c0 f).coeff n = c_tlNSqP3c0 f n := by
 simp only [p_tlNSqP3c0, c_tlNSqP3c0, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNSqP3c1 (f : ℚ) (n : ℕ) :
 (p_tlNSqP3c1 f).coeff n = c_tlNSqP3c1 f n := by
 simp only [p_tlNSqP3c1, c_tlNSqP3c1, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNSqP3c2 (f : ℚ) (n : ℕ) :
 (p_tlNSqP3c2 f).coeff n = c_tlNSqP3c2 f n := by
 simp only [p_tlNSqP3c2, c_tlNSqP3c2, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNSqP3c3 (f : ℚ) (n : ℕ) :
 (p_tlNSqP3c3 f).coeff n = c_tlNSqP3c3 f n := by
 simp only [p_tlNSqP3c3, c_tlNSqP3c3, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNSqP3c4 (f : ℚ) (n : ℕ) :
 (p_tlNSqP3c4 f).coeff n = c_tlNSqP3c4 f n := by
 simp only [p_tlNSqP3c4, c_tlNSqP3c4, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNSqP3c5 (f : ℚ) (n : ℕ) :
 (p_tlNSqP3c5 f).coeff n = c_tlNSqP3c5 f n := by
 simp only [p_tlNSqP3c5, c_tlNSqP3c5, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNSqP3c6 (f : ℚ) (n : ℕ) :
 (p_tlNSqP3c6 f).coeff n = c_tlNSqP3c6 f n := by
 simp only [p_tlNSqP3c6, c_tlNSqP3c6, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNSqP3c7 (f : ℚ) (n : ℕ) :
 (p_tlNSqP3c7 f).coeff n = c_tlNSqP3c7 f n := by
 simp only [p_tlNSqP3c7, c_tlNSqP3c7, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNSqP3c8 (f : ℚ) (n : ℕ) :
 (p_tlNSqP3c8 f).coeff n = c_tlNSqP3c8 f n := by
 simp only [p_tlNSqP3c8, c_tlNSqP3c8, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNSqP3c9 (f : ℚ) (n : ℕ) :
 (p_tlNSqP3c9 f).coeff n = c_tlNSqP3c9 f n := by
 simp only [p_tlNSqP3c9, c_tlNSqP3c9, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNSqP3c10 (f : ℚ) (n : ℕ) :
 (p_tlNSqP3c10 f).coeff n = c_tlNSqP3c10 f n := by
 simp only [p_tlNSqP3c10, c_tlNSqP3c10, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNSqP3c11 (f : ℚ) (n : ℕ) :
 (p_tlNSqP3c11 f).coeff n = c_tlNSqP3c11 f n := by
 simp only [p_tlNSqP3c11, c_tlNSqP3c11, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNSqQ3c0 (f : ℚ) (n : ℕ) :
 (p_tlNSqQ3c0 f).coeff n = c_tlNSqQ3c0 f n := by
 simp only [p_tlNSqQ3c0, c_tlNSqQ3c0, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNSqQ3c1 (f : ℚ) (n : ℕ) :
 (p_tlNSqQ3c1 f).coeff n = c_tlNSqQ3c1 f n := by
 simp only [p_tlNSqQ3c1, c_tlNSqQ3c1, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNSqQ3c2 (f : ℚ) (n : ℕ) :
 (p_tlNSqQ3c2 f).coeff n = c_tlNSqQ3c2 f n := by
 simp only [p_tlNSqQ3c2, c_tlNSqQ3c2, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNSqQ3c3 (f : ℚ) (n : ℕ) :
 (p_tlNSqQ3c3 f).coeff n = c_tlNSqQ3c3 f n := by
 simp only [p_tlNSqQ3c3, c_tlNSqQ3c3, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNSqQ3c4 (f : ℚ) (n : ℕ) :
 (p_tlNSqQ3c4 f).coeff n = c_tlNSqQ3c4 f n := by
 simp only [p_tlNSqQ3c4, c_tlNSqQ3c4, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNSqQ3c5 (f : ℚ) (n : ℕ) :
 (p_tlNSqQ3c5 f).coeff n = c_tlNSqQ3c5 f n := by
 simp only [p_tlNSqQ3c5, c_tlNSqQ3c5, Polynomial.coeff_add, Polynomial.coeff_monomial]

end MazurTransfer.Order27NSqPolynomial
open MazurTransfer.Order27NSqPolynomial
theorem solution :
∀ (f : ℚ) (n : ℕ),
((p_tlN0 f).coeff n = c_tlN0 f n) ∧
((p_tlN1 f).coeff n = c_tlN1 f n) ∧
((p_tlN2 f).coeff n = c_tlN2 f n) ∧
((p_tlN3 f).coeff n = c_tlN3 f n) ∧
((p_tlT0 f).coeff n = c_tlT0 f n) ∧
((p_tlT1 f).coeff n = c_tlT1 f n) ∧
((p_tlT2 f).coeff n = c_tlT2 f n) ∧
((p_tlT3 f).coeff n = c_tlT3 f n) ∧
((p_tlNSqP3c0 f).coeff n = c_tlNSqP3c0 f n) ∧
((p_tlNSqP3c1 f).coeff n = c_tlNSqP3c1 f n) ∧
((p_tlNSqP3c2 f).coeff n = c_tlNSqP3c2 f n) ∧
((p_tlNSqP3c3 f).coeff n = c_tlNSqP3c3 f n) ∧
((p_tlNSqP3c4 f).coeff n = c_tlNSqP3c4 f n) ∧
((p_tlNSqP3c5 f).coeff n = c_tlNSqP3c5 f n) ∧
((p_tlNSqP3c6 f).coeff n = c_tlNSqP3c6 f n) ∧
((p_tlNSqP3c7 f).coeff n = c_tlNSqP3c7 f n) ∧
((p_tlNSqP3c8 f).coeff n = c_tlNSqP3c8 f n) ∧
((p_tlNSqP3c9 f).coeff n = c_tlNSqP3c9 f n) ∧
((p_tlNSqP3c10 f).coeff n = c_tlNSqP3c10 f n) ∧
((p_tlNSqP3c11 f).coeff n = c_tlNSqP3c11 f n) ∧
((p_tlNSqQ3c0 f).coeff n = c_tlNSqQ3c0 f n) ∧
((p_tlNSqQ3c1 f).coeff n = c_tlNSqQ3c1 f n) ∧
((p_tlNSqQ3c2 f).coeff n = c_tlNSqQ3c2 f n) ∧
((p_tlNSqQ3c3 f).coeff n = c_tlNSqQ3c3 f n) ∧
((p_tlNSqQ3c4 f).coeff n = c_tlNSqQ3c4 f n) ∧
((p_tlNSqQ3c5 f).coeff n = c_tlNSqQ3c5 f n) := by
 intro f n
 exact ⟨coeff_table_p_tlN0 f n, coeff_table_p_tlN1 f n, coeff_table_p_tlN2 f n, coeff_table_p_tlN3 f n, coeff_table_p_tlT0 f n, coeff_table_p_tlT1 f n, coeff_table_p_tlT2 f n, coeff_table_p_tlT3 f n, coeff_table_p_tlNSqP3c0 f n, coeff_table_p_tlNSqP3c1 f n, coeff_table_p_tlNSqP3c2 f n, coeff_table_p_tlNSqP3c3 f n, coeff_table_p_tlNSqP3c4 f n, coeff_table_p_tlNSqP3c5 f n, coeff_table_p_tlNSqP3c6 f n, coeff_table_p_tlNSqP3c7 f n, coeff_table_p_tlNSqP3c8 f n, coeff_table_p_tlNSqP3c9 f n, coeff_table_p_tlNSqP3c10 f n, coeff_table_p_tlNSqP3c11 f n, coeff_table_p_tlNSqQ3c0 f n, coeff_table_p_tlNSqQ3c1 f n, coeff_table_p_tlNSqQ3c2 f n, coeff_table_p_tlNSqQ3c3 f n, coeff_table_p_tlNSqQ3c4 f n, coeff_table_p_tlNSqQ3c5 f n⟩

#print axioms solution
