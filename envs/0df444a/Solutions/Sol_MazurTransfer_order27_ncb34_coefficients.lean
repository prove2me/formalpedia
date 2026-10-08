-- Prove2me | solution 1 for MazurTransfer.order27_ncb34_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T18:48:05.411404+00:00
-- url     : https://prove2.me/submissions/e6d88a88-a69c-45c3-a25d-dc85b479168e

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/
import Definitions.Def_MazurTransfer_Order27NCb34PolynomialData
import Definitions.Def_MazurTransfer_Order27NCb34CoefficientData
namespace MazurTransfer.Order27NCb34Polynomial
open Polynomial

theorem coeff_table_p_tlNSqP3c5 (f : ℚ) (n : ℕ) :
 (p_tlNSqP3c5 f).coeff n = c_tlNSqP3c5 f n := by
 simp only [p_tlNSqP3c5, c_tlNSqP3c5, Polynomial.coeff_add, Polynomial.coeff_monomial]

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

theorem coeff_table_p_tlNCbP34c0 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c0 f).coeff n = c_tlNCbP34c0 f n := by
 simp only [p_tlNCbP34c0, c_tlNCbP34c0, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNCbP34c1 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c1 f).coeff n = c_tlNCbP34c1 f n := by
 simp only [p_tlNCbP34c1, c_tlNCbP34c1, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNCbP34c2 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c2 f).coeff n = c_tlNCbP34c2 f n := by
 simp only [p_tlNCbP34c2, c_tlNCbP34c2, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNCbP34c3 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c3 f).coeff n = c_tlNCbP34c3 f n := by
 simp only [p_tlNCbP34c3, c_tlNCbP34c3, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNCbP34c4 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c4 f).coeff n = c_tlNCbP34c4 f n := by
 simp only [p_tlNCbP34c4, c_tlNCbP34c4, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNCbP34c5 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c5 f).coeff n = c_tlNCbP34c5 f n := by
 simp only [p_tlNCbP34c5, c_tlNCbP34c5, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNCbP34c6 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c6 f).coeff n = c_tlNCbP34c6 f n := by
 simp only [p_tlNCbP34c6, c_tlNCbP34c6, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNCbP34c7 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c7 f).coeff n = c_tlNCbP34c7 f n := by
 simp only [p_tlNCbP34c7, c_tlNCbP34c7, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNCbP34c8 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c8 f).coeff n = c_tlNCbP34c8 f n := by
 simp only [p_tlNCbP34c8, c_tlNCbP34c8, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNCbP34c9 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c9 f).coeff n = c_tlNCbP34c9 f n := by
 simp only [p_tlNCbP34c9, c_tlNCbP34c9, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNCbP34c10 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c10 f).coeff n = c_tlNCbP34c10 f n := by
 simp only [p_tlNCbP34c10, c_tlNCbP34c10, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNCbP34c11 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c11 f).coeff n = c_tlNCbP34c11 f n := by
 simp only [p_tlNCbP34c11, c_tlNCbP34c11, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNCbP34c12 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c12 f).coeff n = c_tlNCbP34c12 f n := by
 simp only [p_tlNCbP34c12, c_tlNCbP34c12, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNCbP34c13 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c13 f).coeff n = c_tlNCbP34c13 f n := by
 simp only [p_tlNCbP34c13, c_tlNCbP34c13, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNCbP34c14 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c14 f).coeff n = c_tlNCbP34c14 f n := by
 simp only [p_tlNCbP34c14, c_tlNCbP34c14, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNCbP34c15 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c15 f).coeff n = c_tlNCbP34c15 f n := by
 simp only [p_tlNCbP34c15, c_tlNCbP34c15, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNCbP34c16 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c16 f).coeff n = c_tlNCbP34c16 f n := by
 simp only [p_tlNCbP34c16, c_tlNCbP34c16, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNCbP34c17 (f : ℚ) (n : ℕ) :
 (p_tlNCbP34c17 f).coeff n = c_tlNCbP34c17 f n := by
 simp only [p_tlNCbP34c17, c_tlNCbP34c17, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNCbQ34c0 (f : ℚ) (n : ℕ) :
 (p_tlNCbQ34c0 f).coeff n = c_tlNCbQ34c0 f n := by
 simp only [p_tlNCbQ34c0, c_tlNCbQ34c0, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNCbQ34c1 (f : ℚ) (n : ℕ) :
 (p_tlNCbQ34c1 f).coeff n = c_tlNCbQ34c1 f n := by
 simp only [p_tlNCbQ34c1, c_tlNCbQ34c1, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNCbQ34c2 (f : ℚ) (n : ℕ) :
 (p_tlNCbQ34c2 f).coeff n = c_tlNCbQ34c2 f n := by
 simp only [p_tlNCbQ34c2, c_tlNCbQ34c2, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNCbQ34c3 (f : ℚ) (n : ℕ) :
 (p_tlNCbQ34c3 f).coeff n = c_tlNCbQ34c3 f n := by
 simp only [p_tlNCbQ34c3, c_tlNCbQ34c3, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNCbQ34c4 (f : ℚ) (n : ℕ) :
 (p_tlNCbQ34c4 f).coeff n = c_tlNCbQ34c4 f n := by
 simp only [p_tlNCbQ34c4, c_tlNCbQ34c4, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlNCbQ34c5 (f : ℚ) (n : ℕ) :
 (p_tlNCbQ34c5 f).coeff n = c_tlNCbQ34c5 f n := by
 simp only [p_tlNCbQ34c5, c_tlNCbQ34c5, Polynomial.coeff_add, Polynomial.coeff_monomial]

end MazurTransfer.Order27NCb34Polynomial

#print axioms MazurTransfer.Order27NCb34Polynomial.coeff_table_p_tlNSqP3c5

open Polynomial MazurTransfer.Order27NCb34Polynomial

theorem solution :
∀ (f : ℚ) (n : ℕ),
((p_tlNSqP3c5 f).coeff n = c_tlNSqP3c5 f n) ∧
((p_tlN0 f).coeff n = c_tlN0 f n) ∧
((p_tlN1 f).coeff n = c_tlN1 f n) ∧
((p_tlN2 f).coeff n = c_tlN2 f n) ∧
((p_tlN3 f).coeff n = c_tlN3 f n) ∧
((p_tlT0 f).coeff n = c_tlT0 f n) ∧
((p_tlT1 f).coeff n = c_tlT1 f n) ∧
((p_tlT2 f).coeff n = c_tlT2 f n) ∧
((p_tlT3 f).coeff n = c_tlT3 f n) ∧
((p_tlNCbP34c0 f).coeff n = c_tlNCbP34c0 f n) ∧
((p_tlNCbP34c1 f).coeff n = c_tlNCbP34c1 f n) ∧
((p_tlNCbP34c2 f).coeff n = c_tlNCbP34c2 f n) ∧
((p_tlNCbP34c3 f).coeff n = c_tlNCbP34c3 f n) ∧
((p_tlNCbP34c4 f).coeff n = c_tlNCbP34c4 f n) ∧
((p_tlNCbP34c5 f).coeff n = c_tlNCbP34c5 f n) ∧
((p_tlNCbP34c6 f).coeff n = c_tlNCbP34c6 f n) ∧
((p_tlNCbP34c7 f).coeff n = c_tlNCbP34c7 f n) ∧
((p_tlNCbP34c8 f).coeff n = c_tlNCbP34c8 f n) ∧
((p_tlNCbP34c9 f).coeff n = c_tlNCbP34c9 f n) ∧
((p_tlNCbP34c10 f).coeff n = c_tlNCbP34c10 f n) ∧
((p_tlNCbP34c11 f).coeff n = c_tlNCbP34c11 f n) ∧
((p_tlNCbP34c12 f).coeff n = c_tlNCbP34c12 f n) ∧
((p_tlNCbP34c13 f).coeff n = c_tlNCbP34c13 f n) ∧
((p_tlNCbP34c14 f).coeff n = c_tlNCbP34c14 f n) ∧
((p_tlNCbP34c15 f).coeff n = c_tlNCbP34c15 f n) ∧
((p_tlNCbP34c16 f).coeff n = c_tlNCbP34c16 f n) ∧
((p_tlNCbP34c17 f).coeff n = c_tlNCbP34c17 f n) ∧
((p_tlNCbQ34c0 f).coeff n = c_tlNCbQ34c0 f n) ∧
((p_tlNCbQ34c1 f).coeff n = c_tlNCbQ34c1 f n) ∧
((p_tlNCbQ34c2 f).coeff n = c_tlNCbQ34c2 f n) ∧
((p_tlNCbQ34c3 f).coeff n = c_tlNCbQ34c3 f n) ∧
((p_tlNCbQ34c4 f).coeff n = c_tlNCbQ34c4 f n) ∧
((p_tlNCbQ34c5 f).coeff n = c_tlNCbQ34c5 f n) := by
 intro f n
 exact ⟨coeff_table_p_tlNSqP3c5 f n, coeff_table_p_tlN0 f n, coeff_table_p_tlN1 f n, coeff_table_p_tlN2 f n, coeff_table_p_tlN3 f n, coeff_table_p_tlT0 f n, coeff_table_p_tlT1 f n, coeff_table_p_tlT2 f n, coeff_table_p_tlT3 f n, coeff_table_p_tlNCbP34c0 f n, coeff_table_p_tlNCbP34c1 f n, coeff_table_p_tlNCbP34c2 f n, coeff_table_p_tlNCbP34c3 f n, coeff_table_p_tlNCbP34c4 f n, coeff_table_p_tlNCbP34c5 f n, coeff_table_p_tlNCbP34c6 f n, coeff_table_p_tlNCbP34c7 f n, coeff_table_p_tlNCbP34c8 f n, coeff_table_p_tlNCbP34c9 f n, coeff_table_p_tlNCbP34c10 f n, coeff_table_p_tlNCbP34c11 f n, coeff_table_p_tlNCbP34c12 f n, coeff_table_p_tlNCbP34c13 f n, coeff_table_p_tlNCbP34c14 f n, coeff_table_p_tlNCbP34c15 f n, coeff_table_p_tlNCbP34c16 f n, coeff_table_p_tlNCbP34c17 f n, coeff_table_p_tlNCbQ34c0 f n, coeff_table_p_tlNCbQ34c1 f n, coeff_table_p_tlNCbQ34c2 f n, coeff_table_p_tlNCbQ34c3 f n, coeff_table_p_tlNCbQ34c4 f n, coeff_table_p_tlNCbQ34c5 f n⟩
#print axioms solution
