-- Prove2me | solution 1 for MazurTransfer.order27_dcb1_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T18:49:07.178769+00:00
-- url     : https://prove2.me/submissions/e64800a4-0265-4466-a74b-fccbc4a59bd3

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/
import Definitions.Def_MazurTransfer_Order27DCb1PolynomialData
import Definitions.Def_MazurTransfer_Order27DCb1CoefficientData
namespace MazurTransfer.Order27DCb1Polynomial
open Polynomial

theorem coeff_table_p_tlDSqP0c3 (f : ℚ) (n : ℕ) :
 (p_tlDSqP0c3 f).coeff n = c_tlDSqP0c3 f n := by
 simp only [p_tlDSqP0c3, c_tlDSqP0c3, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlDSqP0c4 (f : ℚ) (n : ℕ) :
 (p_tlDSqP0c4 f).coeff n = c_tlDSqP0c4 f n := by
 simp only [p_tlDSqP0c4, c_tlDSqP0c4, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlDSqP0c5 (f : ℚ) (n : ℕ) :
 (p_tlDSqP0c5 f).coeff n = c_tlDSqP0c5 f n := by
 simp only [p_tlDSqP0c5, c_tlDSqP0c5, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlD0 (f : ℚ) (n : ℕ) :
 (p_tlD0 f).coeff n = c_tlD0 f n := by
 simp only [p_tlD0, c_tlD0, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlD1 (f : ℚ) (n : ℕ) :
 (p_tlD1 f).coeff n = c_tlD1 f n := by
 simp only [p_tlD1, c_tlD1, Polynomial.coeff_add, Polynomial.coeff_monomial]

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

theorem coeff_table_p_tlDCbP1c0 (f : ℚ) (n : ℕ) :
 (p_tlDCbP1c0 f).coeff n = c_tlDCbP1c0 f n := by
 simp only [p_tlDCbP1c0, c_tlDCbP1c0, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlDCbP1c1 (f : ℚ) (n : ℕ) :
 (p_tlDCbP1c1 f).coeff n = c_tlDCbP1c1 f n := by
 simp only [p_tlDCbP1c1, c_tlDCbP1c1, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlDCbP1c2 (f : ℚ) (n : ℕ) :
 (p_tlDCbP1c2 f).coeff n = c_tlDCbP1c2 f n := by
 simp only [p_tlDCbP1c2, c_tlDCbP1c2, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlDCbP1c3 (f : ℚ) (n : ℕ) :
 (p_tlDCbP1c3 f).coeff n = c_tlDCbP1c3 f n := by
 simp only [p_tlDCbP1c3, c_tlDCbP1c3, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlDCbP1c4 (f : ℚ) (n : ℕ) :
 (p_tlDCbP1c4 f).coeff n = c_tlDCbP1c4 f n := by
 simp only [p_tlDCbP1c4, c_tlDCbP1c4, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlDCbP1c5 (f : ℚ) (n : ℕ) :
 (p_tlDCbP1c5 f).coeff n = c_tlDCbP1c5 f n := by
 simp only [p_tlDCbP1c5, c_tlDCbP1c5, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlDCbP1c6 (f : ℚ) (n : ℕ) :
 (p_tlDCbP1c6 f).coeff n = c_tlDCbP1c6 f n := by
 simp only [p_tlDCbP1c6, c_tlDCbP1c6, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlDCbP1c7 (f : ℚ) (n : ℕ) :
 (p_tlDCbP1c7 f).coeff n = c_tlDCbP1c7 f n := by
 simp only [p_tlDCbP1c7, c_tlDCbP1c7, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlDCbP1c8 (f : ℚ) (n : ℕ) :
 (p_tlDCbP1c8 f).coeff n = c_tlDCbP1c8 f n := by
 simp only [p_tlDCbP1c8, c_tlDCbP1c8, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlDCbP1c9 (f : ℚ) (n : ℕ) :
 (p_tlDCbP1c9 f).coeff n = c_tlDCbP1c9 f n := by
 simp only [p_tlDCbP1c9, c_tlDCbP1c9, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlDCbP1c10 (f : ℚ) (n : ℕ) :
 (p_tlDCbP1c10 f).coeff n = c_tlDCbP1c10 f n := by
 simp only [p_tlDCbP1c10, c_tlDCbP1c10, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlDCbP1c11 (f : ℚ) (n : ℕ) :
 (p_tlDCbP1c11 f).coeff n = c_tlDCbP1c11 f n := by
 simp only [p_tlDCbP1c11, c_tlDCbP1c11, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlDCbP1c12 (f : ℚ) (n : ℕ) :
 (p_tlDCbP1c12 f).coeff n = c_tlDCbP1c12 f n := by
 simp only [p_tlDCbP1c12, c_tlDCbP1c12, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlDCbQ1c0 (f : ℚ) (n : ℕ) :
 (p_tlDCbQ1c0 f).coeff n = c_tlDCbQ1c0 f n := by
 simp only [p_tlDCbQ1c0, c_tlDCbQ1c0, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlDCbQ1c1 (f : ℚ) (n : ℕ) :
 (p_tlDCbQ1c1 f).coeff n = c_tlDCbQ1c1 f n := by
 simp only [p_tlDCbQ1c1, c_tlDCbQ1c1, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlDCbQ1c2 (f : ℚ) (n : ℕ) :
 (p_tlDCbQ1c2 f).coeff n = c_tlDCbQ1c2 f n := by
 simp only [p_tlDCbQ1c2, c_tlDCbQ1c2, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlDCbQ1c3 (f : ℚ) (n : ℕ) :
 (p_tlDCbQ1c3 f).coeff n = c_tlDCbQ1c3 f n := by
 simp only [p_tlDCbQ1c3, c_tlDCbQ1c3, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlDCbQ1c4 (f : ℚ) (n : ℕ) :
 (p_tlDCbQ1c4 f).coeff n = c_tlDCbQ1c4 f n := by
 simp only [p_tlDCbQ1c4, c_tlDCbQ1c4, Polynomial.coeff_add, Polynomial.coeff_monomial]

theorem coeff_table_p_tlDCbQ1c5 (f : ℚ) (n : ℕ) :
 (p_tlDCbQ1c5 f).coeff n = c_tlDCbQ1c5 f n := by
 simp only [p_tlDCbQ1c5, c_tlDCbQ1c5, Polynomial.coeff_add, Polynomial.coeff_monomial]

end MazurTransfer.Order27DCb1Polynomial

#print axioms MazurTransfer.Order27DCb1Polynomial.coeff_table_p_tlDSqP0c3

open Polynomial MazurTransfer.Order27DCb1Polynomial

theorem solution :
∀ (f : ℚ) (n : ℕ),
((p_tlDSqP0c3 f).coeff n = c_tlDSqP0c3 f n) ∧
((p_tlDSqP0c4 f).coeff n = c_tlDSqP0c4 f n) ∧
((p_tlDSqP0c5 f).coeff n = c_tlDSqP0c5 f n) ∧
((p_tlD0 f).coeff n = c_tlD0 f n) ∧
((p_tlD1 f).coeff n = c_tlD1 f n) ∧
((p_tlT0 f).coeff n = c_tlT0 f n) ∧
((p_tlT1 f).coeff n = c_tlT1 f n) ∧
((p_tlT2 f).coeff n = c_tlT2 f n) ∧
((p_tlT3 f).coeff n = c_tlT3 f n) ∧
((p_tlDCbP1c0 f).coeff n = c_tlDCbP1c0 f n) ∧
((p_tlDCbP1c1 f).coeff n = c_tlDCbP1c1 f n) ∧
((p_tlDCbP1c2 f).coeff n = c_tlDCbP1c2 f n) ∧
((p_tlDCbP1c3 f).coeff n = c_tlDCbP1c3 f n) ∧
((p_tlDCbP1c4 f).coeff n = c_tlDCbP1c4 f n) ∧
((p_tlDCbP1c5 f).coeff n = c_tlDCbP1c5 f n) ∧
((p_tlDCbP1c6 f).coeff n = c_tlDCbP1c6 f n) ∧
((p_tlDCbP1c7 f).coeff n = c_tlDCbP1c7 f n) ∧
((p_tlDCbP1c8 f).coeff n = c_tlDCbP1c8 f n) ∧
((p_tlDCbP1c9 f).coeff n = c_tlDCbP1c9 f n) ∧
((p_tlDCbP1c10 f).coeff n = c_tlDCbP1c10 f n) ∧
((p_tlDCbP1c11 f).coeff n = c_tlDCbP1c11 f n) ∧
((p_tlDCbP1c12 f).coeff n = c_tlDCbP1c12 f n) ∧
((p_tlDCbQ1c0 f).coeff n = c_tlDCbQ1c0 f n) ∧
((p_tlDCbQ1c1 f).coeff n = c_tlDCbQ1c1 f n) ∧
((p_tlDCbQ1c2 f).coeff n = c_tlDCbQ1c2 f n) ∧
((p_tlDCbQ1c3 f).coeff n = c_tlDCbQ1c3 f n) ∧
((p_tlDCbQ1c4 f).coeff n = c_tlDCbQ1c4 f n) ∧
((p_tlDCbQ1c5 f).coeff n = c_tlDCbQ1c5 f n) := by
 intro f n
 exact ⟨coeff_table_p_tlDSqP0c3 f n, coeff_table_p_tlDSqP0c4 f n, coeff_table_p_tlDSqP0c5 f n, coeff_table_p_tlD0 f n, coeff_table_p_tlD1 f n, coeff_table_p_tlT0 f n, coeff_table_p_tlT1 f n, coeff_table_p_tlT2 f n, coeff_table_p_tlT3 f n, coeff_table_p_tlDCbP1c0 f n, coeff_table_p_tlDCbP1c1 f n, coeff_table_p_tlDCbP1c2 f n, coeff_table_p_tlDCbP1c3 f n, coeff_table_p_tlDCbP1c4 f n, coeff_table_p_tlDCbP1c5 f n, coeff_table_p_tlDCbP1c6 f n, coeff_table_p_tlDCbP1c7 f n, coeff_table_p_tlDCbP1c8 f n, coeff_table_p_tlDCbP1c9 f n, coeff_table_p_tlDCbP1c10 f n, coeff_table_p_tlDCbP1c11 f n, coeff_table_p_tlDCbP1c12 f n, coeff_table_p_tlDCbQ1c0 f n, coeff_table_p_tlDCbQ1c1 f n, coeff_table_p_tlDCbQ1c2 f n, coeff_table_p_tlDCbQ1c3 f n, coeff_table_p_tlDCbQ1c4 f n, coeff_table_p_tlDCbQ1c5 f n⟩
#print axioms solution
