-- Prove2me | solution 1 for OAI.InternalCatalan.fixedIntegerBaseCanonical_mod101_rows_0_11
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T19:54:29.75744+00:00
-- url     : https://prove2.me/submissions/b00958ff-2a50-4784-96b1-e9294aac196d

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_OAICatalanIrrationality

section
-- module Solutions.OAICatalan.Catalan.Estimates.FixedTypedChebyshevTData
namespace OAI


noncomputable section
open Polynomial
namespace InternalCatalan

def fixedChebyshevTData_0 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ)

def fixedChebyshevTData_1 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (1 : ℤ)

def fixedChebyshevTData_2 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (2 : ℤ)

def fixedChebyshevTData_3 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-3 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (4 : ℤ)

def fixedChebyshevTData_4 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-8 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (8 : ℤ)

def fixedChebyshevTData_5 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (5 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-20 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (16 : ℤ)

def fixedChebyshevTData_6 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (18 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-48 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (32 : ℤ)

def fixedChebyshevTData_7 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-7 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (56 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-112 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (64 : ℤ)






































end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Polynomial.CentralCoefficients
namespace OAI

namespace InternalCatalan

section

open scoped BigOperators



@[simp] theorem centralCoeff_zero : centralCoeff 0 = 1 := by
  norm_num [centralCoeff]

@[simp] theorem centralCoeffKernel_zero : centralCoeffKernel 0 = 1 := by
  norm_num [centralCoeffKernel]





@[simp] theorem momentScalar_zero : momentScalar 0 = 2 := by
  norm_num [momentScalar]





@[simp] theorem boundaryMinus_zero : boundaryMinus 0 = 0 := rfl
@[simp] theorem boundaryMinus_one : boundaryMinus 1 = 2 := rfl
@[simp] theorem boundaryPlus_zero : boundaryPlus 0 = 0 := rfl
@[simp] theorem boundaryPlus_one : boundaryPlus 1 = 0 := rfl








@[simp] theorem momentRat_zero_right (i : ℕ) : momentRat i 0 = boundaryMinus i := by
  simp [momentRat]

@[simp] theorem momentRat_zero_left (j : ℕ) : momentRat 0 j = boundaryPlus j := by
  cases j with
  | zero => simp [momentRat]
  | succ j => simp [momentRat]






@[simp] theorem harmonicRat_zero (d : ℕ) : harmonicRat d 0 = 0 := by
  simp [harmonicRat]



@[simp] theorem zetaRat_diagonal (i : ℕ) : zetaRat i i = -harmonicRat 2 i := by
  simp [zetaRat]




end













end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.RealColumnDeterminant
namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial




@[simp] theorem reversedRow_zero (C : ℕ) : reversedRow C 0 = 0 := by
  simp [reversedRow]

theorem reversedRow_coeff (C : ℕ) (F : ℤ[X]) (i : ℕ) :
    (reversedRow C F).coeff i = if i < C then F.coeff (C - 1 - i) else 0 := by
  classical
  unfold reversedRow
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases hi : i < C
  · rw [if_pos hi, Finset.sum_eq_single (C - 1 - i)]
    · rw [if_pos (by omega : i = C - 1 - (C - 1 - i))]
    · intro u hu hne
      have hu' := Finset.mem_range.mp hu
      rw [if_neg (by omega : i ≠ C - 1 - u)]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro u hu
    have hu' := Finset.mem_range.mp hu
    rw [if_neg (by omega : i ≠ C - 1 - u)]










theorem rowD_eq_zero_of_distance_zero {N r : ℕ} (hd : rowDistance N r = 0) :
    rowD N r = 0 := by
  simp [rowD, hd]
















theorem fixedTyped_reversedRow_add (F G : ℤ[X]) :
    reversedRow 63 (F + G) = reversedRow 63 F + reversedRow 63 G := by
  ext i
  simp only [reversedRow_coeff, coeff_add]
  split_ifs <;> simp

theorem fixedTyped_reversedRow_monomial (c : ℤ) (k : ℕ) (hk : k < 63) :
    reversedRow 63 (Polynomial.monomial (R := ℤ) k c) =
      Polynomial.monomial (R := ℤ) (62 - k) c := by
  ext i
  simp only [reversedRow_coeff, coeff_monomial]
  split_ifs <;> omega

theorem fixedTyped_rowFactor (p : ℤ[X]) :
    (1 - X) ^ 2 * p = p - 2 * (X * p) + X * (X * p) := by
  ring

theorem fixedTyped_rowP_of_parameters (N r exponent cutoff : ℕ) (index : ℤ)
    (F : ℤ[X]) (hh : h N = exponent) (hC : Cdegree N = cutoff)
    (hi : (rowDistance N r : ℤ) = index) (hF : Chebyshev.T ℤ index = F) :
    rowP N r = (1 - X) ^ exponent * reversedRow cutoff F := by
  unfold rowP
  rw [hh, hC, hi, hF]

theorem fixedTyped_rowD_of_parameters (N r exponent cutoff : ℕ) (index sign : ℤ)
    (F : ℤ[X]) (hh : h N = exponent) (hC : Cdegree N = cutoff)
    (hs : Int.sign (rowOffset N r) = sign)
    (hi : (rowDistance N r : ℤ) - 1 = index) (hF : Chebyshev.U ℤ index = F) :
    rowD N r = Polynomial.C sign * (1 - X) ^ exponent * reversedRow cutoff F := by
  unfold rowD
  rw [hh, hC, hs, hi, hF]




end

section

open scoped BigOperators









end

section

open Polynomial







variable {K : Type*} [Field K]




end

open Polynomial



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.FixedTypedChebyshevUData
namespace OAI


noncomputable section
open Polynomial
namespace InternalCatalan

def fixedChebyshevUData_0 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ)

def fixedChebyshevUData_1 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (2 : ℤ)

def fixedChebyshevUData_2 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (4 : ℤ)

def fixedChebyshevUData_3 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-4 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (8 : ℤ)

def fixedChebyshevUData_4 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-12 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (16 : ℤ)

def fixedChebyshevUData_5 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (6 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-32 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (32 : ℤ)

def fixedChebyshevUData_6 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (24 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-80 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (64 : ℤ)






































end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.FixedTypedChebyshevU18To23
namespace OAI


noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevU_typed_0 :
    Chebyshev.U ℤ 0 = fixedChebyshevUData_0 := by
  norm_num [fixedChebyshevUData_0, ← Polynomial.C_mul_X_pow_eq_monomial]

theorem fixed_chebyshevU_typed_1 :
    Chebyshev.U ℤ 1 = fixedChebyshevUData_1 := by
  norm_num [fixedChebyshevUData_1, ← Polynomial.C_mul_X_pow_eq_monomial]

theorem fixed_chebyshevU_typed_2 :
    Chebyshev.U ℤ 2 = fixedChebyshevUData_2 := by
  calc
    Chebyshev.U ℤ 2 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 1 - Chebyshev.U ℤ 0 :=
      Chebyshev.U_add_two ℤ 0
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_1 - fixedChebyshevUData_0 := by
      rw [fixed_chebyshevU_typed_1, fixed_chebyshevU_typed_0]
    _ = fixedChebyshevUData_2 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_1, fixedChebyshevUData_0, fixedChebyshevUData_2, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_1, fixedChebyshevUData_0, fixedChebyshevUData_2, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 2
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 2, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 2 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_3 :
    Chebyshev.U ℤ 3 = fixedChebyshevUData_3 := by
  calc
    Chebyshev.U ℤ 3 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 2 - Chebyshev.U ℤ 1 :=
      Chebyshev.U_add_two ℤ 1
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_2 - fixedChebyshevUData_1 := by
      rw [fixed_chebyshevU_typed_2, fixed_chebyshevU_typed_1]
    _ = fixedChebyshevUData_3 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_2, fixedChebyshevUData_1, fixedChebyshevUData_3, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_2, fixedChebyshevUData_1, fixedChebyshevUData_3, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 3
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 3, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 3 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_4 :
    Chebyshev.U ℤ 4 = fixedChebyshevUData_4 := by
  calc
    Chebyshev.U ℤ 4 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 3 - Chebyshev.U ℤ 2 :=
      Chebyshev.U_add_two ℤ 2
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_3 - fixedChebyshevUData_2 := by
      rw [fixed_chebyshevU_typed_3, fixed_chebyshevU_typed_2]
    _ = fixedChebyshevUData_4 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_3, fixedChebyshevUData_2, fixedChebyshevUData_4, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_3, fixedChebyshevUData_2, fixedChebyshevUData_4, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 4
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 4, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 4 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_5 :
    Chebyshev.U ℤ 5 = fixedChebyshevUData_5 := by
  calc
    Chebyshev.U ℤ 5 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 4 - Chebyshev.U ℤ 3 :=
      Chebyshev.U_add_two ℤ 3
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_4 - fixedChebyshevUData_3 := by
      rw [fixed_chebyshevU_typed_4, fixed_chebyshevU_typed_3]
    _ = fixedChebyshevUData_5 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_4, fixedChebyshevUData_3, fixedChebyshevUData_5, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_4, fixedChebyshevUData_3, fixedChebyshevUData_5, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 5
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 5, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 5 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_6 :
    Chebyshev.U ℤ 6 = fixedChebyshevUData_6 := by
  calc
    Chebyshev.U ℤ 6 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 5 - Chebyshev.U ℤ 4 :=
      Chebyshev.U_add_two ℤ 4
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_5 - fixedChebyshevUData_4 := by
      rw [fixed_chebyshevU_typed_5, fixed_chebyshevU_typed_4]
    _ = fixedChebyshevUData_6 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_5, fixedChebyshevUData_4, fixedChebyshevUData_6, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_5, fixedChebyshevUData_4, fixedChebyshevUData_6, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 6
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 6, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 6 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]





end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan








end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan







end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.FixedTypedChebyshevT39To41
namespace OAI


noncomputable section
open Polynomial
namespace InternalCatalan



end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevT_typed_0 :
    Chebyshev.T ℤ 0 = fixedChebyshevTData_0 := by
  norm_num [fixedChebyshevTData_0, ← Polynomial.C_mul_X_pow_eq_monomial]

theorem fixed_chebyshevT_typed_1 :
    Chebyshev.T ℤ 1 = fixedChebyshevTData_1 := by
  norm_num [fixedChebyshevTData_1, ← Polynomial.C_mul_X_pow_eq_monomial]

theorem fixed_chebyshevT_typed_2 :
    Chebyshev.T ℤ 2 = fixedChebyshevTData_2 := by
  calc
    Chebyshev.T ℤ 2 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 1 - Chebyshev.T ℤ 0 :=
      Chebyshev.T_add_two ℤ 0
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_1 - fixedChebyshevTData_0 := by
      rw [fixed_chebyshevT_typed_1, fixed_chebyshevT_typed_0]
    _ = fixedChebyshevTData_2 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_1, fixedChebyshevTData_0, fixedChebyshevTData_2, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_1, fixedChebyshevTData_0, fixedChebyshevTData_2, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 2
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 2, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 2 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_3 :
    Chebyshev.T ℤ 3 = fixedChebyshevTData_3 := by
  calc
    Chebyshev.T ℤ 3 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 2 - Chebyshev.T ℤ 1 :=
      Chebyshev.T_add_two ℤ 1
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_2 - fixedChebyshevTData_1 := by
      rw [fixed_chebyshevT_typed_2, fixed_chebyshevT_typed_1]
    _ = fixedChebyshevTData_3 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_2, fixedChebyshevTData_1, fixedChebyshevTData_3, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_2, fixedChebyshevTData_1, fixedChebyshevTData_3, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 3
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 3, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 3 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_4 :
    Chebyshev.T ℤ 4 = fixedChebyshevTData_4 := by
  calc
    Chebyshev.T ℤ 4 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 3 - Chebyshev.T ℤ 2 :=
      Chebyshev.T_add_two ℤ 2
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_3 - fixedChebyshevTData_2 := by
      rw [fixed_chebyshevT_typed_3, fixed_chebyshevT_typed_2]
    _ = fixedChebyshevTData_4 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_3, fixedChebyshevTData_2, fixedChebyshevTData_4, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_3, fixedChebyshevTData_2, fixedChebyshevTData_4, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 4
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 4, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 4 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_5 :
    Chebyshev.T ℤ 5 = fixedChebyshevTData_5 := by
  calc
    Chebyshev.T ℤ 5 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 4 - Chebyshev.T ℤ 3 :=
      Chebyshev.T_add_two ℤ 3
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_4 - fixedChebyshevTData_3 := by
      rw [fixed_chebyshevT_typed_4, fixed_chebyshevT_typed_3]
    _ = fixedChebyshevTData_5 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_4, fixedChebyshevTData_3, fixedChebyshevTData_5, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_4, fixedChebyshevTData_3, fixedChebyshevTData_5, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 5
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 5, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 5 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_6 :
    Chebyshev.T ℤ 6 = fixedChebyshevTData_6 := by
  calc
    Chebyshev.T ℤ 6 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 5 - Chebyshev.T ℤ 4 :=
      Chebyshev.T_add_two ℤ 4
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_5 - fixedChebyshevTData_4 := by
      rw [fixed_chebyshevT_typed_5, fixed_chebyshevT_typed_4]
    _ = fixedChebyshevTData_6 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_5, fixedChebyshevTData_4, fixedChebyshevTData_6, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_5, fixedChebyshevTData_4, fixedChebyshevTData_6, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 6
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 6, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 6 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_7 :
    Chebyshev.T ℤ 7 = fixedChebyshevTData_7 := by
  calc
    Chebyshev.T ℤ 7 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 6 - Chebyshev.T ℤ 5 :=
      Chebyshev.T_add_two ℤ 5
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_6 - fixedChebyshevTData_5 := by
      rw [fixed_chebyshevT_typed_6, fixed_chebyshevT_typed_5]
    _ = fixedChebyshevTData_7 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_6, fixedChebyshevTData_5, fixedChebyshevTData_7, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_6, fixedChebyshevTData_5, fixedChebyshevTData_7, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 7
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 7, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 7 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]




end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan








end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan







end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan






end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan






end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan





end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan




end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan




end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan




end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.FixedCompactReversedT0To7
namespace OAI


noncomputable section
open Polynomial
namespace InternalCatalan





end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan




end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan




end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan




end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan




end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan



end InternalCatalan

end




noncomputable section
open Polynomial
namespace InternalCatalan

def fixedReversedTData_0 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ)

def fixedReversedTCoeff_0 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0)

theorem fixed_reversedT_typed_data_0 : reversedRow 63 fixedChebyshevTData_0 = fixedReversedTData_0 := by
  simp only [fixedChebyshevTData_0, fixedReversedTData_0]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide)]

theorem fixed_reversedT_typed_coeff_0 (n : ℕ) :
    fixedReversedTData_0.coeff n = fixedReversedTCoeff_0 n := by
  simp only [fixedReversedTData_0, fixedReversedTCoeff_0, coeff_monomial]

theorem fixed_reversedT_typed_tail_0 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_0 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_0, if_neg]

def fixedReversedTData_1 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (1 : ℤ)

def fixedReversedTCoeff_1 (n : ℕ) : ℤ :=
    (if 61 = n then (1 : ℤ) else 0)

theorem fixed_reversedT_typed_data_1 : reversedRow 63 fixedChebyshevTData_1 = fixedReversedTData_1 := by
  simp only [fixedChebyshevTData_1, fixedReversedTData_1]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 1 (by decide)]

theorem fixed_reversedT_typed_coeff_1 (n : ℕ) :
    fixedReversedTData_1.coeff n = fixedReversedTCoeff_1 n := by
  simp only [fixedReversedTData_1, fixedReversedTCoeff_1, coeff_monomial]

theorem fixed_reversedT_typed_tail_1 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_1 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_1, if_neg]

def fixedReversedTData_2 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (2 : ℤ)

def fixedReversedTCoeff_2 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (2 : ℤ) else 0)

theorem fixed_reversedT_typed_data_2 : reversedRow 63 fixedChebyshevTData_2 = fixedReversedTData_2 := by
  simp only [fixedChebyshevTData_2, fixedReversedTData_2, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (2 : ℤ) 2 (by decide)]

theorem fixed_reversedT_typed_coeff_2 (n : ℕ) :
    fixedReversedTData_2.coeff n = fixedReversedTCoeff_2 n := by
  simp only [fixedReversedTData_2, fixedReversedTCoeff_2, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_2 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_2 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_2, if_neg, add_zero]

def fixedReversedTData_3 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-3 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (4 : ℤ)

def fixedReversedTCoeff_3 (n : ℕ) : ℤ :=
    (if 61 = n then (-3 : ℤ) else 0) +
    (if 59 = n then (4 : ℤ) else 0)

theorem fixed_reversedT_typed_data_3 : reversedRow 63 fixedChebyshevTData_3 = fixedReversedTData_3 := by
  simp only [fixedChebyshevTData_3, fixedReversedTData_3, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-3 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (4 : ℤ) 3 (by decide)]

theorem fixed_reversedT_typed_coeff_3 (n : ℕ) :
    fixedReversedTData_3.coeff n = fixedReversedTCoeff_3 n := by
  simp only [fixedReversedTData_3, fixedReversedTCoeff_3, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_3 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_3 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_3, if_neg, add_zero]

def fixedReversedTData_4 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-8 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (8 : ℤ)

def fixedReversedTCoeff_4 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-8 : ℤ) else 0) +
    (if 58 = n then (8 : ℤ) else 0)

theorem fixed_reversedT_typed_data_4 : reversedRow 63 fixedChebyshevTData_4 = fixedReversedTData_4 := by
  simp only [fixedChebyshevTData_4, fixedReversedTData_4, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-8 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (8 : ℤ) 4 (by decide)]

theorem fixed_reversedT_typed_coeff_4 (n : ℕ) :
    fixedReversedTData_4.coeff n = fixedReversedTCoeff_4 n := by
  simp only [fixedReversedTData_4, fixedReversedTCoeff_4, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_4 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_4 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_4, if_neg, add_zero]

def fixedReversedTData_5 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (5 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-20 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (16 : ℤ)

def fixedReversedTCoeff_5 (n : ℕ) : ℤ :=
    (if 61 = n then (5 : ℤ) else 0) +
    (if 59 = n then (-20 : ℤ) else 0) +
    (if 57 = n then (16 : ℤ) else 0)

theorem fixed_reversedT_typed_data_5 : reversedRow 63 fixedChebyshevTData_5 = fixedReversedTData_5 := by
  simp only [fixedChebyshevTData_5, fixedReversedTData_5, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (5 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-20 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (16 : ℤ) 5 (by decide)]

theorem fixed_reversedT_typed_coeff_5 (n : ℕ) :
    fixedReversedTData_5.coeff n = fixedReversedTCoeff_5 n := by
  simp only [fixedReversedTData_5, fixedReversedTCoeff_5, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_5 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_5 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_5, if_neg, add_zero]

def fixedReversedTData_6 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (18 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-48 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (32 : ℤ)

def fixedReversedTCoeff_6 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (18 : ℤ) else 0) +
    (if 58 = n then (-48 : ℤ) else 0) +
    (if 56 = n then (32 : ℤ) else 0)

theorem fixed_reversedT_typed_data_6 : reversedRow 63 fixedChebyshevTData_6 = fixedReversedTData_6 := by
  simp only [fixedChebyshevTData_6, fixedReversedTData_6, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (18 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-48 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (32 : ℤ) 6 (by decide)]

theorem fixed_reversedT_typed_coeff_6 (n : ℕ) :
    fixedReversedTData_6.coeff n = fixedReversedTCoeff_6 n := by
  simp only [fixedReversedTData_6, fixedReversedTCoeff_6, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_6 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_6 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_6, if_neg, add_zero]

def fixedReversedTData_7 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-7 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (56 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-112 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (64 : ℤ)

def fixedReversedTCoeff_7 (n : ℕ) : ℤ :=
    (if 61 = n then (-7 : ℤ) else 0) +
    (if 59 = n then (56 : ℤ) else 0) +
    (if 57 = n then (-112 : ℤ) else 0) +
    (if 55 = n then (64 : ℤ) else 0)

theorem fixed_reversedT_typed_data_7 : reversedRow 63 fixedChebyshevTData_7 = fixedReversedTData_7 := by
  simp only [fixedChebyshevTData_7, fixedReversedTData_7, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-7 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (56 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-112 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (64 : ℤ) 7 (by decide)]

theorem fixed_reversedT_typed_coeff_7 (n : ℕ) :
    fixedReversedTData_7.coeff n = fixedReversedTCoeff_7 n := by
  simp only [fixedReversedTData_7, fixedReversedTCoeff_7, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_7 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_7 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_7, if_neg, add_zero]

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.FixedCompactReversedU0To7
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedReversedUData_0 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ)

def fixedReversedUCoeff_0 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0)

theorem fixed_reversedU_typed_data_0 : reversedRow 63 fixedChebyshevUData_0 = fixedReversedUData_0 := by
  simp only [fixedChebyshevUData_0, fixedReversedUData_0]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide)]

theorem fixed_reversedU_typed_coeff_0 (n : ℕ) :
    fixedReversedUData_0.coeff n = fixedReversedUCoeff_0 n := by
  simp only [fixedReversedUData_0, fixedReversedUCoeff_0, coeff_monomial]

theorem fixed_reversedU_typed_tail_0 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_0 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_0, if_neg]

def fixedReversedUData_1 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (2 : ℤ)

def fixedReversedUCoeff_1 (n : ℕ) : ℤ :=
    (if 61 = n then (2 : ℤ) else 0)

theorem fixed_reversedU_typed_data_1 : reversedRow 63 fixedChebyshevUData_1 = fixedReversedUData_1 := by
  simp only [fixedChebyshevUData_1, fixedReversedUData_1]
  rw [fixedTyped_reversedRow_monomial (2 : ℤ) 1 (by decide)]

theorem fixed_reversedU_typed_coeff_1 (n : ℕ) :
    fixedReversedUData_1.coeff n = fixedReversedUCoeff_1 n := by
  simp only [fixedReversedUData_1, fixedReversedUCoeff_1, coeff_monomial]

theorem fixed_reversedU_typed_tail_1 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_1 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_1, if_neg]

def fixedReversedUData_2 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (4 : ℤ)

def fixedReversedUCoeff_2 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (4 : ℤ) else 0)

theorem fixed_reversedU_typed_data_2 : reversedRow 63 fixedChebyshevUData_2 = fixedReversedUData_2 := by
  simp only [fixedChebyshevUData_2, fixedReversedUData_2, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (4 : ℤ) 2 (by decide)]

theorem fixed_reversedU_typed_coeff_2 (n : ℕ) :
    fixedReversedUData_2.coeff n = fixedReversedUCoeff_2 n := by
  simp only [fixedReversedUData_2, fixedReversedUCoeff_2, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_2 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_2 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_2, if_neg, add_zero]

def fixedReversedUData_3 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-4 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (8 : ℤ)

def fixedReversedUCoeff_3 (n : ℕ) : ℤ :=
    (if 61 = n then (-4 : ℤ) else 0) +
    (if 59 = n then (8 : ℤ) else 0)

theorem fixed_reversedU_typed_data_3 : reversedRow 63 fixedChebyshevUData_3 = fixedReversedUData_3 := by
  simp only [fixedChebyshevUData_3, fixedReversedUData_3, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-4 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (8 : ℤ) 3 (by decide)]

theorem fixed_reversedU_typed_coeff_3 (n : ℕ) :
    fixedReversedUData_3.coeff n = fixedReversedUCoeff_3 n := by
  simp only [fixedReversedUData_3, fixedReversedUCoeff_3, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_3 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_3 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_3, if_neg, add_zero]

def fixedReversedUData_4 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-12 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (16 : ℤ)

def fixedReversedUCoeff_4 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-12 : ℤ) else 0) +
    (if 58 = n then (16 : ℤ) else 0)

theorem fixed_reversedU_typed_data_4 : reversedRow 63 fixedChebyshevUData_4 = fixedReversedUData_4 := by
  simp only [fixedChebyshevUData_4, fixedReversedUData_4, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-12 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (16 : ℤ) 4 (by decide)]

theorem fixed_reversedU_typed_coeff_4 (n : ℕ) :
    fixedReversedUData_4.coeff n = fixedReversedUCoeff_4 n := by
  simp only [fixedReversedUData_4, fixedReversedUCoeff_4, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_4 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_4 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_4, if_neg, add_zero]

def fixedReversedUData_5 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (6 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-32 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (32 : ℤ)

def fixedReversedUCoeff_5 (n : ℕ) : ℤ :=
    (if 61 = n then (6 : ℤ) else 0) +
    (if 59 = n then (-32 : ℤ) else 0) +
    (if 57 = n then (32 : ℤ) else 0)

theorem fixed_reversedU_typed_data_5 : reversedRow 63 fixedChebyshevUData_5 = fixedReversedUData_5 := by
  simp only [fixedChebyshevUData_5, fixedReversedUData_5, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (6 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-32 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (32 : ℤ) 5 (by decide)]

theorem fixed_reversedU_typed_coeff_5 (n : ℕ) :
    fixedReversedUData_5.coeff n = fixedReversedUCoeff_5 n := by
  simp only [fixedReversedUData_5, fixedReversedUCoeff_5, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_5 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_5 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_5, if_neg, add_zero]

def fixedReversedUData_6 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (24 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-80 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (64 : ℤ)

def fixedReversedUCoeff_6 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (24 : ℤ) else 0) +
    (if 58 = n then (-80 : ℤ) else 0) +
    (if 56 = n then (64 : ℤ) else 0)

theorem fixed_reversedU_typed_data_6 : reversedRow 63 fixedChebyshevUData_6 = fixedReversedUData_6 := by
  simp only [fixedChebyshevUData_6, fixedReversedUData_6, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (24 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-80 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (64 : ℤ) 6 (by decide)]

theorem fixed_reversedU_typed_coeff_6 (n : ℕ) :
    fixedReversedUData_6.coeff n = fixedReversedUCoeff_6 n := by
  simp only [fixedReversedUData_6, fixedReversedUCoeff_6, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_6 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_6 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_6, if_neg, add_zero]






end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow0
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_0 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 58 (8 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-16 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (16 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-7 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_0 (n : ℕ) : ℤ :=
    (if 58 = n then (8 : ℤ) else 0) +
    (if 59 = n then (-16 : ℤ) else 0) +
    (if 61 = n then (16 : ℤ) else 0) +
    (if 62 = n then (-7 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_0 (n : ℕ) :
    fixedRowPData_0.coeff n = fixedRowPCoeff_0 n := by
  simp only [fixedRowPData_0, fixedRowPCoeff_0, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_0 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_0 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_0, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_0 : ∀ k : Fin 63,
    fixedReversedTCoeff_4 (k.val + 2) - 2 * fixedReversedTCoeff_4 (k.val + 1) + fixedReversedTCoeff_4 k.val = fixedRowPCoeff_0 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_0 :
    (1 - X) ^ 2 * fixedReversedTData_4 = fixedRowPData_0 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_4, fixed_rowP_typed_coeff_0]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_4, fixed_rowP_typed_coeff_0]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_4, fixed_rowP_typed_coeff_0]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_0 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_4 _ (by omega),
              fixed_reversedT_typed_tail_4 _ (by omega), fixed_reversedT_typed_tail_4 _ hn',
              fixed_rowP_typed_tail_0 _ (by omega)]
            decide

theorem fixed_rowP_typed_0 : rowP 1 0 = fixedRowPData_0 := by
  calc
    rowP 1 0 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_4 :=
      fixedTyped_rowP_of_parameters 1 0 2 63 4 fixedChebyshevTData_4
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_4
    _ = fixedRowPData_0 := by
      rw [fixed_reversedT_typed_data_4, fixed_rowP_typed_factor_0]

def fixedRowDData_0 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 59 (-8 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (16 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-4 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-8 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (4 : ℤ)

def fixedRowDCoeff_0 (n : ℕ) : ℤ :=
    (if 59 = n then (-8 : ℤ) else 0) +
    (if 60 = n then (16 : ℤ) else 0) +
    (if 61 = n then (-4 : ℤ) else 0) +
    (if 62 = n then (-8 : ℤ) else 0) +
    (if 63 = n then (4 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_0 (n : ℕ) :
    fixedRowDData_0.coeff n = fixedRowDCoeff_0 n := by
  simp only [fixedRowDData_0, fixedRowDCoeff_0, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_0 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_0 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_0, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_0 : ∀ k : Fin 63,
    (-1 : ℤ) * (fixedReversedUCoeff_3 (k.val + 2) - 2 * fixedReversedUCoeff_3 (k.val + 1) + fixedReversedUCoeff_3 k.val) = fixedRowDCoeff_0 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_0 :
    Polynomial.C (-1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_3 = fixedRowDData_0 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_3, fixed_rowD_typed_coeff_0]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_3, fixed_rowD_typed_coeff_0]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_3, fixed_rowD_typed_coeff_0]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_0 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_3 _ (by omega),
              fixed_reversedU_typed_tail_3 _ (by omega), fixed_reversedU_typed_tail_3 _ hn',
              fixed_rowD_typed_tail_0 _ (by omega)]
            decide

theorem fixed_rowD_typed_0 : rowD 1 0 = fixedRowDData_0 := by
  calc
    rowD 1 0 = Polynomial.C (-1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_3 :=
      fixedTyped_rowD_of_parameters 1 0 2 63 3 (-1)
        fixedChebyshevUData_3 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_3
    _ = fixedRowDData_0 := by
      rw [fixed_reversedU_typed_data_3, fixed_rowD_typed_factor_0]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow1
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_1 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 59 (4 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-8 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (6 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-3 : ℤ)

def fixedRowPCoeff_1 (n : ℕ) : ℤ :=
    (if 59 = n then (4 : ℤ) else 0) +
    (if 60 = n then (-8 : ℤ) else 0) +
    (if 61 = n then (1 : ℤ) else 0) +
    (if 62 = n then (6 : ℤ) else 0) +
    (if 63 = n then (-3 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_1 (n : ℕ) :
    fixedRowPData_1.coeff n = fixedRowPCoeff_1 n := by
  simp only [fixedRowPData_1, fixedRowPCoeff_1, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_1 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_1 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_1, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_1 : ∀ k : Fin 63,
    fixedReversedTCoeff_3 (k.val + 2) - 2 * fixedReversedTCoeff_3 (k.val + 1) + fixedReversedTCoeff_3 k.val = fixedRowPCoeff_1 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_1 :
    (1 - X) ^ 2 * fixedReversedTData_3 = fixedRowPData_1 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_3, fixed_rowP_typed_coeff_1]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_3, fixed_rowP_typed_coeff_1]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_3, fixed_rowP_typed_coeff_1]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_1 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_3 _ (by omega),
              fixed_reversedT_typed_tail_3 _ (by omega), fixed_reversedT_typed_tail_3 _ hn',
              fixed_rowP_typed_tail_1 _ (by omega)]
            decide

theorem fixed_rowP_typed_1 : rowP 1 1 = fixedRowPData_1 := by
  calc
    rowP 1 1 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_3 :=
      fixedTyped_rowP_of_parameters 1 1 2 63 3 fixedChebyshevTData_3
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_3
    _ = fixedRowPData_1 := by
      rw [fixed_reversedT_typed_data_3, fixed_rowP_typed_factor_1]

def fixedRowDData_1 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 60 (-4 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (8 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-3 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowDCoeff_1 (n : ℕ) : ℤ :=
    (if 60 = n then (-4 : ℤ) else 0) +
    (if 61 = n then (8 : ℤ) else 0) +
    (if 62 = n then (-3 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_1 (n : ℕ) :
    fixedRowDData_1.coeff n = fixedRowDCoeff_1 n := by
  simp only [fixedRowDData_1, fixedRowDCoeff_1, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_1 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_1 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_1, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_1 : ∀ k : Fin 63,
    (-1 : ℤ) * (fixedReversedUCoeff_2 (k.val + 2) - 2 * fixedReversedUCoeff_2 (k.val + 1) + fixedReversedUCoeff_2 k.val) = fixedRowDCoeff_1 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_1 :
    Polynomial.C (-1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_2 = fixedRowDData_1 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_2, fixed_rowD_typed_coeff_1]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_2, fixed_rowD_typed_coeff_1]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_2, fixed_rowD_typed_coeff_1]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_1 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_2 _ (by omega),
              fixed_reversedU_typed_tail_2 _ (by omega), fixed_reversedU_typed_tail_2 _ hn',
              fixed_rowD_typed_tail_1 _ (by omega)]
            decide

theorem fixed_rowD_typed_1 : rowD 1 1 = fixedRowDData_1 := by
  calc
    rowD 1 1 = Polynomial.C (-1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_2 :=
      fixedTyped_rowD_of_parameters 1 1 2 63 2 (-1)
        fixedChebyshevUData_2 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_2
    _ = fixedRowDData_1 := by
      rw [fixed_reversedU_typed_data_2, fixed_rowD_typed_factor_1]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow10
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_10 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 56 (32 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-64 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-16 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (96 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-30 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-36 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (17 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowPCoeff_10 (n : ℕ) : ℤ :=
    (if 56 = n then (32 : ℤ) else 0) +
    (if 57 = n then (-64 : ℤ) else 0) +
    (if 58 = n then (-16 : ℤ) else 0) +
    (if 59 = n then (96 : ℤ) else 0) +
    (if 60 = n then (-30 : ℤ) else 0) +
    (if 61 = n then (-36 : ℤ) else 0) +
    (if 62 = n then (17 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_10 (n : ℕ) :
    fixedRowPData_10.coeff n = fixedRowPCoeff_10 n := by
  simp only [fixedRowPData_10, fixedRowPCoeff_10, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_10 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_10 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_10, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_10 : ∀ k : Fin 63,
    fixedReversedTCoeff_6 (k.val + 2) - 2 * fixedReversedTCoeff_6 (k.val + 1) + fixedReversedTCoeff_6 k.val = fixedRowPCoeff_10 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_10 :
    (1 - X) ^ 2 * fixedReversedTData_6 = fixedRowPData_10 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_6, fixed_rowP_typed_coeff_10]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_6, fixed_rowP_typed_coeff_10]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_6, fixed_rowP_typed_coeff_10]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_10 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_6 _ (by omega),
              fixed_reversedT_typed_tail_6 _ (by omega), fixed_reversedT_typed_tail_6 _ hn',
              fixed_rowP_typed_tail_10 _ (by omega)]
            decide

theorem fixed_rowP_typed_10 : rowP 1 10 = fixedRowPData_10 := by
  calc
    rowP 1 10 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_6 :=
      fixedTyped_rowP_of_parameters 1 10 2 63 6 fixedChebyshevTData_6
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_6
    _ = fixedRowPData_10 := by
      rw [fixed_reversedT_typed_data_6, fixed_rowP_typed_factor_10]

def fixedRowDData_10 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 57 (32 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-64 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (64 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-26 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-12 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (6 : ℤ)

def fixedRowDCoeff_10 (n : ℕ) : ℤ :=
    (if 57 = n then (32 : ℤ) else 0) +
    (if 58 = n then (-64 : ℤ) else 0) +
    (if 60 = n then (64 : ℤ) else 0) +
    (if 61 = n then (-26 : ℤ) else 0) +
    (if 62 = n then (-12 : ℤ) else 0) +
    (if 63 = n then (6 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_10 (n : ℕ) :
    fixedRowDData_10.coeff n = fixedRowDCoeff_10 n := by
  simp only [fixedRowDData_10, fixedRowDCoeff_10, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_10 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_10 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_10, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_10 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_5 (k.val + 2) - 2 * fixedReversedUCoeff_5 (k.val + 1) + fixedReversedUCoeff_5 k.val) = fixedRowDCoeff_10 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_10 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_5 = fixedRowDData_10 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_5, fixed_rowD_typed_coeff_10]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_5, fixed_rowD_typed_coeff_10]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_5, fixed_rowD_typed_coeff_10]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_10 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_5 _ (by omega),
              fixed_reversedU_typed_tail_5 _ (by omega), fixed_reversedU_typed_tail_5 _ hn',
              fixed_rowD_typed_tail_10 _ (by omega)]
            decide

theorem fixed_rowD_typed_10 : rowD 1 10 = fixedRowDData_10 := by
  calc
    rowD 1 10 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_5 :=
      fixedTyped_rowD_of_parameters 1 10 2 63 5 (1)
        fixedChebyshevUData_5 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_5
    _ = fixedRowDData_10 := by
      rw [fixed_reversedU_typed_data_5, fixed_rowD_typed_factor_10]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow11
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_11 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 55 (64 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-128 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-48 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (224 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-56 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-112 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (49 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (14 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-7 : ℤ)

def fixedRowPCoeff_11 (n : ℕ) : ℤ :=
    (if 55 = n then (64 : ℤ) else 0) +
    (if 56 = n then (-128 : ℤ) else 0) +
    (if 57 = n then (-48 : ℤ) else 0) +
    (if 58 = n then (224 : ℤ) else 0) +
    (if 59 = n then (-56 : ℤ) else 0) +
    (if 60 = n then (-112 : ℤ) else 0) +
    (if 61 = n then (49 : ℤ) else 0) +
    (if 62 = n then (14 : ℤ) else 0) +
    (if 63 = n then (-7 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_11 (n : ℕ) :
    fixedRowPData_11.coeff n = fixedRowPCoeff_11 n := by
  simp only [fixedRowPData_11, fixedRowPCoeff_11, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_11 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_11 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_11, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_11 : ∀ k : Fin 63,
    fixedReversedTCoeff_7 (k.val + 2) - 2 * fixedReversedTCoeff_7 (k.val + 1) + fixedReversedTCoeff_7 k.val = fixedRowPCoeff_11 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_11 :
    (1 - X) ^ 2 * fixedReversedTData_7 = fixedRowPData_11 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_7, fixed_rowP_typed_coeff_11]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_7, fixed_rowP_typed_coeff_11]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_7, fixed_rowP_typed_coeff_11]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_11 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_7 _ (by omega),
              fixed_reversedT_typed_tail_7 _ (by omega), fixed_reversedT_typed_tail_7 _ hn',
              fixed_rowP_typed_tail_11 _ (by omega)]
            decide

theorem fixed_rowP_typed_11 : rowP 1 11 = fixedRowPData_11 := by
  calc
    rowP 1 11 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_7 :=
      fixedTyped_rowP_of_parameters 1 11 2 63 7 fixedChebyshevTData_7
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_7
    _ = fixedRowPData_11 := by
      rw [fixed_reversedT_typed_data_7, fixed_rowP_typed_factor_11]

def fixedRowDData_11 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 56 (64 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-128 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-16 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (160 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-56 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-48 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (23 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowDCoeff_11 (n : ℕ) : ℤ :=
    (if 56 = n then (64 : ℤ) else 0) +
    (if 57 = n then (-128 : ℤ) else 0) +
    (if 58 = n then (-16 : ℤ) else 0) +
    (if 59 = n then (160 : ℤ) else 0) +
    (if 60 = n then (-56 : ℤ) else 0) +
    (if 61 = n then (-48 : ℤ) else 0) +
    (if 62 = n then (23 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_11 (n : ℕ) :
    fixedRowDData_11.coeff n = fixedRowDCoeff_11 n := by
  simp only [fixedRowDData_11, fixedRowDCoeff_11, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_11 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_11 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_11, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_11 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_6 (k.val + 2) - 2 * fixedReversedUCoeff_6 (k.val + 1) + fixedReversedUCoeff_6 k.val) = fixedRowDCoeff_11 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_11 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_6 = fixedRowDData_11 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_6, fixed_rowD_typed_coeff_11]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_6, fixed_rowD_typed_coeff_11]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_6, fixed_rowD_typed_coeff_11]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_11 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_6 _ (by omega),
              fixed_reversedU_typed_tail_6 _ (by omega), fixed_reversedU_typed_tail_6 _ hn',
              fixed_rowD_typed_tail_11 _ (by omega)]
            decide

theorem fixed_rowD_typed_11 : rowD 1 11 = fixedRowDData_11 := by
  calc
    rowD 1 11 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_6 :=
      fixedTyped_rowD_of_parameters 1 11 2 63 6 (1)
        fixedChebyshevUData_6 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_6
    _ = fixedRowDData_11 := by
      rw [fixed_reversedU_typed_data_6, fixed_rowD_typed_factor_11]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow2
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_2 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 60 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-4 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowPCoeff_2 (n : ℕ) : ℤ :=
    (if 60 = n then (2 : ℤ) else 0) +
    (if 61 = n then (-4 : ℤ) else 0) +
    (if 62 = n then (1 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_2 (n : ℕ) :
    fixedRowPData_2.coeff n = fixedRowPCoeff_2 n := by
  simp only [fixedRowPData_2, fixedRowPCoeff_2, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_2 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_2 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_2, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_2 : ∀ k : Fin 63,
    fixedReversedTCoeff_2 (k.val + 2) - 2 * fixedReversedTCoeff_2 (k.val + 1) + fixedReversedTCoeff_2 k.val = fixedRowPCoeff_2 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_2 :
    (1 - X) ^ 2 * fixedReversedTData_2 = fixedRowPData_2 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_2, fixed_rowP_typed_coeff_2]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_2, fixed_rowP_typed_coeff_2]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_2, fixed_rowP_typed_coeff_2]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_2 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_2 _ (by omega),
              fixed_reversedT_typed_tail_2 _ (by omega), fixed_reversedT_typed_tail_2 _ hn',
              fixed_rowP_typed_tail_2 _ (by omega)]
            decide

theorem fixed_rowP_typed_2 : rowP 1 2 = fixedRowPData_2 := by
  calc
    rowP 1 2 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_2 :=
      fixedTyped_rowP_of_parameters 1 2 2 63 2 fixedChebyshevTData_2
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_2
    _ = fixedRowPData_2 := by
      rw [fixed_reversedT_typed_data_2, fixed_rowP_typed_factor_2]

def fixedRowDData_2 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (4 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ)

def fixedRowDCoeff_2 (n : ℕ) : ℤ :=
    (if 61 = n then (-2 : ℤ) else 0) +
    (if 62 = n then (4 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_2 (n : ℕ) :
    fixedRowDData_2.coeff n = fixedRowDCoeff_2 n := by
  simp only [fixedRowDData_2, fixedRowDCoeff_2, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_2 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_2 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_2, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_2 : ∀ k : Fin 63,
    (-1 : ℤ) * (fixedReversedUCoeff_1 (k.val + 2) - 2 * fixedReversedUCoeff_1 (k.val + 1) + fixedReversedUCoeff_1 k.val) = fixedRowDCoeff_2 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_2 :
    Polynomial.C (-1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_1 = fixedRowDData_2 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_1, fixed_rowD_typed_coeff_2]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_1, fixed_rowD_typed_coeff_2]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_1, fixed_rowD_typed_coeff_2]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_2 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_1 _ (by omega),
              fixed_reversedU_typed_tail_1 _ (by omega), fixed_reversedU_typed_tail_1 _ hn',
              fixed_rowD_typed_tail_2 _ (by omega)]
            decide

theorem fixed_rowD_typed_2 : rowD 1 2 = fixedRowDData_2 := by
  calc
    rowD 1 2 = Polynomial.C (-1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_1 :=
      fixedTyped_rowD_of_parameters 1 2 2 63 1 (-1)
        fixedChebyshevUData_1 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_1
    _ = fixedRowDData_2 := by
      rw [fixed_reversedU_typed_data_1, fixed_rowD_typed_factor_2]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow3
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_3 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (1 : ℤ)

def fixedRowPCoeff_3 (n : ℕ) : ℤ :=
    (if 61 = n then (1 : ℤ) else 0) +
    (if 62 = n then (-2 : ℤ) else 0) +
    (if 63 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_3 (n : ℕ) :
    fixedRowPData_3.coeff n = fixedRowPCoeff_3 n := by
  simp only [fixedRowPData_3, fixedRowPCoeff_3, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_3 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_3 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_3, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_3 : ∀ k : Fin 63,
    fixedReversedTCoeff_1 (k.val + 2) - 2 * fixedReversedTCoeff_1 (k.val + 1) + fixedReversedTCoeff_1 k.val = fixedRowPCoeff_3 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_3 :
    (1 - X) ^ 2 * fixedReversedTData_1 = fixedRowPData_3 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_1, fixed_rowP_typed_coeff_3]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_1, fixed_rowP_typed_coeff_3]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_1, fixed_rowP_typed_coeff_3]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_3 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_1 _ (by omega),
              fixed_reversedT_typed_tail_1 _ (by omega), fixed_reversedT_typed_tail_1 _ hn',
              fixed_rowP_typed_tail_3 _ (by omega)]
            decide

theorem fixed_rowP_typed_3 : rowP 1 3 = fixedRowPData_3 := by
  calc
    rowP 1 3 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_1 :=
      fixedTyped_rowP_of_parameters 1 3 2 63 1 fixedChebyshevTData_1
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_1
    _ = fixedRowPData_3 := by
      rw [fixed_reversedT_typed_data_1, fixed_rowP_typed_factor_3]

def fixedRowDData_3 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowDCoeff_3 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_3 (n : ℕ) :
    fixedRowDData_3.coeff n = fixedRowDCoeff_3 n := by
  simp only [fixedRowDData_3, fixedRowDCoeff_3, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_3 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_3 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_3, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_3 : ∀ k : Fin 63,
    (-1 : ℤ) * (fixedReversedUCoeff_0 (k.val + 2) - 2 * fixedReversedUCoeff_0 (k.val + 1) + fixedReversedUCoeff_0 k.val) = fixedRowDCoeff_3 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_3 :
    Polynomial.C (-1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_0 = fixedRowDData_3 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_0, fixed_rowD_typed_coeff_3]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_0, fixed_rowD_typed_coeff_3]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_0, fixed_rowD_typed_coeff_3]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_3 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_0 _ (by omega),
              fixed_reversedU_typed_tail_0 _ (by omega), fixed_reversedU_typed_tail_0 _ hn',
              fixed_rowD_typed_tail_3 _ (by omega)]
            decide

theorem fixed_rowD_typed_3 : rowD 1 3 = fixedRowDData_3 := by
  calc
    rowD 1 3 = Polynomial.C (-1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_0 :=
      fixedTyped_rowD_of_parameters 1 3 2 63 0 (-1)
        fixedChebyshevUData_0 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_0
    _ = fixedRowDData_3 := by
      rw [fixed_reversedU_typed_data_0, fixed_rowD_typed_factor_3]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow5
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_5 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (1 : ℤ)

def fixedRowPCoeff_5 (n : ℕ) : ℤ :=
    (if 61 = n then (1 : ℤ) else 0) +
    (if 62 = n then (-2 : ℤ) else 0) +
    (if 63 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_5 (n : ℕ) :
    fixedRowPData_5.coeff n = fixedRowPCoeff_5 n := by
  simp only [fixedRowPData_5, fixedRowPCoeff_5, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_5 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_5 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_5, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_5 : ∀ k : Fin 63,
    fixedReversedTCoeff_1 (k.val + 2) - 2 * fixedReversedTCoeff_1 (k.val + 1) + fixedReversedTCoeff_1 k.val = fixedRowPCoeff_5 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_5 :
    (1 - X) ^ 2 * fixedReversedTData_1 = fixedRowPData_5 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_1, fixed_rowP_typed_coeff_5]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_1, fixed_rowP_typed_coeff_5]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_1, fixed_rowP_typed_coeff_5]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_5 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_1 _ (by omega),
              fixed_reversedT_typed_tail_1 _ (by omega), fixed_reversedT_typed_tail_1 _ hn',
              fixed_rowP_typed_tail_5 _ (by omega)]
            decide

theorem fixed_rowP_typed_5 : rowP 1 5 = fixedRowPData_5 := by
  calc
    rowP 1 5 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_1 :=
      fixedTyped_rowP_of_parameters 1 5 2 63 1 fixedChebyshevTData_1
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_1
    _ = fixedRowPData_5 := by
      rw [fixed_reversedT_typed_data_1, fixed_rowP_typed_factor_5]

def fixedRowDData_5 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowDCoeff_5 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_5 (n : ℕ) :
    fixedRowDData_5.coeff n = fixedRowDCoeff_5 n := by
  simp only [fixedRowDData_5, fixedRowDCoeff_5, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_5 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_5 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_5, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_5 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_0 (k.val + 2) - 2 * fixedReversedUCoeff_0 (k.val + 1) + fixedReversedUCoeff_0 k.val) = fixedRowDCoeff_5 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_5 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_0 = fixedRowDData_5 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_0, fixed_rowD_typed_coeff_5]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_0, fixed_rowD_typed_coeff_5]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_0, fixed_rowD_typed_coeff_5]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_5 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_0 _ (by omega),
              fixed_reversedU_typed_tail_0 _ (by omega), fixed_reversedU_typed_tail_0 _ hn',
              fixed_rowD_typed_tail_5 _ (by omega)]
            decide

theorem fixed_rowD_typed_5 : rowD 1 5 = fixedRowDData_5 := by
  calc
    rowD 1 5 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_0 :=
      fixedTyped_rowD_of_parameters 1 5 2 63 0 (1)
        fixedChebyshevUData_0 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_0
    _ = fixedRowDData_5 := by
      rw [fixed_reversedU_typed_data_0, fixed_rowD_typed_factor_5]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow6
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_6 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 60 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-4 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowPCoeff_6 (n : ℕ) : ℤ :=
    (if 60 = n then (2 : ℤ) else 0) +
    (if 61 = n then (-4 : ℤ) else 0) +
    (if 62 = n then (1 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_6 (n : ℕ) :
    fixedRowPData_6.coeff n = fixedRowPCoeff_6 n := by
  simp only [fixedRowPData_6, fixedRowPCoeff_6, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_6 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_6 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_6, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_6 : ∀ k : Fin 63,
    fixedReversedTCoeff_2 (k.val + 2) - 2 * fixedReversedTCoeff_2 (k.val + 1) + fixedReversedTCoeff_2 k.val = fixedRowPCoeff_6 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_6 :
    (1 - X) ^ 2 * fixedReversedTData_2 = fixedRowPData_6 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_2, fixed_rowP_typed_coeff_6]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_2, fixed_rowP_typed_coeff_6]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_2, fixed_rowP_typed_coeff_6]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_6 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_2 _ (by omega),
              fixed_reversedT_typed_tail_2 _ (by omega), fixed_reversedT_typed_tail_2 _ hn',
              fixed_rowP_typed_tail_6 _ (by omega)]
            decide

theorem fixed_rowP_typed_6 : rowP 1 6 = fixedRowPData_6 := by
  calc
    rowP 1 6 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_2 :=
      fixedTyped_rowP_of_parameters 1 6 2 63 2 fixedChebyshevTData_2
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_2
    _ = fixedRowPData_6 := by
      rw [fixed_reversedT_typed_data_2, fixed_rowP_typed_factor_6]

def fixedRowDData_6 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-4 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ)

def fixedRowDCoeff_6 (n : ℕ) : ℤ :=
    (if 61 = n then (2 : ℤ) else 0) +
    (if 62 = n then (-4 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_6 (n : ℕ) :
    fixedRowDData_6.coeff n = fixedRowDCoeff_6 n := by
  simp only [fixedRowDData_6, fixedRowDCoeff_6, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_6 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_6 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_6, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_6 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_1 (k.val + 2) - 2 * fixedReversedUCoeff_1 (k.val + 1) + fixedReversedUCoeff_1 k.val) = fixedRowDCoeff_6 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_6 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_1 = fixedRowDData_6 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_1, fixed_rowD_typed_coeff_6]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_1, fixed_rowD_typed_coeff_6]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_1, fixed_rowD_typed_coeff_6]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_6 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_1 _ (by omega),
              fixed_reversedU_typed_tail_1 _ (by omega), fixed_reversedU_typed_tail_1 _ hn',
              fixed_rowD_typed_tail_6 _ (by omega)]
            decide

theorem fixed_rowD_typed_6 : rowD 1 6 = fixedRowDData_6 := by
  calc
    rowD 1 6 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_1 :=
      fixedTyped_rowD_of_parameters 1 6 2 63 1 (1)
        fixedChebyshevUData_1 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_1
    _ = fixedRowDData_6 := by
      rw [fixed_reversedU_typed_data_1, fixed_rowD_typed_factor_6]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow7
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_7 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 59 (4 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-8 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (6 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-3 : ℤ)

def fixedRowPCoeff_7 (n : ℕ) : ℤ :=
    (if 59 = n then (4 : ℤ) else 0) +
    (if 60 = n then (-8 : ℤ) else 0) +
    (if 61 = n then (1 : ℤ) else 0) +
    (if 62 = n then (6 : ℤ) else 0) +
    (if 63 = n then (-3 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_7 (n : ℕ) :
    fixedRowPData_7.coeff n = fixedRowPCoeff_7 n := by
  simp only [fixedRowPData_7, fixedRowPCoeff_7, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_7 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_7 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_7, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_7 : ∀ k : Fin 63,
    fixedReversedTCoeff_3 (k.val + 2) - 2 * fixedReversedTCoeff_3 (k.val + 1) + fixedReversedTCoeff_3 k.val = fixedRowPCoeff_7 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_7 :
    (1 - X) ^ 2 * fixedReversedTData_3 = fixedRowPData_7 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_3, fixed_rowP_typed_coeff_7]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_3, fixed_rowP_typed_coeff_7]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_3, fixed_rowP_typed_coeff_7]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_7 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_3 _ (by omega),
              fixed_reversedT_typed_tail_3 _ (by omega), fixed_reversedT_typed_tail_3 _ hn',
              fixed_rowP_typed_tail_7 _ (by omega)]
            decide

theorem fixed_rowP_typed_7 : rowP 1 7 = fixedRowPData_7 := by
  calc
    rowP 1 7 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_3 :=
      fixedTyped_rowP_of_parameters 1 7 2 63 3 fixedChebyshevTData_3
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_3
    _ = fixedRowPData_7 := by
      rw [fixed_reversedT_typed_data_3, fixed_rowP_typed_factor_7]

def fixedRowDData_7 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 60 (4 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-8 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (3 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowDCoeff_7 (n : ℕ) : ℤ :=
    (if 60 = n then (4 : ℤ) else 0) +
    (if 61 = n then (-8 : ℤ) else 0) +
    (if 62 = n then (3 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_7 (n : ℕ) :
    fixedRowDData_7.coeff n = fixedRowDCoeff_7 n := by
  simp only [fixedRowDData_7, fixedRowDCoeff_7, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_7 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_7 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_7, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_7 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_2 (k.val + 2) - 2 * fixedReversedUCoeff_2 (k.val + 1) + fixedReversedUCoeff_2 k.val) = fixedRowDCoeff_7 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_7 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_2 = fixedRowDData_7 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_2, fixed_rowD_typed_coeff_7]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_2, fixed_rowD_typed_coeff_7]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_2, fixed_rowD_typed_coeff_7]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_7 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_2 _ (by omega),
              fixed_reversedU_typed_tail_2 _ (by omega), fixed_reversedU_typed_tail_2 _ hn',
              fixed_rowD_typed_tail_7 _ (by omega)]
            decide

theorem fixed_rowD_typed_7 : rowD 1 7 = fixedRowDData_7 := by
  calc
    rowD 1 7 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_2 :=
      fixedTyped_rowD_of_parameters 1 7 2 63 2 (1)
        fixedChebyshevUData_2 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_2
    _ = fixedRowDData_7 := by
      rw [fixed_reversedU_typed_data_2, fixed_rowD_typed_factor_7]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow8
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_8 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 58 (8 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-16 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (16 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-7 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_8 (n : ℕ) : ℤ :=
    (if 58 = n then (8 : ℤ) else 0) +
    (if 59 = n then (-16 : ℤ) else 0) +
    (if 61 = n then (16 : ℤ) else 0) +
    (if 62 = n then (-7 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_8 (n : ℕ) :
    fixedRowPData_8.coeff n = fixedRowPCoeff_8 n := by
  simp only [fixedRowPData_8, fixedRowPCoeff_8, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_8 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_8 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_8, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_8 : ∀ k : Fin 63,
    fixedReversedTCoeff_4 (k.val + 2) - 2 * fixedReversedTCoeff_4 (k.val + 1) + fixedReversedTCoeff_4 k.val = fixedRowPCoeff_8 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_8 :
    (1 - X) ^ 2 * fixedReversedTData_4 = fixedRowPData_8 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_4, fixed_rowP_typed_coeff_8]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_4, fixed_rowP_typed_coeff_8]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_4, fixed_rowP_typed_coeff_8]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_8 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_4 _ (by omega),
              fixed_reversedT_typed_tail_4 _ (by omega), fixed_reversedT_typed_tail_4 _ hn',
              fixed_rowP_typed_tail_8 _ (by omega)]
            decide

theorem fixed_rowP_typed_8 : rowP 1 8 = fixedRowPData_8 := by
  calc
    rowP 1 8 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_4 :=
      fixedTyped_rowP_of_parameters 1 8 2 63 4 fixedChebyshevTData_4
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_4
    _ = fixedRowPData_8 := by
      rw [fixed_reversedT_typed_data_4, fixed_rowP_typed_factor_8]

def fixedRowDData_8 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 59 (8 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-16 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (4 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (8 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-4 : ℤ)

def fixedRowDCoeff_8 (n : ℕ) : ℤ :=
    (if 59 = n then (8 : ℤ) else 0) +
    (if 60 = n then (-16 : ℤ) else 0) +
    (if 61 = n then (4 : ℤ) else 0) +
    (if 62 = n then (8 : ℤ) else 0) +
    (if 63 = n then (-4 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_8 (n : ℕ) :
    fixedRowDData_8.coeff n = fixedRowDCoeff_8 n := by
  simp only [fixedRowDData_8, fixedRowDCoeff_8, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_8 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_8 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_8, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_8 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_3 (k.val + 2) - 2 * fixedReversedUCoeff_3 (k.val + 1) + fixedReversedUCoeff_3 k.val) = fixedRowDCoeff_8 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_8 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_3 = fixedRowDData_8 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_3, fixed_rowD_typed_coeff_8]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_3, fixed_rowD_typed_coeff_8]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_3, fixed_rowD_typed_coeff_8]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_8 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_3 _ (by omega),
              fixed_reversedU_typed_tail_3 _ (by omega), fixed_reversedU_typed_tail_3 _ hn',
              fixed_rowD_typed_tail_8 _ (by omega)]
            decide

theorem fixed_rowD_typed_8 : rowD 1 8 = fixedRowDData_8 := by
  calc
    rowD 1 8 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_3 :=
      fixedTyped_rowD_of_parameters 1 8 2 63 3 (1)
        fixedChebyshevUData_3 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_3
    _ = fixedRowDData_8 := by
      rw [fixed_reversedU_typed_data_3, fixed_rowD_typed_factor_8]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow9
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_9 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 57 (16 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-32 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-4 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (40 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-15 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-10 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (5 : ℤ)

def fixedRowPCoeff_9 (n : ℕ) : ℤ :=
    (if 57 = n then (16 : ℤ) else 0) +
    (if 58 = n then (-32 : ℤ) else 0) +
    (if 59 = n then (-4 : ℤ) else 0) +
    (if 60 = n then (40 : ℤ) else 0) +
    (if 61 = n then (-15 : ℤ) else 0) +
    (if 62 = n then (-10 : ℤ) else 0) +
    (if 63 = n then (5 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_9 (n : ℕ) :
    fixedRowPData_9.coeff n = fixedRowPCoeff_9 n := by
  simp only [fixedRowPData_9, fixedRowPCoeff_9, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_9 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_9 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_9, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_9 : ∀ k : Fin 63,
    fixedReversedTCoeff_5 (k.val + 2) - 2 * fixedReversedTCoeff_5 (k.val + 1) + fixedReversedTCoeff_5 k.val = fixedRowPCoeff_9 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_9 :
    (1 - X) ^ 2 * fixedReversedTData_5 = fixedRowPData_9 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_5, fixed_rowP_typed_coeff_9]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_5, fixed_rowP_typed_coeff_9]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_5, fixed_rowP_typed_coeff_9]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_9 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_5 _ (by omega),
              fixed_reversedT_typed_tail_5 _ (by omega), fixed_reversedT_typed_tail_5 _ hn',
              fixed_rowP_typed_tail_9 _ (by omega)]
            decide

theorem fixed_rowP_typed_9 : rowP 1 9 = fixedRowPData_9 := by
  calc
    rowP 1 9 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_5 :=
      fixedTyped_rowP_of_parameters 1 9 2 63 5 fixedChebyshevTData_5
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_5
    _ = fixedRowPData_9 := by
      rw [fixed_reversedT_typed_data_5, fixed_rowP_typed_factor_9]

def fixedRowDData_9 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 58 (16 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-32 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (4 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (24 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-11 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowDCoeff_9 (n : ℕ) : ℤ :=
    (if 58 = n then (16 : ℤ) else 0) +
    (if 59 = n then (-32 : ℤ) else 0) +
    (if 60 = n then (4 : ℤ) else 0) +
    (if 61 = n then (24 : ℤ) else 0) +
    (if 62 = n then (-11 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_9 (n : ℕ) :
    fixedRowDData_9.coeff n = fixedRowDCoeff_9 n := by
  simp only [fixedRowDData_9, fixedRowDCoeff_9, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_9 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_9 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_9, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_9 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_4 (k.val + 2) - 2 * fixedReversedUCoeff_4 (k.val + 1) + fixedReversedUCoeff_4 k.val) = fixedRowDCoeff_9 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_9 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_4 = fixedRowDData_9 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_4, fixed_rowD_typed_coeff_9]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_4, fixed_rowD_typed_coeff_9]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_4, fixed_rowD_typed_coeff_9]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_9 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_4 _ (by omega),
              fixed_reversedU_typed_tail_4 _ (by omega), fixed_reversedU_typed_tail_4 _ hn',
              fixed_rowD_typed_tail_9 _ (by omega)]
            decide

theorem fixed_rowD_typed_9 : rowD 1 9 = fixedRowDData_9 := by
  calc
    rowD 1 9 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_4 :=
      fixedTyped_rowD_of_parameters 1 9 2 63 4 (1)
        fixedChebyshevUData_4 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_4
    _ = fixedRowDData_9 := by
      rw [fixed_reversedU_typed_data_4, fixed_rowD_typed_factor_9]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRowsAll
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_4 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_4 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_4 (n : ℕ) :
    fixedRowPData_4.coeff n = fixedRowPCoeff_4 n := by
  simp only [fixedRowPData_4, fixedRowPCoeff_4, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_4 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_4 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_4, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_4 : ∀ k : Fin 63,
    fixedReversedTCoeff_0 (k.val + 2) - 2 * fixedReversedTCoeff_0 (k.val + 1) + fixedReversedTCoeff_0 k.val = fixedRowPCoeff_4 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_4 :
    (1 - X) ^ 2 * fixedReversedTData_0 = fixedRowPData_4 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_0, fixed_rowP_typed_coeff_4]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_0, fixed_rowP_typed_coeff_4]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_0, fixed_rowP_typed_coeff_4]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_4 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_0 _ (by omega),
              fixed_reversedT_typed_tail_0 _ (by omega), fixed_reversedT_typed_tail_0 _ hn',
              fixed_rowP_typed_tail_4 _ (by omega)]
            decide

theorem fixed_rowP_typed_4 : rowP 1 4 = fixedRowPData_4 := by
  calc
    rowP 1 4 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_0 :=
      fixedTyped_rowP_of_parameters 1 4 2 63 0 fixedChebyshevTData_0
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_0
    _ = fixedRowPData_4 := by
      rw [fixed_reversedT_typed_data_0, fixed_rowP_typed_factor_4]

def fixedRowDData_4 : ℤ[X] :=
    0

def fixedRowDCoeff_4 (_n : ℕ) : ℤ :=
    0

theorem fixed_rowD_typed_coeff_4 (n : ℕ) :
    fixedRowDData_4.coeff n = fixedRowDCoeff_4 n := by
  simp only [fixedRowDData_4, fixedRowDCoeff_4, coeff_zero]


theorem fixed_rowD_typed_4 : rowD 1 4 = fixedRowDData_4 := by
  apply rowD_eq_zero_of_distance_zero
  decide

end InternalCatalan

end

end

section

noncomputable section
open Polynomial
namespace InternalCatalan















end InternalCatalan

end

end

section

noncomputable section
open Polynomial
namespace InternalCatalan















end InternalCatalan

end

end

section



end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.PalindromicBlockInverse
namespace OAI


noncomputable section

open Polynomial
open scoped BigOperators

namespace InternalCatalan





@[simp] theorem fixedMatrix_zero : fixedMatrix 0 = fixedB0 := by simp [fixedMatrix]
@[simp] theorem fixedMatrix_one : fixedMatrix 1 = fixedB0 + fixedB1 := by
  simp [fixedMatrix]
@[simp] theorem fixedMatrix_neg_one : fixedMatrix (-1) = fixedB0 - fixedB1 := by
  simp [fixedMatrix, sub_eq_add_neg]




end InternalCatalan

end



noncomputable section
open scoped BigOperators
namespace InternalCatalan




end InternalCatalan

end



noncomputable section

namespace InternalCatalan



















open scoped BigOperators


























end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Matrix
open scoped Kronecker













end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open Matrix
open scoped Kronecker








end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Split.IntBaseRows0
namespace OAI

namespace InternalCatalan

theorem splitBaseMod_row_0 (k : Fin 48) :
    (fixedIntegerBaseCanonical (0 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (0 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (0 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_0 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_0 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 0).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 0).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_0, fixed_rowD_typed_0]
    simp only [fixed_rowP_typed_coeff_0, fixed_rowD_typed_coeff_0,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_1 (k : Fin 48) :
    (fixedIntegerBaseCanonical (1 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (1 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (1 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_1 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_1 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 1).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 1).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_1, fixed_rowD_typed_1]
    simp only [fixed_rowP_typed_coeff_1, fixed_rowD_typed_coeff_1,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_2 (k : Fin 48) :
    (fixedIntegerBaseCanonical (2 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (2 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (2 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_2 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_2 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 2).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 2).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_2, fixed_rowD_typed_2]
    simp only [fixed_rowP_typed_coeff_2, fixed_rowD_typed_coeff_2,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_3 (k : Fin 48) :
    (fixedIntegerBaseCanonical (3 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (3 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (3 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_3 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_3 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 3).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 3).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_3, fixed_rowD_typed_3]
    simp only [fixed_rowP_typed_coeff_3, fixed_rowD_typed_coeff_3,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_4 (k : Fin 48) :
    (fixedIntegerBaseCanonical (4 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (4 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (4 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_4 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_4 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 4).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 4).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_4, fixed_rowD_typed_4]
    simp only [fixed_rowP_typed_coeff_4, fixed_rowD_typed_coeff_4,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_5 (k : Fin 48) :
    (fixedIntegerBaseCanonical (5 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (5 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (5 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_5 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_5 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 5).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 5).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_5, fixed_rowD_typed_5]
    simp only [fixed_rowP_typed_coeff_5, fixed_rowD_typed_coeff_5,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_6 (k : Fin 48) :
    (fixedIntegerBaseCanonical (6 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (6 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (6 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_6 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_6 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 6).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 6).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_6, fixed_rowD_typed_6]
    simp only [fixed_rowP_typed_coeff_6, fixed_rowD_typed_coeff_6,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_7 (k : Fin 48) :
    (fixedIntegerBaseCanonical (7 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (7 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (7 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_7 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_7 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 7).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 7).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_7, fixed_rowD_typed_7]
    simp only [fixed_rowP_typed_coeff_7, fixed_rowD_typed_coeff_7,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_8 (k : Fin 48) :
    (fixedIntegerBaseCanonical (8 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (8 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (8 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_8 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_8 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 8).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 8).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_8, fixed_rowD_typed_8]
    simp only [fixed_rowP_typed_coeff_8, fixed_rowD_typed_coeff_8,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_9 (k : Fin 48) :
    (fixedIntegerBaseCanonical (9 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (9 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (9 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_9 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_9 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 9).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 9).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_9, fixed_rowD_typed_9]
    simp only [fixed_rowP_typed_coeff_9, fixed_rowD_typed_coeff_9,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_10 (k : Fin 48) :
    (fixedIntegerBaseCanonical (10 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (10 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (10 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_10 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_10 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 10).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 10).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_10, fixed_rowD_typed_10]
    simp only [fixed_rowP_typed_coeff_10, fixed_rowD_typed_coeff_10,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_11 (k : Fin 48) :
    (fixedIntegerBaseCanonical (11 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (11 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (11 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_11 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_11 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 11).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 11).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_11, fixed_rowD_typed_11]
    simp only [fixed_rowP_typed_coeff_11, fixed_rowD_typed_coeff_11,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem fixedIntegerBaseCanonical_mod101_rows_0_11 (r : Fin 49) (hr : 0 ≤ r.val ∧ r.val < 12)
    (k : Fin 48) :
    (fixedIntegerBaseCanonical r k : ZMod 101) = fixedLiteralBaseMod r k := by
  obtain ⟨r, hr'⟩ := r
  obtain ⟨hra, hrb⟩ := hr
  simp only at hra hrb
  interval_cases r
  · exact splitBaseMod_row_0 k
  · exact splitBaseMod_row_1 k
  · exact splitBaseMod_row_2 k
  · exact splitBaseMod_row_3 k
  · exact splitBaseMod_row_4 k
  · exact splitBaseMod_row_5 k
  · exact splitBaseMod_row_6 k
  · exact splitBaseMod_row_7 k
  · exact splitBaseMod_row_8 k
  · exact splitBaseMod_row_9 k
  · exact splitBaseMod_row_10 k
  · exact splitBaseMod_row_11 k

end InternalCatalan

end OAI

end

section
open OAI.InternalCatalan

theorem solution (r : Fin 49) (hr : 0 ≤ r.val ∧ r.val < 12)
    (k : Fin 48) :
    (fixedIntegerBaseCanonical r k : ZMod 101) = fixedLiteralBaseMod r k := by
  first
  | exact @OAI.InternalCatalan.fixedIntegerBaseCanonical_mod101_rows_0_11
  | (apply OAI.InternalCatalan.fixedIntegerBaseCanonical_mod101_rows_0_11 <;> assumption)

end
