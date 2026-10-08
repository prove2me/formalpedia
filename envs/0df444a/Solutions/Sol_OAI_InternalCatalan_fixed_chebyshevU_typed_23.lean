-- Prove2me | solution 1 for OAI.InternalCatalan.fixed_chebyshevU_typed_23
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T22:05:40.517995+00:00
-- url     : https://prove2.me/submissions/508f5d57-3328-49be-8974-88a044741651

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_OAICatalanIrrationality
import Definitions.Def_OAICatalanChebyshevData
import Theorems.Thm_OAI_InternalCatalan_fixed_chebyshevU_typed_22

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

def fixedChebyshevUData_7 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-8 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (80 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-192 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (128 : ℤ)

def fixedChebyshevUData_8 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-40 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (240 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-448 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (256 : ℤ)

def fixedChebyshevUData_9 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (10 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-160 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (672 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-1024 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (512 : ℤ)

def fixedChebyshevUData_10 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (60 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-560 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (1792 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-2304 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (1024 : ℤ)

def fixedChebyshevUData_11 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-12 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (280 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-1792 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (4608 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-5120 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (2048 : ℤ)

def fixedChebyshevUData_12 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-84 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (1120 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-5376 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (11520 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-11264 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (4096 : ℤ)

def fixedChebyshevUData_13 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (14 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-448 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (4032 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-15360 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (28160 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (-24576 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (8192 : ℤ)

def fixedChebyshevUData_14 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (112 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-2016 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (13440 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-42240 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (67584 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (-53248 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (16384 : ℤ)

def fixedChebyshevUData_15 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-16 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (672 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-8064 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (42240 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-112640 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (159744 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (-114688 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (32768 : ℤ)

def fixedChebyshevUData_16 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-144 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (3360 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-29568 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (126720 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-292864 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (372736 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (-245760 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (65536 : ℤ)

def fixedChebyshevUData_17 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (18 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-960 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (14784 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-101376 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (366080 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (-745472 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (860160 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (-524288 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (131072 : ℤ)

def fixedChebyshevUData_18 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (180 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-5280 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (59136 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-329472 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (1025024 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (-1863680 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (1966080 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (-1114112 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (262144 : ℤ)

def fixedChebyshevUData_19 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-20 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (1320 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-25344 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (219648 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-1025024 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (2795520 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (-4587520 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (4456448 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (-2359296 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (524288 : ℤ)

def fixedChebyshevUData_20 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-220 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (7920 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-109824 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (768768 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-3075072 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (7454720 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (-11141120 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (10027008 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (-4980736 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (1048576 : ℤ)

def fixedChebyshevUData_21 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (22 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-1760 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (41184 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-439296 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (2562560 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (-8945664 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (19496960 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (-26738688 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (22413312 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (-10485760 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (2097152 : ℤ)























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

theorem fixed_chebyshevU_typed_7 :
    Chebyshev.U ℤ 7 = fixedChebyshevUData_7 := by
  calc
    Chebyshev.U ℤ 7 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 6 - Chebyshev.U ℤ 5 :=
      Chebyshev.U_add_two ℤ 5
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_6 - fixedChebyshevUData_5 := by
      rw [fixed_chebyshevU_typed_6, fixed_chebyshevU_typed_5]
    _ = fixedChebyshevUData_7 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_6, fixedChebyshevUData_5, fixedChebyshevUData_7, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_6, fixedChebyshevUData_5, fixedChebyshevUData_7, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 7
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 7, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 7 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_8 :
    Chebyshev.U ℤ 8 = fixedChebyshevUData_8 := by
  calc
    Chebyshev.U ℤ 8 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 7 - Chebyshev.U ℤ 6 :=
      Chebyshev.U_add_two ℤ 6
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_7 - fixedChebyshevUData_6 := by
      rw [fixed_chebyshevU_typed_7, fixed_chebyshevU_typed_6]
    _ = fixedChebyshevUData_8 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_7, fixedChebyshevUData_6, fixedChebyshevUData_8, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_7, fixedChebyshevUData_6, fixedChebyshevUData_8, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 8
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 8, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 8 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_9 :
    Chebyshev.U ℤ 9 = fixedChebyshevUData_9 := by
  calc
    Chebyshev.U ℤ 9 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 8 - Chebyshev.U ℤ 7 :=
      Chebyshev.U_add_two ℤ 7
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_8 - fixedChebyshevUData_7 := by
      rw [fixed_chebyshevU_typed_8, fixed_chebyshevU_typed_7]
    _ = fixedChebyshevUData_9 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_8, fixedChebyshevUData_7, fixedChebyshevUData_9, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_8, fixedChebyshevUData_7, fixedChebyshevUData_9, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 9
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 9, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 9 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_10 :
    Chebyshev.U ℤ 10 = fixedChebyshevUData_10 := by
  calc
    Chebyshev.U ℤ 10 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 9 - Chebyshev.U ℤ 8 :=
      Chebyshev.U_add_two ℤ 8
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_9 - fixedChebyshevUData_8 := by
      rw [fixed_chebyshevU_typed_9, fixed_chebyshevU_typed_8]
    _ = fixedChebyshevUData_10 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_9, fixedChebyshevUData_8, fixedChebyshevUData_10, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_9, fixedChebyshevUData_8, fixedChebyshevUData_10, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 10
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 10, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 10 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevU_typed_11 :
    Chebyshev.U ℤ 11 = fixedChebyshevUData_11 := by
  calc
    Chebyshev.U ℤ 11 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 10 - Chebyshev.U ℤ 9 :=
      Chebyshev.U_add_two ℤ 9
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_10 - fixedChebyshevUData_9 := by
      rw [fixed_chebyshevU_typed_10, fixed_chebyshevU_typed_9]
    _ = fixedChebyshevUData_11 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_10, fixedChebyshevUData_9, fixedChebyshevUData_11, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_10, fixedChebyshevUData_9, fixedChebyshevUData_11, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 11
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 11, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 11 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_12 :
    Chebyshev.U ℤ 12 = fixedChebyshevUData_12 := by
  calc
    Chebyshev.U ℤ 12 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 11 - Chebyshev.U ℤ 10 :=
      Chebyshev.U_add_two ℤ 10
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_11 - fixedChebyshevUData_10 := by
      rw [fixed_chebyshevU_typed_11, fixed_chebyshevU_typed_10]
    _ = fixedChebyshevUData_12 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_11, fixedChebyshevUData_10, fixedChebyshevUData_12, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_11, fixedChebyshevUData_10, fixedChebyshevUData_12, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 12
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 12, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 12 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_13 :
    Chebyshev.U ℤ 13 = fixedChebyshevUData_13 := by
  calc
    Chebyshev.U ℤ 13 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 12 - Chebyshev.U ℤ 11 :=
      Chebyshev.U_add_two ℤ 11
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_12 - fixedChebyshevUData_11 := by
      rw [fixed_chebyshevU_typed_12, fixed_chebyshevU_typed_11]
    _ = fixedChebyshevUData_13 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_12, fixedChebyshevUData_11, fixedChebyshevUData_13, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_12, fixedChebyshevUData_11, fixedChebyshevUData_13, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 13
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 13, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 13 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_14 :
    Chebyshev.U ℤ 14 = fixedChebyshevUData_14 := by
  calc
    Chebyshev.U ℤ 14 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 13 - Chebyshev.U ℤ 12 :=
      Chebyshev.U_add_two ℤ 12
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_13 - fixedChebyshevUData_12 := by
      rw [fixed_chebyshevU_typed_13, fixed_chebyshevU_typed_12]
    _ = fixedChebyshevUData_14 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_13, fixedChebyshevUData_12, fixedChebyshevUData_14, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_13, fixedChebyshevUData_12, fixedChebyshevUData_14, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 14
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 14, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 14 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_15 :
    Chebyshev.U ℤ 15 = fixedChebyshevUData_15 := by
  calc
    Chebyshev.U ℤ 15 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 14 - Chebyshev.U ℤ 13 :=
      Chebyshev.U_add_two ℤ 13
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_14 - fixedChebyshevUData_13 := by
      rw [fixed_chebyshevU_typed_14, fixed_chebyshevU_typed_13]
    _ = fixedChebyshevUData_15 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_14, fixedChebyshevUData_13, fixedChebyshevUData_15, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_14, fixedChebyshevUData_13, fixedChebyshevUData_15, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 15
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 15, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 15 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_16 :
    Chebyshev.U ℤ 16 = fixedChebyshevUData_16 := by
  calc
    Chebyshev.U ℤ 16 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 15 - Chebyshev.U ℤ 14 :=
      Chebyshev.U_add_two ℤ 14
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_15 - fixedChebyshevUData_14 := by
      rw [fixed_chebyshevU_typed_15, fixed_chebyshevU_typed_14]
    _ = fixedChebyshevUData_16 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_15, fixedChebyshevUData_14, fixedChebyshevUData_16, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_15, fixedChebyshevUData_14, fixedChebyshevUData_16, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 16
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 16, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 16 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_17 :
    Chebyshev.U ℤ 17 = fixedChebyshevUData_17 := by
  calc
    Chebyshev.U ℤ 17 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 16 - Chebyshev.U ℤ 15 :=
      Chebyshev.U_add_two ℤ 15
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_16 - fixedChebyshevUData_15 := by
      rw [fixed_chebyshevU_typed_16, fixed_chebyshevU_typed_15]
    _ = fixedChebyshevUData_17 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_16, fixedChebyshevUData_15, fixedChebyshevUData_17, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_16, fixedChebyshevUData_15, fixedChebyshevUData_17, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 17
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 17, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 17 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevU_typed_18 :
    Chebyshev.U ℤ 18 = fixedChebyshevUData_18 := by
  calc
    Chebyshev.U ℤ 18 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 17 - Chebyshev.U ℤ 16 :=
      Chebyshev.U_add_two ℤ 16
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_17 - fixedChebyshevUData_16 := by
      rw [fixed_chebyshevU_typed_17, fixed_chebyshevU_typed_16]
    _ = fixedChebyshevUData_18 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_17, fixedChebyshevUData_16, fixedChebyshevUData_18, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_17, fixedChebyshevUData_16, fixedChebyshevUData_18, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 18
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 18, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 18 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_19 :
    Chebyshev.U ℤ 19 = fixedChebyshevUData_19 := by
  calc
    Chebyshev.U ℤ 19 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 18 - Chebyshev.U ℤ 17 :=
      Chebyshev.U_add_two ℤ 17
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_18 - fixedChebyshevUData_17 := by
      rw [fixed_chebyshevU_typed_18, fixed_chebyshevU_typed_17]
    _ = fixedChebyshevUData_19 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_18, fixedChebyshevUData_17, fixedChebyshevUData_19, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_18, fixedChebyshevUData_17, fixedChebyshevUData_19, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 19
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 19, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 19 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_20 :
    Chebyshev.U ℤ 20 = fixedChebyshevUData_20 := by
  calc
    Chebyshev.U ℤ 20 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 19 - Chebyshev.U ℤ 18 :=
      Chebyshev.U_add_two ℤ 18
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_19 - fixedChebyshevUData_18 := by
      rw [fixed_chebyshevU_typed_19, fixed_chebyshevU_typed_18]
    _ = fixedChebyshevUData_20 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_19, fixedChebyshevUData_18, fixedChebyshevUData_20, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_19, fixedChebyshevUData_18, fixedChebyshevUData_20, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 20
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 20, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 20 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevU_typed_21 :
    Chebyshev.U ℤ 21 = fixedChebyshevUData_21 := by
  calc
    Chebyshev.U ℤ 21 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 20 - Chebyshev.U ℤ 19 :=
      Chebyshev.U_add_two ℤ 19
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_20 - fixedChebyshevUData_19 := by
      rw [fixed_chebyshevU_typed_20, fixed_chebyshevU_typed_19]
    _ = fixedChebyshevUData_21 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_20, fixedChebyshevUData_19, fixedChebyshevUData_21, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_20, fixedChebyshevUData_19, fixedChebyshevUData_21, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 21
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 21, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 21 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]


theorem fixed_chebyshevU_typed_23 :
    Chebyshev.U ℤ 23 = fixedChebyshevUData_23 := by
  calc
    Chebyshev.U ℤ 23 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 22 - Chebyshev.U ℤ 21 :=
      Chebyshev.U_add_two ℤ 21
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_22 - fixedChebyshevUData_21 := by
      rw [fixed_chebyshevU_typed_22, fixed_chebyshevU_typed_21]
    _ = fixedChebyshevUData_23 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_22, fixedChebyshevUData_21, fixedChebyshevUData_23, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_22, fixedChebyshevUData_21, fixedChebyshevUData_23, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 23
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 23, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 23 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

end InternalCatalan

end

end OAI

end

section
open OAI.InternalCatalan
open Polynomial

theorem solution :
    Chebyshev.U ℤ 23 = fixedChebyshevUData_23 := by
  first
  | exact @OAI.InternalCatalan.fixed_chebyshevU_typed_23
  | (apply OAI.InternalCatalan.fixed_chebyshevU_typed_23 <;> assumption)

end
