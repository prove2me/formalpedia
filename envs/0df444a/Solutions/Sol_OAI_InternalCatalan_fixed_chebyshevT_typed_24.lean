-- Prove2me | solution 1 for OAI.InternalCatalan.fixed_chebyshevT_typed_24
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T22:02:01.729996+00:00
-- url     : https://prove2.me/submissions/eaec1f43-af19-462c-818b-2480e5a56796

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
import Theorems.Thm_OAI_InternalCatalan_fixed_chebyshevT_typed_23

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

def fixedChebyshevTData_8 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-32 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (160 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-256 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (128 : ℤ)

def fixedChebyshevTData_9 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (9 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-120 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (432 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-576 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (256 : ℤ)

def fixedChebyshevTData_10 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (50 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-400 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (1120 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-1280 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (512 : ℤ)

def fixedChebyshevTData_11 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-11 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (220 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-1232 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (2816 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-2816 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (1024 : ℤ)

def fixedChebyshevTData_12 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-72 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (840 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-3584 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (6912 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-6144 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (2048 : ℤ)

def fixedChebyshevTData_13 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (13 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-364 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (2912 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-9984 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (16640 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (-13312 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (4096 : ℤ)

def fixedChebyshevTData_14 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (98 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-1568 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (9408 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-26880 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (39424 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (-28672 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (8192 : ℤ)

def fixedChebyshevTData_15 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-15 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (560 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-6048 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (28800 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-70400 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (92160 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (-61440 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (16384 : ℤ)

def fixedChebyshevTData_16 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-128 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (2688 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-21504 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (84480 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-180224 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (212992 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (-131072 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (32768 : ℤ)

def fixedChebyshevTData_17 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (17 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-816 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (11424 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-71808 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (239360 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (-452608 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (487424 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (-278528 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (65536 : ℤ)

def fixedChebyshevTData_18 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (162 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-4320 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (44352 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-228096 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (658944 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (-1118208 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (1105920 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (-589824 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (131072 : ℤ)

def fixedChebyshevTData_19 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-19 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (1140 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-20064 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (160512 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-695552 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (1770496 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (-2723840 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (2490368 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (-1245184 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (262144 : ℤ)

def fixedChebyshevTData_20 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-200 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (6600 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-84480 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (549120 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-2050048 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (4659200 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (-6553600 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (5570560 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (-2621440 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (524288 : ℤ)

def fixedChebyshevTData_21 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (21 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-1540 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (33264 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-329472 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (1793792 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (-5870592 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (12042240 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (-15597568 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (12386304 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (-5505024 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (1048576 : ℤ)

def fixedChebyshevTData_22 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (242 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-9680 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (151008 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-1208064 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (5637632 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (-16400384 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (30638080 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (-36765696 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (27394048 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (-11534336 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (2097152 : ℤ)























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

theorem fixedTyped_chebyshevT_link (a b c : ℤ) (P Q : ℤ[X])
    (hba : b = a + 1) (hca : c = a + 2)
    (hP : Chebyshev.T ℤ a = P) (hQ : Chebyshev.T ℤ b = Q) :
    Chebyshev.T ℤ c = (2 : ℤ[X]) * X * Q - P := by
  rw [hca, Chebyshev.T_add_two, ← hba, hP, hQ]


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

theorem fixed_chebyshevT_typed_8 :
    Chebyshev.T ℤ 8 = fixedChebyshevTData_8 := by
  calc
    Chebyshev.T ℤ 8 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 7 - Chebyshev.T ℤ 6 :=
      Chebyshev.T_add_two ℤ 6
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_7 - fixedChebyshevTData_6 := by
      rw [fixed_chebyshevT_typed_7, fixed_chebyshevT_typed_6]
    _ = fixedChebyshevTData_8 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_7, fixedChebyshevTData_6, fixedChebyshevTData_8, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_7, fixedChebyshevTData_6, fixedChebyshevTData_8, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 8
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 8, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 8 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_9 :
    Chebyshev.T ℤ 9 = fixedChebyshevTData_9 := by
  calc
    Chebyshev.T ℤ 9 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 8 - Chebyshev.T ℤ 7 :=
      Chebyshev.T_add_two ℤ 7
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_8 - fixedChebyshevTData_7 := by
      rw [fixed_chebyshevT_typed_8, fixed_chebyshevT_typed_7]
    _ = fixedChebyshevTData_9 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_8, fixedChebyshevTData_7, fixedChebyshevTData_9, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_8, fixedChebyshevTData_7, fixedChebyshevTData_9, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 9
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 9, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 9 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_10 :
    Chebyshev.T ℤ 10 = fixedChebyshevTData_10 := by
  calc
    Chebyshev.T ℤ 10 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 9 - Chebyshev.T ℤ 8 :=
      Chebyshev.T_add_two ℤ 8
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_9 - fixedChebyshevTData_8 := by
      rw [fixed_chebyshevT_typed_9, fixed_chebyshevT_typed_8]
    _ = fixedChebyshevTData_10 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_9, fixedChebyshevTData_8, fixedChebyshevTData_10, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_9, fixedChebyshevTData_8, fixedChebyshevTData_10, coeff_sub,
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

theorem fixed_chebyshevT_typed_11 :
    Chebyshev.T ℤ 11 = fixedChebyshevTData_11 := by
  calc
    Chebyshev.T ℤ 11 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 10 - Chebyshev.T ℤ 9 :=
      Chebyshev.T_add_two ℤ 9
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_10 - fixedChebyshevTData_9 := by
      rw [fixed_chebyshevT_typed_10, fixed_chebyshevT_typed_9]
    _ = fixedChebyshevTData_11 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_10, fixedChebyshevTData_9, fixedChebyshevTData_11, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_10, fixedChebyshevTData_9, fixedChebyshevTData_11, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 11
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 11, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 11 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_12 :
    Chebyshev.T ℤ 12 = fixedChebyshevTData_12 := by
  calc
    Chebyshev.T ℤ 12 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 11 - Chebyshev.T ℤ 10 :=
      Chebyshev.T_add_two ℤ 10
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_11 - fixedChebyshevTData_10 := by
      rw [fixed_chebyshevT_typed_11, fixed_chebyshevT_typed_10]
    _ = fixedChebyshevTData_12 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_11, fixedChebyshevTData_10, fixedChebyshevTData_12, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_11, fixedChebyshevTData_10, fixedChebyshevTData_12, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 12
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 12, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 12 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_13 :
    Chebyshev.T ℤ 13 = fixedChebyshevTData_13 := by
  calc
    Chebyshev.T ℤ 13 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 12 - Chebyshev.T ℤ 11 :=
      Chebyshev.T_add_two ℤ 11
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_12 - fixedChebyshevTData_11 := by
      rw [fixed_chebyshevT_typed_12, fixed_chebyshevT_typed_11]
    _ = fixedChebyshevTData_13 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_12, fixedChebyshevTData_11, fixedChebyshevTData_13, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_12, fixedChebyshevTData_11, fixedChebyshevTData_13, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 13
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 13, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 13 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_14 :
    Chebyshev.T ℤ 14 = fixedChebyshevTData_14 := by
  calc
    Chebyshev.T ℤ 14 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 13 - Chebyshev.T ℤ 12 :=
      Chebyshev.T_add_two ℤ 12
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_13 - fixedChebyshevTData_12 := by
      rw [fixed_chebyshevT_typed_13, fixed_chebyshevT_typed_12]
    _ = fixedChebyshevTData_14 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_13, fixedChebyshevTData_12, fixedChebyshevTData_14, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_13, fixedChebyshevTData_12, fixedChebyshevTData_14, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 14
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 14, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 14 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_15 :
    Chebyshev.T ℤ 15 = fixedChebyshevTData_15 := by
  calc
    Chebyshev.T ℤ 15 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 14 - Chebyshev.T ℤ 13 :=
      Chebyshev.T_add_two ℤ 13
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_14 - fixedChebyshevTData_13 := by
      rw [fixed_chebyshevT_typed_14, fixed_chebyshevT_typed_13]
    _ = fixedChebyshevTData_15 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_14, fixedChebyshevTData_13, fixedChebyshevTData_15, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_14, fixedChebyshevTData_13, fixedChebyshevTData_15, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 15
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 15, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 15 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_16 :
    Chebyshev.T ℤ 16 = fixedChebyshevTData_16 := by
  calc
    Chebyshev.T ℤ 16 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 15 - Chebyshev.T ℤ 14 :=
      Chebyshev.T_add_two ℤ 14
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_15 - fixedChebyshevTData_14 := by
      rw [fixed_chebyshevT_typed_15, fixed_chebyshevT_typed_14]
    _ = fixedChebyshevTData_16 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_15, fixedChebyshevTData_14, fixedChebyshevTData_16, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_15, fixedChebyshevTData_14, fixedChebyshevTData_16, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 16
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 16, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 16 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_17 :
    Chebyshev.T ℤ 17 = fixedChebyshevTData_17 := by
  calc
    Chebyshev.T ℤ 17 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 16 - Chebyshev.T ℤ 15 :=
      Chebyshev.T_add_two ℤ 15
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_16 - fixedChebyshevTData_15 := by
      rw [fixed_chebyshevT_typed_16, fixed_chebyshevT_typed_15]
    _ = fixedChebyshevTData_17 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_16, fixedChebyshevTData_15, fixedChebyshevTData_17, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_16, fixedChebyshevTData_15, fixedChebyshevTData_17, coeff_sub,
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

theorem fixed_chebyshevT_typed_18 :
    Chebyshev.T ℤ 18 = fixedChebyshevTData_18 := by
  calc
    Chebyshev.T ℤ 18 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 17 - Chebyshev.T ℤ 16 :=
      Chebyshev.T_add_two ℤ 16
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_17 - fixedChebyshevTData_16 := by
      rw [fixed_chebyshevT_typed_17, fixed_chebyshevT_typed_16]
    _ = fixedChebyshevTData_18 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_17, fixedChebyshevTData_16, fixedChebyshevTData_18, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_17, fixedChebyshevTData_16, fixedChebyshevTData_18, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 18
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 18, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 18 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_19 :
    Chebyshev.T ℤ 19 = fixedChebyshevTData_19 := by
  calc
    Chebyshev.T ℤ 19 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 18 - Chebyshev.T ℤ 17 :=
      Chebyshev.T_add_two ℤ 17
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_18 - fixedChebyshevTData_17 := by
      rw [fixed_chebyshevT_typed_18, fixed_chebyshevT_typed_17]
    _ = fixedChebyshevTData_19 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_18, fixedChebyshevTData_17, fixedChebyshevTData_19, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_18, fixedChebyshevTData_17, fixedChebyshevTData_19, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 19
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 19, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 19 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_20 :
    Chebyshev.T ℤ 20 = fixedChebyshevTData_20 := by
  calc
    Chebyshev.T ℤ 20 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 19 - Chebyshev.T ℤ 18 :=
      Chebyshev.T_add_two ℤ 18
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_19 - fixedChebyshevTData_18 := by
      rw [fixed_chebyshevT_typed_19, fixed_chebyshevT_typed_18]
    _ = fixedChebyshevTData_20 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_19, fixedChebyshevTData_18, fixedChebyshevTData_20, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_19, fixedChebyshevTData_18, fixedChebyshevTData_20, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 20
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 20, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 20 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_21 :
    Chebyshev.T ℤ 21 = fixedChebyshevTData_21 := by
  calc
    Chebyshev.T ℤ 21 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 20 - Chebyshev.T ℤ 19 :=
      Chebyshev.T_add_two ℤ 19
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_20 - fixedChebyshevTData_19 := by
      rw [fixed_chebyshevT_typed_20, fixed_chebyshevT_typed_19]
    _ = fixedChebyshevTData_21 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_20, fixedChebyshevTData_19, fixedChebyshevTData_21, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_20, fixedChebyshevTData_19, fixedChebyshevTData_21, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 21
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 21, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 21 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]

theorem fixed_chebyshevT_typed_22 :
    Chebyshev.T ℤ 22 = fixedChebyshevTData_22 := by
  calc
    Chebyshev.T ℤ 22 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 21 - Chebyshev.T ℤ 20 :=
      Chebyshev.T_add_two ℤ 20
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_21 - fixedChebyshevTData_20 := by
      rw [fixed_chebyshevT_typed_21, fixed_chebyshevT_typed_20]
    _ = fixedChebyshevTData_22 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_21, fixedChebyshevTData_20, fixedChebyshevTData_22, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_21, fixedChebyshevTData_20, fixedChebyshevTData_22, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 22
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 22, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 22 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]


end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevT_typed_24 :
    Chebyshev.T ℤ 24 = fixedChebyshevTData_24 := by
  calc
    Chebyshev.T ℤ 24 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_23 - fixedChebyshevTData_22 :=
      fixedTyped_chebyshevT_link 22 23 24 fixedChebyshevTData_22 fixedChebyshevTData_23
        (by decide) (by decide) fixed_chebyshevT_typed_22 fixed_chebyshevT_typed_23
    _ = fixedChebyshevTData_24 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_23, fixedChebyshevTData_22, fixedChebyshevTData_24, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_23, fixedChebyshevTData_22, fixedChebyshevTData_24, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 24
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 24, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 24 ≤ k := Nat.le_of_not_gt hk
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

end OAI

end

section
open OAI.InternalCatalan
open Polynomial

theorem solution :
    Chebyshev.T ℤ 24 = fixedChebyshevTData_24 := by
  first
  | exact @OAI.InternalCatalan.fixed_chebyshevT_typed_24
  | (apply OAI.InternalCatalan.fixed_chebyshevT_typed_24 <;> assumption)

end
