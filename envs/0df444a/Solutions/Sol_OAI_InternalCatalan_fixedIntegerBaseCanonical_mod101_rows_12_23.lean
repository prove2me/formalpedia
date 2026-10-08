-- Prove2me | solution 1 for OAI.InternalCatalan.fixedIntegerBaseCanonical_mod101_rows_12_23
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T19:49:05.568067+00:00
-- url     : https://prove2.me/submissions/22030e52-5481-4da5-b3d3-e748df8b22c4

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
-- module Solutions.OAICatalan.Catalan.Estimates.FixedCompactReversedT8To15
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedReversedTData_8 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-32 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (160 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-256 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (128 : ℤ)

def fixedReversedTCoeff_8 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-32 : ℤ) else 0) +
    (if 58 = n then (160 : ℤ) else 0) +
    (if 56 = n then (-256 : ℤ) else 0) +
    (if 54 = n then (128 : ℤ) else 0)

theorem fixed_reversedT_typed_data_8 : reversedRow 63 fixedChebyshevTData_8 = fixedReversedTData_8 := by
  simp only [fixedChebyshevTData_8, fixedReversedTData_8, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-32 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (160 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-256 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (128 : ℤ) 8 (by decide)]

theorem fixed_reversedT_typed_coeff_8 (n : ℕ) :
    fixedReversedTData_8.coeff n = fixedReversedTCoeff_8 n := by
  simp only [fixedReversedTData_8, fixedReversedTCoeff_8, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_8 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_8 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_8, if_neg, add_zero]

def fixedReversedTData_9 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (9 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-120 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (432 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-576 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (256 : ℤ)

def fixedReversedTCoeff_9 (n : ℕ) : ℤ :=
    (if 61 = n then (9 : ℤ) else 0) +
    (if 59 = n then (-120 : ℤ) else 0) +
    (if 57 = n then (432 : ℤ) else 0) +
    (if 55 = n then (-576 : ℤ) else 0) +
    (if 53 = n then (256 : ℤ) else 0)

theorem fixed_reversedT_typed_data_9 : reversedRow 63 fixedChebyshevTData_9 = fixedReversedTData_9 := by
  simp only [fixedChebyshevTData_9, fixedReversedTData_9, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (9 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-120 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (432 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-576 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (256 : ℤ) 9 (by decide)]

theorem fixed_reversedT_typed_coeff_9 (n : ℕ) :
    fixedReversedTData_9.coeff n = fixedReversedTCoeff_9 n := by
  simp only [fixedReversedTData_9, fixedReversedTCoeff_9, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_9 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_9 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_9, if_neg, add_zero]

def fixedReversedTData_10 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (50 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-400 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (1120 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-1280 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (512 : ℤ)

def fixedReversedTCoeff_10 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (50 : ℤ) else 0) +
    (if 58 = n then (-400 : ℤ) else 0) +
    (if 56 = n then (1120 : ℤ) else 0) +
    (if 54 = n then (-1280 : ℤ) else 0) +
    (if 52 = n then (512 : ℤ) else 0)

theorem fixed_reversedT_typed_data_10 : reversedRow 63 fixedChebyshevTData_10 = fixedReversedTData_10 := by
  simp only [fixedChebyshevTData_10, fixedReversedTData_10, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (50 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-400 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (1120 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-1280 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (512 : ℤ) 10 (by decide)]

theorem fixed_reversedT_typed_coeff_10 (n : ℕ) :
    fixedReversedTData_10.coeff n = fixedReversedTCoeff_10 n := by
  simp only [fixedReversedTData_10, fixedReversedTCoeff_10, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_10 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_10 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_10, if_neg, add_zero]

def fixedReversedTData_11 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-11 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (220 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-1232 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (2816 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-2816 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (1024 : ℤ)

def fixedReversedTCoeff_11 (n : ℕ) : ℤ :=
    (if 61 = n then (-11 : ℤ) else 0) +
    (if 59 = n then (220 : ℤ) else 0) +
    (if 57 = n then (-1232 : ℤ) else 0) +
    (if 55 = n then (2816 : ℤ) else 0) +
    (if 53 = n then (-2816 : ℤ) else 0) +
    (if 51 = n then (1024 : ℤ) else 0)

theorem fixed_reversedT_typed_data_11 : reversedRow 63 fixedChebyshevTData_11 = fixedReversedTData_11 := by
  simp only [fixedChebyshevTData_11, fixedReversedTData_11, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-11 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (220 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-1232 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (2816 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-2816 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (1024 : ℤ) 11 (by decide)]

theorem fixed_reversedT_typed_coeff_11 (n : ℕ) :
    fixedReversedTData_11.coeff n = fixedReversedTCoeff_11 n := by
  simp only [fixedReversedTData_11, fixedReversedTCoeff_11, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_11 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_11 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_11, if_neg, add_zero]

def fixedReversedTData_12 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-72 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (840 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-3584 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (6912 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-6144 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (2048 : ℤ)

def fixedReversedTCoeff_12 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-72 : ℤ) else 0) +
    (if 58 = n then (840 : ℤ) else 0) +
    (if 56 = n then (-3584 : ℤ) else 0) +
    (if 54 = n then (6912 : ℤ) else 0) +
    (if 52 = n then (-6144 : ℤ) else 0) +
    (if 50 = n then (2048 : ℤ) else 0)

theorem fixed_reversedT_typed_data_12 : reversedRow 63 fixedChebyshevTData_12 = fixedReversedTData_12 := by
  simp only [fixedChebyshevTData_12, fixedReversedTData_12, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-72 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (840 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-3584 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (6912 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-6144 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (2048 : ℤ) 12 (by decide)]

theorem fixed_reversedT_typed_coeff_12 (n : ℕ) :
    fixedReversedTData_12.coeff n = fixedReversedTCoeff_12 n := by
  simp only [fixedReversedTData_12, fixedReversedTCoeff_12, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_12 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_12 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_12, if_neg, add_zero]

def fixedReversedTData_13 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (13 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-364 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (2912 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-9984 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (16640 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-13312 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (4096 : ℤ)

def fixedReversedTCoeff_13 (n : ℕ) : ℤ :=
    (if 61 = n then (13 : ℤ) else 0) +
    (if 59 = n then (-364 : ℤ) else 0) +
    (if 57 = n then (2912 : ℤ) else 0) +
    (if 55 = n then (-9984 : ℤ) else 0) +
    (if 53 = n then (16640 : ℤ) else 0) +
    (if 51 = n then (-13312 : ℤ) else 0) +
    (if 49 = n then (4096 : ℤ) else 0)

theorem fixed_reversedT_typed_data_13 : reversedRow 63 fixedChebyshevTData_13 = fixedReversedTData_13 := by
  simp only [fixedChebyshevTData_13, fixedReversedTData_13, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (13 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-364 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (2912 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-9984 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (16640 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-13312 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (4096 : ℤ) 13 (by decide)]

theorem fixed_reversedT_typed_coeff_13 (n : ℕ) :
    fixedReversedTData_13.coeff n = fixedReversedTCoeff_13 n := by
  simp only [fixedReversedTData_13, fixedReversedTCoeff_13, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_13 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_13 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_13, if_neg, add_zero]

def fixedReversedTData_14 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (98 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-1568 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (9408 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-26880 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (39424 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-28672 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (8192 : ℤ)

def fixedReversedTCoeff_14 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (98 : ℤ) else 0) +
    (if 58 = n then (-1568 : ℤ) else 0) +
    (if 56 = n then (9408 : ℤ) else 0) +
    (if 54 = n then (-26880 : ℤ) else 0) +
    (if 52 = n then (39424 : ℤ) else 0) +
    (if 50 = n then (-28672 : ℤ) else 0) +
    (if 48 = n then (8192 : ℤ) else 0)

theorem fixed_reversedT_typed_data_14 : reversedRow 63 fixedChebyshevTData_14 = fixedReversedTData_14 := by
  simp only [fixedChebyshevTData_14, fixedReversedTData_14, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (98 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-1568 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (9408 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-26880 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (39424 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-28672 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (8192 : ℤ) 14 (by decide)]

theorem fixed_reversedT_typed_coeff_14 (n : ℕ) :
    fixedReversedTData_14.coeff n = fixedReversedTCoeff_14 n := by
  simp only [fixedReversedTData_14, fixedReversedTCoeff_14, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_14 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_14 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_14, if_neg, add_zero]

def fixedReversedTData_15 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-15 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (560 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-6048 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (28800 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-70400 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (92160 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-61440 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (16384 : ℤ)

def fixedReversedTCoeff_15 (n : ℕ) : ℤ :=
    (if 61 = n then (-15 : ℤ) else 0) +
    (if 59 = n then (560 : ℤ) else 0) +
    (if 57 = n then (-6048 : ℤ) else 0) +
    (if 55 = n then (28800 : ℤ) else 0) +
    (if 53 = n then (-70400 : ℤ) else 0) +
    (if 51 = n then (92160 : ℤ) else 0) +
    (if 49 = n then (-61440 : ℤ) else 0) +
    (if 47 = n then (16384 : ℤ) else 0)

theorem fixed_reversedT_typed_data_15 : reversedRow 63 fixedChebyshevTData_15 = fixedReversedTData_15 := by
  simp only [fixedChebyshevTData_15, fixedReversedTData_15, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-15 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (560 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-6048 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (28800 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-70400 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (92160 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-61440 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (16384 : ℤ) 15 (by decide)]

theorem fixed_reversedT_typed_coeff_15 (n : ℕ) :
    fixedReversedTData_15.coeff n = fixedReversedTCoeff_15 n := by
  simp only [fixedReversedTData_15, fixedReversedTCoeff_15, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_15 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_15 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_15, if_neg, add_zero]

end InternalCatalan

end

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




































def fixedReversedUData_7 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-8 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (80 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-192 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (128 : ℤ)

def fixedReversedUCoeff_7 (n : ℕ) : ℤ :=
    (if 61 = n then (-8 : ℤ) else 0) +
    (if 59 = n then (80 : ℤ) else 0) +
    (if 57 = n then (-192 : ℤ) else 0) +
    (if 55 = n then (128 : ℤ) else 0)

theorem fixed_reversedU_typed_data_7 : reversedRow 63 fixedChebyshevUData_7 = fixedReversedUData_7 := by
  simp only [fixedChebyshevUData_7, fixedReversedUData_7, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-8 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (80 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-192 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (128 : ℤ) 7 (by decide)]

theorem fixed_reversedU_typed_coeff_7 (n : ℕ) :
    fixedReversedUData_7.coeff n = fixedReversedUCoeff_7 n := by
  simp only [fixedReversedUData_7, fixedReversedUCoeff_7, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_7 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_7 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_7, if_neg, add_zero]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow12
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_12 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 54 (128 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-256 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-128 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (512 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-96 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-320 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (128 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (64 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-31 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_12 (n : ℕ) : ℤ :=
    (if 54 = n then (128 : ℤ) else 0) +
    (if 55 = n then (-256 : ℤ) else 0) +
    (if 56 = n then (-128 : ℤ) else 0) +
    (if 57 = n then (512 : ℤ) else 0) +
    (if 58 = n then (-96 : ℤ) else 0) +
    (if 59 = n then (-320 : ℤ) else 0) +
    (if 60 = n then (128 : ℤ) else 0) +
    (if 61 = n then (64 : ℤ) else 0) +
    (if 62 = n then (-31 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_12 (n : ℕ) :
    fixedRowPData_12.coeff n = fixedRowPCoeff_12 n := by
  simp only [fixedRowPData_12, fixedRowPCoeff_12, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_12 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_12 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_12, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_12 : ∀ k : Fin 63,
    fixedReversedTCoeff_8 (k.val + 2) - 2 * fixedReversedTCoeff_8 (k.val + 1) + fixedReversedTCoeff_8 k.val = fixedRowPCoeff_12 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_12 :
    (1 - X) ^ 2 * fixedReversedTData_8 = fixedRowPData_12 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_8, fixed_rowP_typed_coeff_12]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_8, fixed_rowP_typed_coeff_12]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_8, fixed_rowP_typed_coeff_12]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_12 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_8 _ (by omega),
              fixed_reversedT_typed_tail_8 _ (by omega), fixed_reversedT_typed_tail_8 _ hn',
              fixed_rowP_typed_tail_12 _ (by omega)]
            decide

theorem fixed_rowP_typed_12 : rowP 1 12 = fixedRowPData_12 := by
  calc
    rowP 1 12 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_8 :=
      fixedTyped_rowP_of_parameters 1 12 2 63 8 fixedChebyshevTData_8
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_8
    _ = fixedRowPData_12 := by
      rw [fixed_reversedT_typed_data_8, fixed_rowP_typed_factor_12]

def fixedRowDData_12 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 55 (128 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-256 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-64 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (384 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-112 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-160 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (72 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (16 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-8 : ℤ)

def fixedRowDCoeff_12 (n : ℕ) : ℤ :=
    (if 55 = n then (128 : ℤ) else 0) +
    (if 56 = n then (-256 : ℤ) else 0) +
    (if 57 = n then (-64 : ℤ) else 0) +
    (if 58 = n then (384 : ℤ) else 0) +
    (if 59 = n then (-112 : ℤ) else 0) +
    (if 60 = n then (-160 : ℤ) else 0) +
    (if 61 = n then (72 : ℤ) else 0) +
    (if 62 = n then (16 : ℤ) else 0) +
    (if 63 = n then (-8 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_12 (n : ℕ) :
    fixedRowDData_12.coeff n = fixedRowDCoeff_12 n := by
  simp only [fixedRowDData_12, fixedRowDCoeff_12, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_12 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_12 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_12, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_12 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_7 (k.val + 2) - 2 * fixedReversedUCoeff_7 (k.val + 1) + fixedReversedUCoeff_7 k.val) = fixedRowDCoeff_12 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_12 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_7 = fixedRowDData_12 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_7, fixed_rowD_typed_coeff_12]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_7, fixed_rowD_typed_coeff_12]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_7, fixed_rowD_typed_coeff_12]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_12 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_7 _ (by omega),
              fixed_reversedU_typed_tail_7 _ (by omega), fixed_reversedU_typed_tail_7 _ hn',
              fixed_rowD_typed_tail_12 _ (by omega)]
            decide

theorem fixed_rowD_typed_12 : rowD 1 12 = fixedRowDData_12 := by
  calc
    rowD 1 12 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_7 :=
      fixedTyped_rowD_of_parameters 1 12 2 63 7 (1)
        fixedChebyshevUData_7 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_7
    _ = fixedRowDData_12 := by
      rw [fixed_reversedU_typed_data_7, fixed_rowD_typed_factor_12]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.FixedCompactReversedU8To15
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedReversedUData_8 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-40 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (240 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-448 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (256 : ℤ)

def fixedReversedUCoeff_8 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-40 : ℤ) else 0) +
    (if 58 = n then (240 : ℤ) else 0) +
    (if 56 = n then (-448 : ℤ) else 0) +
    (if 54 = n then (256 : ℤ) else 0)

theorem fixed_reversedU_typed_data_8 : reversedRow 63 fixedChebyshevUData_8 = fixedReversedUData_8 := by
  simp only [fixedChebyshevUData_8, fixedReversedUData_8, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-40 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (240 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-448 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (256 : ℤ) 8 (by decide)]

theorem fixed_reversedU_typed_coeff_8 (n : ℕ) :
    fixedReversedUData_8.coeff n = fixedReversedUCoeff_8 n := by
  simp only [fixedReversedUData_8, fixedReversedUCoeff_8, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_8 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_8 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_8, if_neg, add_zero]

def fixedReversedUData_9 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (10 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-160 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (672 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-1024 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (512 : ℤ)

def fixedReversedUCoeff_9 (n : ℕ) : ℤ :=
    (if 61 = n then (10 : ℤ) else 0) +
    (if 59 = n then (-160 : ℤ) else 0) +
    (if 57 = n then (672 : ℤ) else 0) +
    (if 55 = n then (-1024 : ℤ) else 0) +
    (if 53 = n then (512 : ℤ) else 0)

theorem fixed_reversedU_typed_data_9 : reversedRow 63 fixedChebyshevUData_9 = fixedReversedUData_9 := by
  simp only [fixedChebyshevUData_9, fixedReversedUData_9, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (10 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-160 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (672 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-1024 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (512 : ℤ) 9 (by decide)]

theorem fixed_reversedU_typed_coeff_9 (n : ℕ) :
    fixedReversedUData_9.coeff n = fixedReversedUCoeff_9 n := by
  simp only [fixedReversedUData_9, fixedReversedUCoeff_9, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_9 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_9 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_9, if_neg, add_zero]

def fixedReversedUData_10 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (60 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-560 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (1792 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-2304 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (1024 : ℤ)

def fixedReversedUCoeff_10 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (60 : ℤ) else 0) +
    (if 58 = n then (-560 : ℤ) else 0) +
    (if 56 = n then (1792 : ℤ) else 0) +
    (if 54 = n then (-2304 : ℤ) else 0) +
    (if 52 = n then (1024 : ℤ) else 0)

theorem fixed_reversedU_typed_data_10 : reversedRow 63 fixedChebyshevUData_10 = fixedReversedUData_10 := by
  simp only [fixedChebyshevUData_10, fixedReversedUData_10, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (60 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-560 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (1792 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-2304 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (1024 : ℤ) 10 (by decide)]

theorem fixed_reversedU_typed_coeff_10 (n : ℕ) :
    fixedReversedUData_10.coeff n = fixedReversedUCoeff_10 n := by
  simp only [fixedReversedUData_10, fixedReversedUCoeff_10, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_10 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_10 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_10, if_neg, add_zero]

def fixedReversedUData_11 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-12 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (280 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-1792 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (4608 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-5120 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (2048 : ℤ)

def fixedReversedUCoeff_11 (n : ℕ) : ℤ :=
    (if 61 = n then (-12 : ℤ) else 0) +
    (if 59 = n then (280 : ℤ) else 0) +
    (if 57 = n then (-1792 : ℤ) else 0) +
    (if 55 = n then (4608 : ℤ) else 0) +
    (if 53 = n then (-5120 : ℤ) else 0) +
    (if 51 = n then (2048 : ℤ) else 0)

theorem fixed_reversedU_typed_data_11 : reversedRow 63 fixedChebyshevUData_11 = fixedReversedUData_11 := by
  simp only [fixedChebyshevUData_11, fixedReversedUData_11, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-12 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (280 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-1792 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (4608 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-5120 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (2048 : ℤ) 11 (by decide)]

theorem fixed_reversedU_typed_coeff_11 (n : ℕ) :
    fixedReversedUData_11.coeff n = fixedReversedUCoeff_11 n := by
  simp only [fixedReversedUData_11, fixedReversedUCoeff_11, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_11 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_11 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_11, if_neg, add_zero]

def fixedReversedUData_12 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-84 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (1120 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-5376 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (11520 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-11264 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (4096 : ℤ)

def fixedReversedUCoeff_12 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-84 : ℤ) else 0) +
    (if 58 = n then (1120 : ℤ) else 0) +
    (if 56 = n then (-5376 : ℤ) else 0) +
    (if 54 = n then (11520 : ℤ) else 0) +
    (if 52 = n then (-11264 : ℤ) else 0) +
    (if 50 = n then (4096 : ℤ) else 0)

theorem fixed_reversedU_typed_data_12 : reversedRow 63 fixedChebyshevUData_12 = fixedReversedUData_12 := by
  simp only [fixedChebyshevUData_12, fixedReversedUData_12, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-84 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (1120 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-5376 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (11520 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-11264 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (4096 : ℤ) 12 (by decide)]

theorem fixed_reversedU_typed_coeff_12 (n : ℕ) :
    fixedReversedUData_12.coeff n = fixedReversedUCoeff_12 n := by
  simp only [fixedReversedUData_12, fixedReversedUCoeff_12, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_12 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_12 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_12, if_neg, add_zero]

def fixedReversedUData_13 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (14 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-448 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (4032 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-15360 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (28160 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-24576 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (8192 : ℤ)

def fixedReversedUCoeff_13 (n : ℕ) : ℤ :=
    (if 61 = n then (14 : ℤ) else 0) +
    (if 59 = n then (-448 : ℤ) else 0) +
    (if 57 = n then (4032 : ℤ) else 0) +
    (if 55 = n then (-15360 : ℤ) else 0) +
    (if 53 = n then (28160 : ℤ) else 0) +
    (if 51 = n then (-24576 : ℤ) else 0) +
    (if 49 = n then (8192 : ℤ) else 0)

theorem fixed_reversedU_typed_data_13 : reversedRow 63 fixedChebyshevUData_13 = fixedReversedUData_13 := by
  simp only [fixedChebyshevUData_13, fixedReversedUData_13, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (14 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-448 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (4032 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-15360 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (28160 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-24576 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (8192 : ℤ) 13 (by decide)]

theorem fixed_reversedU_typed_coeff_13 (n : ℕ) :
    fixedReversedUData_13.coeff n = fixedReversedUCoeff_13 n := by
  simp only [fixedReversedUData_13, fixedReversedUCoeff_13, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_13 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_13 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_13, if_neg, add_zero]

def fixedReversedUData_14 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (112 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-2016 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (13440 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-42240 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (67584 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-53248 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (16384 : ℤ)

def fixedReversedUCoeff_14 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (112 : ℤ) else 0) +
    (if 58 = n then (-2016 : ℤ) else 0) +
    (if 56 = n then (13440 : ℤ) else 0) +
    (if 54 = n then (-42240 : ℤ) else 0) +
    (if 52 = n then (67584 : ℤ) else 0) +
    (if 50 = n then (-53248 : ℤ) else 0) +
    (if 48 = n then (16384 : ℤ) else 0)

theorem fixed_reversedU_typed_data_14 : reversedRow 63 fixedChebyshevUData_14 = fixedReversedUData_14 := by
  simp only [fixedChebyshevUData_14, fixedReversedUData_14, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (112 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-2016 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (13440 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-42240 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (67584 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-53248 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (16384 : ℤ) 14 (by decide)]

theorem fixed_reversedU_typed_coeff_14 (n : ℕ) :
    fixedReversedUData_14.coeff n = fixedReversedUCoeff_14 n := by
  simp only [fixedReversedUData_14, fixedReversedUCoeff_14, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_14 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_14 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_14, if_neg, add_zero]

def fixedReversedUData_15 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-16 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (672 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-8064 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (42240 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-112640 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (159744 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-114688 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (32768 : ℤ)

def fixedReversedUCoeff_15 (n : ℕ) : ℤ :=
    (if 61 = n then (-16 : ℤ) else 0) +
    (if 59 = n then (672 : ℤ) else 0) +
    (if 57 = n then (-8064 : ℤ) else 0) +
    (if 55 = n then (42240 : ℤ) else 0) +
    (if 53 = n then (-112640 : ℤ) else 0) +
    (if 51 = n then (159744 : ℤ) else 0) +
    (if 49 = n then (-114688 : ℤ) else 0) +
    (if 47 = n then (32768 : ℤ) else 0)

theorem fixed_reversedU_typed_data_15 : reversedRow 63 fixedChebyshevUData_15 = fixedReversedUData_15 := by
  simp only [fixedChebyshevUData_15, fixedReversedUData_15, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-16 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (672 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-8064 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (42240 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-112640 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (159744 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-114688 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (32768 : ℤ) 15 (by decide)]

theorem fixed_reversedU_typed_coeff_15 (n : ℕ) :
    fixedReversedUData_15.coeff n = fixedReversedUCoeff_15 n := by
  simp only [fixedReversedUData_15, fixedReversedUCoeff_15, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_15 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_15 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_15, if_neg, add_zero]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow13
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_13 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 53 (256 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-512 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-320 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (1152 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-144 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-864 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (312 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (240 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-111 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-18 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (9 : ℤ)

def fixedRowPCoeff_13 (n : ℕ) : ℤ :=
    (if 53 = n then (256 : ℤ) else 0) +
    (if 54 = n then (-512 : ℤ) else 0) +
    (if 55 = n then (-320 : ℤ) else 0) +
    (if 56 = n then (1152 : ℤ) else 0) +
    (if 57 = n then (-144 : ℤ) else 0) +
    (if 58 = n then (-864 : ℤ) else 0) +
    (if 59 = n then (312 : ℤ) else 0) +
    (if 60 = n then (240 : ℤ) else 0) +
    (if 61 = n then (-111 : ℤ) else 0) +
    (if 62 = n then (-18 : ℤ) else 0) +
    (if 63 = n then (9 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_13 (n : ℕ) :
    fixedRowPData_13.coeff n = fixedRowPCoeff_13 n := by
  simp only [fixedRowPData_13, fixedRowPCoeff_13, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_13 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_13 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_13, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_13 : ∀ k : Fin 63,
    fixedReversedTCoeff_9 (k.val + 2) - 2 * fixedReversedTCoeff_9 (k.val + 1) + fixedReversedTCoeff_9 k.val = fixedRowPCoeff_13 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_13 :
    (1 - X) ^ 2 * fixedReversedTData_9 = fixedRowPData_13 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_9, fixed_rowP_typed_coeff_13]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_9, fixed_rowP_typed_coeff_13]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_9, fixed_rowP_typed_coeff_13]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_13 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_9 _ (by omega),
              fixed_reversedT_typed_tail_9 _ (by omega), fixed_reversedT_typed_tail_9 _ hn',
              fixed_rowP_typed_tail_13 _ (by omega)]
            decide

theorem fixed_rowP_typed_13 : rowP 1 13 = fixedRowPData_13 := by
  calc
    rowP 1 13 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_9 :=
      fixedTyped_rowP_of_parameters 1 13 2 63 9 fixedChebyshevTData_9
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_9
    _ = fixedRowPData_13 := by
      rw [fixed_reversedT_typed_data_9, fixed_rowP_typed_factor_13]

def fixedRowDData_13 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 54 (256 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-512 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-192 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (896 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-208 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-480 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (200 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (80 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-39 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowDCoeff_13 (n : ℕ) : ℤ :=
    (if 54 = n then (256 : ℤ) else 0) +
    (if 55 = n then (-512 : ℤ) else 0) +
    (if 56 = n then (-192 : ℤ) else 0) +
    (if 57 = n then (896 : ℤ) else 0) +
    (if 58 = n then (-208 : ℤ) else 0) +
    (if 59 = n then (-480 : ℤ) else 0) +
    (if 60 = n then (200 : ℤ) else 0) +
    (if 61 = n then (80 : ℤ) else 0) +
    (if 62 = n then (-39 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_13 (n : ℕ) :
    fixedRowDData_13.coeff n = fixedRowDCoeff_13 n := by
  simp only [fixedRowDData_13, fixedRowDCoeff_13, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_13 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_13 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_13, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_13 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_8 (k.val + 2) - 2 * fixedReversedUCoeff_8 (k.val + 1) + fixedReversedUCoeff_8 k.val) = fixedRowDCoeff_13 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_13 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_8 = fixedRowDData_13 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_8, fixed_rowD_typed_coeff_13]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_8, fixed_rowD_typed_coeff_13]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_8, fixed_rowD_typed_coeff_13]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_13 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_8 _ (by omega),
              fixed_reversedU_typed_tail_8 _ (by omega), fixed_reversedU_typed_tail_8 _ hn',
              fixed_rowD_typed_tail_13 _ (by omega)]
            decide

theorem fixed_rowD_typed_13 : rowD 1 13 = fixedRowDData_13 := by
  calc
    rowD 1 13 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_8 :=
      fixedTyped_rowD_of_parameters 1 13 2 63 8 (1)
        fixedChebyshevUData_8 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_8
    _ = fixedRowDData_13 := by
      rw [fixed_reversedU_typed_data_8, fixed_rowD_typed_factor_13]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow14
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_14 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 52 (512 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-1024 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-768 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (2560 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-160 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-2240 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (720 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (800 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-350 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-100 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (49 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowPCoeff_14 (n : ℕ) : ℤ :=
    (if 52 = n then (512 : ℤ) else 0) +
    (if 53 = n then (-1024 : ℤ) else 0) +
    (if 54 = n then (-768 : ℤ) else 0) +
    (if 55 = n then (2560 : ℤ) else 0) +
    (if 56 = n then (-160 : ℤ) else 0) +
    (if 57 = n then (-2240 : ℤ) else 0) +
    (if 58 = n then (720 : ℤ) else 0) +
    (if 59 = n then (800 : ℤ) else 0) +
    (if 60 = n then (-350 : ℤ) else 0) +
    (if 61 = n then (-100 : ℤ) else 0) +
    (if 62 = n then (49 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_14 (n : ℕ) :
    fixedRowPData_14.coeff n = fixedRowPCoeff_14 n := by
  simp only [fixedRowPData_14, fixedRowPCoeff_14, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_14 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_14 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_14, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_14 : ∀ k : Fin 63,
    fixedReversedTCoeff_10 (k.val + 2) - 2 * fixedReversedTCoeff_10 (k.val + 1) + fixedReversedTCoeff_10 k.val = fixedRowPCoeff_14 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_14 :
    (1 - X) ^ 2 * fixedReversedTData_10 = fixedRowPData_14 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_10, fixed_rowP_typed_coeff_14]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_10, fixed_rowP_typed_coeff_14]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_10, fixed_rowP_typed_coeff_14]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_14 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_10 _ (by omega),
              fixed_reversedT_typed_tail_10 _ (by omega), fixed_reversedT_typed_tail_10 _ hn',
              fixed_rowP_typed_tail_14 _ (by omega)]
            decide

theorem fixed_rowP_typed_14 : rowP 1 14 = fixedRowPData_14 := by
  calc
    rowP 1 14 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_10 :=
      fixedTyped_rowP_of_parameters 1 14 2 63 10 fixedChebyshevTData_10
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_10
    _ = fixedRowPData_14 := by
      rw [fixed_reversedT_typed_data_10, fixed_rowP_typed_factor_14]

def fixedRowDData_14 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 53 (512 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-1024 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-512 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (2048 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-352 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-1344 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (512 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (320 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-150 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-20 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (10 : ℤ)

def fixedRowDCoeff_14 (n : ℕ) : ℤ :=
    (if 53 = n then (512 : ℤ) else 0) +
    (if 54 = n then (-1024 : ℤ) else 0) +
    (if 55 = n then (-512 : ℤ) else 0) +
    (if 56 = n then (2048 : ℤ) else 0) +
    (if 57 = n then (-352 : ℤ) else 0) +
    (if 58 = n then (-1344 : ℤ) else 0) +
    (if 59 = n then (512 : ℤ) else 0) +
    (if 60 = n then (320 : ℤ) else 0) +
    (if 61 = n then (-150 : ℤ) else 0) +
    (if 62 = n then (-20 : ℤ) else 0) +
    (if 63 = n then (10 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_14 (n : ℕ) :
    fixedRowDData_14.coeff n = fixedRowDCoeff_14 n := by
  simp only [fixedRowDData_14, fixedRowDCoeff_14, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_14 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_14 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_14, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_14 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_9 (k.val + 2) - 2 * fixedReversedUCoeff_9 (k.val + 1) + fixedReversedUCoeff_9 k.val) = fixedRowDCoeff_14 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_14 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_9 = fixedRowDData_14 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_9, fixed_rowD_typed_coeff_14]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_9, fixed_rowD_typed_coeff_14]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_9, fixed_rowD_typed_coeff_14]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_14 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_9 _ (by omega),
              fixed_reversedU_typed_tail_9 _ (by omega), fixed_reversedU_typed_tail_9 _ hn',
              fixed_rowD_typed_tail_14 _ (by omega)]
            decide

theorem fixed_rowD_typed_14 : rowD 1 14 = fixedRowDData_14 := by
  calc
    rowD 1 14 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_9 :=
      fixedTyped_rowD_of_parameters 1 14 2 63 9 (1)
        fixedChebyshevUData_9 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_9
    _ = fixedRowDData_14 := by
      rw [fixed_reversedU_typed_data_9, fixed_rowD_typed_factor_14]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow15
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_15 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 51 (1024 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-2048 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-1792 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (5632 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-5632 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (1584 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (2464 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-1012 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-440 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (209 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (22 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-11 : ℤ)

def fixedRowPCoeff_15 (n : ℕ) : ℤ :=
    (if 51 = n then (1024 : ℤ) else 0) +
    (if 52 = n then (-2048 : ℤ) else 0) +
    (if 53 = n then (-1792 : ℤ) else 0) +
    (if 54 = n then (5632 : ℤ) else 0) +
    (if 56 = n then (-5632 : ℤ) else 0) +
    (if 57 = n then (1584 : ℤ) else 0) +
    (if 58 = n then (2464 : ℤ) else 0) +
    (if 59 = n then (-1012 : ℤ) else 0) +
    (if 60 = n then (-440 : ℤ) else 0) +
    (if 61 = n then (209 : ℤ) else 0) +
    (if 62 = n then (22 : ℤ) else 0) +
    (if 63 = n then (-11 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_15 (n : ℕ) :
    fixedRowPData_15.coeff n = fixedRowPCoeff_15 n := by
  simp only [fixedRowPData_15, fixedRowPCoeff_15, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_15 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_15 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_15, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_15 : ∀ k : Fin 63,
    fixedReversedTCoeff_11 (k.val + 2) - 2 * fixedReversedTCoeff_11 (k.val + 1) + fixedReversedTCoeff_11 k.val = fixedRowPCoeff_15 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_15 :
    (1 - X) ^ 2 * fixedReversedTData_11 = fixedRowPData_15 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_11, fixed_rowP_typed_coeff_15]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_11, fixed_rowP_typed_coeff_15]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_11, fixed_rowP_typed_coeff_15]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_15 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_11 _ (by omega),
              fixed_reversedT_typed_tail_11 _ (by omega), fixed_reversedT_typed_tail_11 _ hn',
              fixed_rowP_typed_tail_15 _ (by omega)]
            decide

theorem fixed_rowP_typed_15 : rowP 1 15 = fixedRowPData_15 := by
  calc
    rowP 1 15 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_11 :=
      fixedTyped_rowP_of_parameters 1 15 2 63 11 fixedChebyshevTData_11
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_11
    _ = fixedRowPData_15 := by
      rw [fixed_reversedT_typed_data_11, fixed_rowP_typed_factor_15]

def fixedRowDData_15 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 52 (1024 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-2048 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-1280 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (4608 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-512 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-3584 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (1232 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (1120 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-500 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-120 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (59 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowDCoeff_15 (n : ℕ) : ℤ :=
    (if 52 = n then (1024 : ℤ) else 0) +
    (if 53 = n then (-2048 : ℤ) else 0) +
    (if 54 = n then (-1280 : ℤ) else 0) +
    (if 55 = n then (4608 : ℤ) else 0) +
    (if 56 = n then (-512 : ℤ) else 0) +
    (if 57 = n then (-3584 : ℤ) else 0) +
    (if 58 = n then (1232 : ℤ) else 0) +
    (if 59 = n then (1120 : ℤ) else 0) +
    (if 60 = n then (-500 : ℤ) else 0) +
    (if 61 = n then (-120 : ℤ) else 0) +
    (if 62 = n then (59 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_15 (n : ℕ) :
    fixedRowDData_15.coeff n = fixedRowDCoeff_15 n := by
  simp only [fixedRowDData_15, fixedRowDCoeff_15, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_15 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_15 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_15, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_15 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_10 (k.val + 2) - 2 * fixedReversedUCoeff_10 (k.val + 1) + fixedReversedUCoeff_10 k.val) = fixedRowDCoeff_15 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_15 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_10 = fixedRowDData_15 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_10, fixed_rowD_typed_coeff_15]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_10, fixed_rowD_typed_coeff_15]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_10, fixed_rowD_typed_coeff_15]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_15 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_10 _ (by omega),
              fixed_reversedU_typed_tail_10 _ (by omega), fixed_reversedU_typed_tail_10 _ hn',
              fixed_rowD_typed_tail_15 _ (by omega)]
            decide

theorem fixed_rowD_typed_15 : rowD 1 15 = fixedRowDData_15 := by
  calc
    rowD 1 15 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_10 :=
      fixedTyped_rowD_of_parameters 1 15 2 63 10 (1)
        fixedChebyshevUData_10 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_10
    _ = fixedRowDData_15 := by
      rw [fixed_reversedU_typed_data_10, fixed_rowD_typed_factor_15]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow16
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_16 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 50 (2048 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-4096 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-4096 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (12288 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (768 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-13824 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (3328 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (7168 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-2744 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-1680 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (768 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (144 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-71 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_16 (n : ℕ) : ℤ :=
    (if 50 = n then (2048 : ℤ) else 0) +
    (if 51 = n then (-4096 : ℤ) else 0) +
    (if 52 = n then (-4096 : ℤ) else 0) +
    (if 53 = n then (12288 : ℤ) else 0) +
    (if 54 = n then (768 : ℤ) else 0) +
    (if 55 = n then (-13824 : ℤ) else 0) +
    (if 56 = n then (3328 : ℤ) else 0) +
    (if 57 = n then (7168 : ℤ) else 0) +
    (if 58 = n then (-2744 : ℤ) else 0) +
    (if 59 = n then (-1680 : ℤ) else 0) +
    (if 60 = n then (768 : ℤ) else 0) +
    (if 61 = n then (144 : ℤ) else 0) +
    (if 62 = n then (-71 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_16 (n : ℕ) :
    fixedRowPData_16.coeff n = fixedRowPCoeff_16 n := by
  simp only [fixedRowPData_16, fixedRowPCoeff_16, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_16 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_16 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_16, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_16 : ∀ k : Fin 63,
    fixedReversedTCoeff_12 (k.val + 2) - 2 * fixedReversedTCoeff_12 (k.val + 1) + fixedReversedTCoeff_12 k.val = fixedRowPCoeff_16 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_16 :
    (1 - X) ^ 2 * fixedReversedTData_12 = fixedRowPData_16 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_12, fixed_rowP_typed_coeff_16]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_12, fixed_rowP_typed_coeff_16]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_12, fixed_rowP_typed_coeff_16]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_16 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_12 _ (by omega),
              fixed_reversedT_typed_tail_12 _ (by omega), fixed_reversedT_typed_tail_12 _ hn',
              fixed_rowP_typed_tail_16 _ (by omega)]
            decide

theorem fixed_rowP_typed_16 : rowP 1 16 = fixedRowPData_16 := by
  calc
    rowP 1 16 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_12 :=
      fixedTyped_rowP_of_parameters 1 16 2 63 12 fixedChebyshevTData_12
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_12
    _ = fixedRowPData_16 := by
      rw [fixed_reversedT_typed_data_12, fixed_rowP_typed_factor_16]

def fixedRowDData_16 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 51 (2048 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-4096 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-3072 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (10240 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-512 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-9216 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (2816 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (3584 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-1512 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-560 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (268 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (24 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-12 : ℤ)

def fixedRowDCoeff_16 (n : ℕ) : ℤ :=
    (if 51 = n then (2048 : ℤ) else 0) +
    (if 52 = n then (-4096 : ℤ) else 0) +
    (if 53 = n then (-3072 : ℤ) else 0) +
    (if 54 = n then (10240 : ℤ) else 0) +
    (if 55 = n then (-512 : ℤ) else 0) +
    (if 56 = n then (-9216 : ℤ) else 0) +
    (if 57 = n then (2816 : ℤ) else 0) +
    (if 58 = n then (3584 : ℤ) else 0) +
    (if 59 = n then (-1512 : ℤ) else 0) +
    (if 60 = n then (-560 : ℤ) else 0) +
    (if 61 = n then (268 : ℤ) else 0) +
    (if 62 = n then (24 : ℤ) else 0) +
    (if 63 = n then (-12 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_16 (n : ℕ) :
    fixedRowDData_16.coeff n = fixedRowDCoeff_16 n := by
  simp only [fixedRowDData_16, fixedRowDCoeff_16, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_16 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_16 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_16, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_16 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_11 (k.val + 2) - 2 * fixedReversedUCoeff_11 (k.val + 1) + fixedReversedUCoeff_11 k.val) = fixedRowDCoeff_16 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_16 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_11 = fixedRowDData_16 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_11, fixed_rowD_typed_coeff_16]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_11, fixed_rowD_typed_coeff_16]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_11, fixed_rowD_typed_coeff_16]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_16 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_11 _ (by omega),
              fixed_reversedU_typed_tail_11 _ (by omega), fixed_reversedU_typed_tail_11 _ hn',
              fixed_rowD_typed_tail_16 _ (by omega)]
            decide

theorem fixed_rowD_typed_16 : rowD 1 16 = fixedRowDData_16 := by
  calc
    rowD 1 16 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_11 :=
      fixedTyped_rowD_of_parameters 1 16 2 63 11 (1)
        fixedChebyshevUData_11 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_11
    _ = fixedRowDData_16 := by
      rw [fixed_reversedU_typed_data_11, fixed_rowD_typed_factor_16]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow17
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_17 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 49 (4096 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-8192 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-9216 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (26624 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (3328 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-33280 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (6656 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (19968 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-7072 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-5824 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (2548 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (728 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-351 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-26 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (13 : ℤ)

def fixedRowPCoeff_17 (n : ℕ) : ℤ :=
    (if 49 = n then (4096 : ℤ) else 0) +
    (if 50 = n then (-8192 : ℤ) else 0) +
    (if 51 = n then (-9216 : ℤ) else 0) +
    (if 52 = n then (26624 : ℤ) else 0) +
    (if 53 = n then (3328 : ℤ) else 0) +
    (if 54 = n then (-33280 : ℤ) else 0) +
    (if 55 = n then (6656 : ℤ) else 0) +
    (if 56 = n then (19968 : ℤ) else 0) +
    (if 57 = n then (-7072 : ℤ) else 0) +
    (if 58 = n then (-5824 : ℤ) else 0) +
    (if 59 = n then (2548 : ℤ) else 0) +
    (if 60 = n then (728 : ℤ) else 0) +
    (if 61 = n then (-351 : ℤ) else 0) +
    (if 62 = n then (-26 : ℤ) else 0) +
    (if 63 = n then (13 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_17 (n : ℕ) :
    fixedRowPData_17.coeff n = fixedRowPCoeff_17 n := by
  simp only [fixedRowPData_17, fixedRowPCoeff_17, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_17 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_17 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_17, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_17 : ∀ k : Fin 63,
    fixedReversedTCoeff_13 (k.val + 2) - 2 * fixedReversedTCoeff_13 (k.val + 1) + fixedReversedTCoeff_13 k.val = fixedRowPCoeff_17 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_17 :
    (1 - X) ^ 2 * fixedReversedTData_13 = fixedRowPData_17 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_13, fixed_rowP_typed_coeff_17]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_13, fixed_rowP_typed_coeff_17]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_13, fixed_rowP_typed_coeff_17]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_17 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_13 _ (by omega),
              fixed_reversedT_typed_tail_13 _ (by omega), fixed_reversedT_typed_tail_13 _ hn',
              fixed_rowP_typed_tail_17 _ (by omega)]
            decide

theorem fixed_rowP_typed_17 : rowP 1 17 = fixedRowPData_17 := by
  calc
    rowP 1 17 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_13 :=
      fixedTyped_rowP_of_parameters 1 17 2 63 13 fixedChebyshevTData_13
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_13
    _ = fixedRowPData_17 := by
      rw [fixed_reversedT_typed_data_13, fixed_rowP_typed_factor_17]

def fixedRowDData_17 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 50 (4096 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-8192 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-7168 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (22528 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (256 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-23040 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (6144 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (10752 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-4256 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-2240 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (1036 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (168 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-83 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowDCoeff_17 (n : ℕ) : ℤ :=
    (if 50 = n then (4096 : ℤ) else 0) +
    (if 51 = n then (-8192 : ℤ) else 0) +
    (if 52 = n then (-7168 : ℤ) else 0) +
    (if 53 = n then (22528 : ℤ) else 0) +
    (if 54 = n then (256 : ℤ) else 0) +
    (if 55 = n then (-23040 : ℤ) else 0) +
    (if 56 = n then (6144 : ℤ) else 0) +
    (if 57 = n then (10752 : ℤ) else 0) +
    (if 58 = n then (-4256 : ℤ) else 0) +
    (if 59 = n then (-2240 : ℤ) else 0) +
    (if 60 = n then (1036 : ℤ) else 0) +
    (if 61 = n then (168 : ℤ) else 0) +
    (if 62 = n then (-83 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_17 (n : ℕ) :
    fixedRowDData_17.coeff n = fixedRowDCoeff_17 n := by
  simp only [fixedRowDData_17, fixedRowDCoeff_17, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_17 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_17 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_17, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_17 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_12 (k.val + 2) - 2 * fixedReversedUCoeff_12 (k.val + 1) + fixedReversedUCoeff_12 k.val) = fixedRowDCoeff_17 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_17 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_12 = fixedRowDData_17 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_12, fixed_rowD_typed_coeff_17]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_12, fixed_rowD_typed_coeff_17]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_12, fixed_rowD_typed_coeff_17]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_17 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_12 _ (by omega),
              fixed_reversedU_typed_tail_12 _ (by omega), fixed_reversedU_typed_tail_12 _ hn',
              fixed_rowD_typed_tail_17 _ (by omega)]
            decide

theorem fixed_rowD_typed_17 : rowD 1 17 = fixedRowDData_17 := by
  calc
    rowD 1 17 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_12 :=
      fixedTyped_rowD_of_parameters 1 17 2 63 12 (1)
        fixedChebyshevUData_12 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_12
    _ = fixedRowDData_17 := by
      rw [fixed_reversedU_typed_data_12, fixed_rowD_typed_factor_17]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow18
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_18 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 48 (8192 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-16384 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-20480 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (57344 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (10752 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-78848 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (12544 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (53760 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-17472 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-18816 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (7840 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (3136 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-1470 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-196 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (97 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowPCoeff_18 (n : ℕ) : ℤ :=
    (if 48 = n then (8192 : ℤ) else 0) +
    (if 49 = n then (-16384 : ℤ) else 0) +
    (if 50 = n then (-20480 : ℤ) else 0) +
    (if 51 = n then (57344 : ℤ) else 0) +
    (if 52 = n then (10752 : ℤ) else 0) +
    (if 53 = n then (-78848 : ℤ) else 0) +
    (if 54 = n then (12544 : ℤ) else 0) +
    (if 55 = n then (53760 : ℤ) else 0) +
    (if 56 = n then (-17472 : ℤ) else 0) +
    (if 57 = n then (-18816 : ℤ) else 0) +
    (if 58 = n then (7840 : ℤ) else 0) +
    (if 59 = n then (3136 : ℤ) else 0) +
    (if 60 = n then (-1470 : ℤ) else 0) +
    (if 61 = n then (-196 : ℤ) else 0) +
    (if 62 = n then (97 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_18 (n : ℕ) :
    fixedRowPData_18.coeff n = fixedRowPCoeff_18 n := by
  simp only [fixedRowPData_18, fixedRowPCoeff_18, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_18 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_18 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_18, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_18 : ∀ k : Fin 63,
    fixedReversedTCoeff_14 (k.val + 2) - 2 * fixedReversedTCoeff_14 (k.val + 1) + fixedReversedTCoeff_14 k.val = fixedRowPCoeff_18 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_18 :
    (1 - X) ^ 2 * fixedReversedTData_14 = fixedRowPData_18 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_14, fixed_rowP_typed_coeff_18]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_14, fixed_rowP_typed_coeff_18]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_14, fixed_rowP_typed_coeff_18]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_18 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_14 _ (by omega),
              fixed_reversedT_typed_tail_14 _ (by omega), fixed_reversedT_typed_tail_14 _ hn',
              fixed_rowP_typed_tail_18 _ (by omega)]
            decide

theorem fixed_rowP_typed_18 : rowP 1 18 = fixedRowPData_18 := by
  calc
    rowP 1 18 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_14 :=
      fixedTyped_rowP_of_parameters 1 18 2 63 14 fixedChebyshevTData_14
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_14
    _ = fixedRowPData_18 := by
      rw [fixed_reversedT_typed_data_14, fixed_rowP_typed_factor_18]

def fixedRowDData_18 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 49 (8192 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-16384 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-16384 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (49152 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (3584 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-56320 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (12800 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (30720 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-11328 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-8064 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (3584 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (896 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-434 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-28 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (14 : ℤ)

def fixedRowDCoeff_18 (n : ℕ) : ℤ :=
    (if 49 = n then (8192 : ℤ) else 0) +
    (if 50 = n then (-16384 : ℤ) else 0) +
    (if 51 = n then (-16384 : ℤ) else 0) +
    (if 52 = n then (49152 : ℤ) else 0) +
    (if 53 = n then (3584 : ℤ) else 0) +
    (if 54 = n then (-56320 : ℤ) else 0) +
    (if 55 = n then (12800 : ℤ) else 0) +
    (if 56 = n then (30720 : ℤ) else 0) +
    (if 57 = n then (-11328 : ℤ) else 0) +
    (if 58 = n then (-8064 : ℤ) else 0) +
    (if 59 = n then (3584 : ℤ) else 0) +
    (if 60 = n then (896 : ℤ) else 0) +
    (if 61 = n then (-434 : ℤ) else 0) +
    (if 62 = n then (-28 : ℤ) else 0) +
    (if 63 = n then (14 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_18 (n : ℕ) :
    fixedRowDData_18.coeff n = fixedRowDCoeff_18 n := by
  simp only [fixedRowDData_18, fixedRowDCoeff_18, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_18 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_18 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_18, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_18 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_13 (k.val + 2) - 2 * fixedReversedUCoeff_13 (k.val + 1) + fixedReversedUCoeff_13 k.val) = fixedRowDCoeff_18 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_18 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_13 = fixedRowDData_18 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_13, fixed_rowD_typed_coeff_18]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_13, fixed_rowD_typed_coeff_18]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_13, fixed_rowD_typed_coeff_18]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_18 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_13 _ (by omega),
              fixed_reversedU_typed_tail_13 _ (by omega), fixed_reversedU_typed_tail_13 _ hn',
              fixed_rowD_typed_tail_18 _ (by omega)]
            decide

theorem fixed_rowD_typed_18 : rowD 1 18 = fixedRowDData_18 := by
  calc
    rowD 1 18 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_13 :=
      fixedTyped_rowD_of_parameters 1 18 2 63 13 (1)
        fixedChebyshevUData_13 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_13
    _ = fixedRowDData_18 := by
      rw [fixed_reversedU_typed_data_13, fixed_rowD_typed_factor_18]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.FixedCompactReversedT16To23
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedReversedTData_16 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-128 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (2688 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-21504 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (84480 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-180224 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (212992 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-131072 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (32768 : ℤ)

def fixedReversedTCoeff_16 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-128 : ℤ) else 0) +
    (if 58 = n then (2688 : ℤ) else 0) +
    (if 56 = n then (-21504 : ℤ) else 0) +
    (if 54 = n then (84480 : ℤ) else 0) +
    (if 52 = n then (-180224 : ℤ) else 0) +
    (if 50 = n then (212992 : ℤ) else 0) +
    (if 48 = n then (-131072 : ℤ) else 0) +
    (if 46 = n then (32768 : ℤ) else 0)

theorem fixed_reversedT_typed_data_16 : reversedRow 63 fixedChebyshevTData_16 = fixedReversedTData_16 := by
  simp only [fixedChebyshevTData_16, fixedReversedTData_16, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-128 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (2688 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-21504 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (84480 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-180224 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (212992 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-131072 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (32768 : ℤ) 16 (by decide)]

theorem fixed_reversedT_typed_coeff_16 (n : ℕ) :
    fixedReversedTData_16.coeff n = fixedReversedTCoeff_16 n := by
  simp only [fixedReversedTData_16, fixedReversedTCoeff_16, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_16 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_16 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_16, if_neg, add_zero]

def fixedReversedTData_17 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (17 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-816 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (11424 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-71808 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (239360 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-452608 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (487424 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-278528 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (65536 : ℤ)

def fixedReversedTCoeff_17 (n : ℕ) : ℤ :=
    (if 61 = n then (17 : ℤ) else 0) +
    (if 59 = n then (-816 : ℤ) else 0) +
    (if 57 = n then (11424 : ℤ) else 0) +
    (if 55 = n then (-71808 : ℤ) else 0) +
    (if 53 = n then (239360 : ℤ) else 0) +
    (if 51 = n then (-452608 : ℤ) else 0) +
    (if 49 = n then (487424 : ℤ) else 0) +
    (if 47 = n then (-278528 : ℤ) else 0) +
    (if 45 = n then (65536 : ℤ) else 0)

theorem fixed_reversedT_typed_data_17 : reversedRow 63 fixedChebyshevTData_17 = fixedReversedTData_17 := by
  simp only [fixedChebyshevTData_17, fixedReversedTData_17, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (17 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-816 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (11424 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-71808 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (239360 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-452608 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (487424 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-278528 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (65536 : ℤ) 17 (by decide)]

theorem fixed_reversedT_typed_coeff_17 (n : ℕ) :
    fixedReversedTData_17.coeff n = fixedReversedTCoeff_17 n := by
  simp only [fixedReversedTData_17, fixedReversedTCoeff_17, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_17 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_17 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_17, if_neg, add_zero]

def fixedReversedTData_18 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (162 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-4320 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (44352 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-228096 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (658944 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-1118208 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (1105920 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-589824 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (131072 : ℤ)

def fixedReversedTCoeff_18 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (162 : ℤ) else 0) +
    (if 58 = n then (-4320 : ℤ) else 0) +
    (if 56 = n then (44352 : ℤ) else 0) +
    (if 54 = n then (-228096 : ℤ) else 0) +
    (if 52 = n then (658944 : ℤ) else 0) +
    (if 50 = n then (-1118208 : ℤ) else 0) +
    (if 48 = n then (1105920 : ℤ) else 0) +
    (if 46 = n then (-589824 : ℤ) else 0) +
    (if 44 = n then (131072 : ℤ) else 0)

theorem fixed_reversedT_typed_data_18 : reversedRow 63 fixedChebyshevTData_18 = fixedReversedTData_18 := by
  simp only [fixedChebyshevTData_18, fixedReversedTData_18, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (162 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-4320 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (44352 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-228096 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (658944 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-1118208 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (1105920 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-589824 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (131072 : ℤ) 18 (by decide)]

theorem fixed_reversedT_typed_coeff_18 (n : ℕ) :
    fixedReversedTData_18.coeff n = fixedReversedTCoeff_18 n := by
  simp only [fixedReversedTData_18, fixedReversedTCoeff_18, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_18 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_18 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_18, if_neg, add_zero]

def fixedReversedTData_19 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-19 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (1140 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-20064 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (160512 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-695552 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (1770496 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-2723840 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (2490368 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-1245184 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (262144 : ℤ)

def fixedReversedTCoeff_19 (n : ℕ) : ℤ :=
    (if 61 = n then (-19 : ℤ) else 0) +
    (if 59 = n then (1140 : ℤ) else 0) +
    (if 57 = n then (-20064 : ℤ) else 0) +
    (if 55 = n then (160512 : ℤ) else 0) +
    (if 53 = n then (-695552 : ℤ) else 0) +
    (if 51 = n then (1770496 : ℤ) else 0) +
    (if 49 = n then (-2723840 : ℤ) else 0) +
    (if 47 = n then (2490368 : ℤ) else 0) +
    (if 45 = n then (-1245184 : ℤ) else 0) +
    (if 43 = n then (262144 : ℤ) else 0)

theorem fixed_reversedT_typed_data_19 : reversedRow 63 fixedChebyshevTData_19 = fixedReversedTData_19 := by
  simp only [fixedChebyshevTData_19, fixedReversedTData_19, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-19 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (1140 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-20064 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (160512 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-695552 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (1770496 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-2723840 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (2490368 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-1245184 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (262144 : ℤ) 19 (by decide)]

theorem fixed_reversedT_typed_coeff_19 (n : ℕ) :
    fixedReversedTData_19.coeff n = fixedReversedTCoeff_19 n := by
  simp only [fixedReversedTData_19, fixedReversedTCoeff_19, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_19 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_19 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_19, if_neg, add_zero]





















end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.FixedCompactReversedU16To23
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedReversedUData_16 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-144 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (3360 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-29568 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (126720 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-292864 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (372736 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-245760 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (65536 : ℤ)

def fixedReversedUCoeff_16 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-144 : ℤ) else 0) +
    (if 58 = n then (3360 : ℤ) else 0) +
    (if 56 = n then (-29568 : ℤ) else 0) +
    (if 54 = n then (126720 : ℤ) else 0) +
    (if 52 = n then (-292864 : ℤ) else 0) +
    (if 50 = n then (372736 : ℤ) else 0) +
    (if 48 = n then (-245760 : ℤ) else 0) +
    (if 46 = n then (65536 : ℤ) else 0)

theorem fixed_reversedU_typed_data_16 : reversedRow 63 fixedChebyshevUData_16 = fixedReversedUData_16 := by
  simp only [fixedChebyshevUData_16, fixedReversedUData_16, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-144 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (3360 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-29568 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (126720 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-292864 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (372736 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-245760 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (65536 : ℤ) 16 (by decide)]

theorem fixed_reversedU_typed_coeff_16 (n : ℕ) :
    fixedReversedUData_16.coeff n = fixedReversedUCoeff_16 n := by
  simp only [fixedReversedUData_16, fixedReversedUCoeff_16, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_16 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_16 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_16, if_neg, add_zero]

def fixedReversedUData_17 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (18 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-960 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (14784 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-101376 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (366080 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-745472 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (860160 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-524288 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (131072 : ℤ)

def fixedReversedUCoeff_17 (n : ℕ) : ℤ :=
    (if 61 = n then (18 : ℤ) else 0) +
    (if 59 = n then (-960 : ℤ) else 0) +
    (if 57 = n then (14784 : ℤ) else 0) +
    (if 55 = n then (-101376 : ℤ) else 0) +
    (if 53 = n then (366080 : ℤ) else 0) +
    (if 51 = n then (-745472 : ℤ) else 0) +
    (if 49 = n then (860160 : ℤ) else 0) +
    (if 47 = n then (-524288 : ℤ) else 0) +
    (if 45 = n then (131072 : ℤ) else 0)

theorem fixed_reversedU_typed_data_17 : reversedRow 63 fixedChebyshevUData_17 = fixedReversedUData_17 := by
  simp only [fixedChebyshevUData_17, fixedReversedUData_17, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (18 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-960 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (14784 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-101376 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (366080 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-745472 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (860160 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-524288 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (131072 : ℤ) 17 (by decide)]

theorem fixed_reversedU_typed_coeff_17 (n : ℕ) :
    fixedReversedUData_17.coeff n = fixedReversedUCoeff_17 n := by
  simp only [fixedReversedUData_17, fixedReversedUCoeff_17, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_17 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_17 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_17, if_neg, add_zero]

def fixedReversedUData_18 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (180 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-5280 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (59136 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-329472 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (1025024 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-1863680 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (1966080 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-1114112 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (262144 : ℤ)

def fixedReversedUCoeff_18 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (180 : ℤ) else 0) +
    (if 58 = n then (-5280 : ℤ) else 0) +
    (if 56 = n then (59136 : ℤ) else 0) +
    (if 54 = n then (-329472 : ℤ) else 0) +
    (if 52 = n then (1025024 : ℤ) else 0) +
    (if 50 = n then (-1863680 : ℤ) else 0) +
    (if 48 = n then (1966080 : ℤ) else 0) +
    (if 46 = n then (-1114112 : ℤ) else 0) +
    (if 44 = n then (262144 : ℤ) else 0)

theorem fixed_reversedU_typed_data_18 : reversedRow 63 fixedChebyshevUData_18 = fixedReversedUData_18 := by
  simp only [fixedChebyshevUData_18, fixedReversedUData_18, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (180 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-5280 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (59136 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-329472 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (1025024 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-1863680 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (1966080 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-1114112 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (262144 : ℤ) 18 (by decide)]

theorem fixed_reversedU_typed_coeff_18 (n : ℕ) :
    fixedReversedUData_18.coeff n = fixedReversedUCoeff_18 n := by
  simp only [fixedReversedUData_18, fixedReversedUCoeff_18, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_18 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_18 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_18, if_neg, add_zero]


























end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow21
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_21 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 45 (65536 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-131072 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-212992 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (557056 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (208896 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-974848 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (34816 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (905216 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-213248 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-478720 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (167552 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (143616 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-60384 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-22848 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (10608 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (1632 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-799 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-34 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (17 : ℤ)

def fixedRowPCoeff_21 (n : ℕ) : ℤ :=
    (if 45 = n then (65536 : ℤ) else 0) +
    (if 46 = n then (-131072 : ℤ) else 0) +
    (if 47 = n then (-212992 : ℤ) else 0) +
    (if 48 = n then (557056 : ℤ) else 0) +
    (if 49 = n then (208896 : ℤ) else 0) +
    (if 50 = n then (-974848 : ℤ) else 0) +
    (if 51 = n then (34816 : ℤ) else 0) +
    (if 52 = n then (905216 : ℤ) else 0) +
    (if 53 = n then (-213248 : ℤ) else 0) +
    (if 54 = n then (-478720 : ℤ) else 0) +
    (if 55 = n then (167552 : ℤ) else 0) +
    (if 56 = n then (143616 : ℤ) else 0) +
    (if 57 = n then (-60384 : ℤ) else 0) +
    (if 58 = n then (-22848 : ℤ) else 0) +
    (if 59 = n then (10608 : ℤ) else 0) +
    (if 60 = n then (1632 : ℤ) else 0) +
    (if 61 = n then (-799 : ℤ) else 0) +
    (if 62 = n then (-34 : ℤ) else 0) +
    (if 63 = n then (17 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_21 (n : ℕ) :
    fixedRowPData_21.coeff n = fixedRowPCoeff_21 n := by
  simp only [fixedRowPData_21, fixedRowPCoeff_21, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_21 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_21 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_21, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_21 : ∀ k : Fin 63,
    fixedReversedTCoeff_17 (k.val + 2) - 2 * fixedReversedTCoeff_17 (k.val + 1) + fixedReversedTCoeff_17 k.val = fixedRowPCoeff_21 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_21 :
    (1 - X) ^ 2 * fixedReversedTData_17 = fixedRowPData_21 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_17, fixed_rowP_typed_coeff_21]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_17, fixed_rowP_typed_coeff_21]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_17, fixed_rowP_typed_coeff_21]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_21 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_17 _ (by omega),
              fixed_reversedT_typed_tail_17 _ (by omega), fixed_reversedT_typed_tail_17 _ hn',
              fixed_rowP_typed_tail_21 _ (by omega)]
            decide

theorem fixed_rowP_typed_21 : rowP 1 21 = fixedRowPData_21 := by
  calc
    rowP 1 21 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_17 :=
      fixedTyped_rowP_of_parameters 1 21 2 63 17 fixedChebyshevTData_17
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_17
    _ = fixedRowPData_21 := by
      rw [fixed_reversedT_typed_data_17, fixed_rowP_typed_factor_21]

def fixedRowDData_21 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 46 (65536 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-131072 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-180224 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (491520 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (126976 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-745472 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (79872 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (585728 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-166144 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-253440 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (97152 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (59136 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-26208 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-6720 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (3216 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (288 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-143 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowDCoeff_21 (n : ℕ) : ℤ :=
    (if 46 = n then (65536 : ℤ) else 0) +
    (if 47 = n then (-131072 : ℤ) else 0) +
    (if 48 = n then (-180224 : ℤ) else 0) +
    (if 49 = n then (491520 : ℤ) else 0) +
    (if 50 = n then (126976 : ℤ) else 0) +
    (if 51 = n then (-745472 : ℤ) else 0) +
    (if 52 = n then (79872 : ℤ) else 0) +
    (if 53 = n then (585728 : ℤ) else 0) +
    (if 54 = n then (-166144 : ℤ) else 0) +
    (if 55 = n then (-253440 : ℤ) else 0) +
    (if 56 = n then (97152 : ℤ) else 0) +
    (if 57 = n then (59136 : ℤ) else 0) +
    (if 58 = n then (-26208 : ℤ) else 0) +
    (if 59 = n then (-6720 : ℤ) else 0) +
    (if 60 = n then (3216 : ℤ) else 0) +
    (if 61 = n then (288 : ℤ) else 0) +
    (if 62 = n then (-143 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_21 (n : ℕ) :
    fixedRowDData_21.coeff n = fixedRowDCoeff_21 n := by
  simp only [fixedRowDData_21, fixedRowDCoeff_21, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_21 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_21 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_21, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_21 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_16 (k.val + 2) - 2 * fixedReversedUCoeff_16 (k.val + 1) + fixedReversedUCoeff_16 k.val) = fixedRowDCoeff_21 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_21 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_16 = fixedRowDData_21 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_16, fixed_rowD_typed_coeff_21]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_16, fixed_rowD_typed_coeff_21]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_16, fixed_rowD_typed_coeff_21]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_21 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_16 _ (by omega),
              fixed_reversedU_typed_tail_16 _ (by omega), fixed_reversedU_typed_tail_16 _ hn',
              fixed_rowD_typed_tail_21 _ (by omega)]
            decide

theorem fixed_rowD_typed_21 : rowD 1 21 = fixedRowDData_21 := by
  calc
    rowD 1 21 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_16 :=
      fixedTyped_rowD_of_parameters 1 21 2 63 16 (1)
        fixedChebyshevUData_16 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_16
    _ = fixedRowDData_21 := by
      rw [fixed_reversedU_typed_data_16, fixed_rowD_typed_factor_21]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow22
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_22 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 44 (131072 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-262144 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-458752 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (1179648 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (516096 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-2211840 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-12288 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (2236416 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-459264 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-1317888 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (430848 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (456192 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-183744 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-88704 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (40032 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (8640 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-4158 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-324 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (161 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowPCoeff_22 (n : ℕ) : ℤ :=
    (if 44 = n then (131072 : ℤ) else 0) +
    (if 45 = n then (-262144 : ℤ) else 0) +
    (if 46 = n then (-458752 : ℤ) else 0) +
    (if 47 = n then (1179648 : ℤ) else 0) +
    (if 48 = n then (516096 : ℤ) else 0) +
    (if 49 = n then (-2211840 : ℤ) else 0) +
    (if 50 = n then (-12288 : ℤ) else 0) +
    (if 51 = n then (2236416 : ℤ) else 0) +
    (if 52 = n then (-459264 : ℤ) else 0) +
    (if 53 = n then (-1317888 : ℤ) else 0) +
    (if 54 = n then (430848 : ℤ) else 0) +
    (if 55 = n then (456192 : ℤ) else 0) +
    (if 56 = n then (-183744 : ℤ) else 0) +
    (if 57 = n then (-88704 : ℤ) else 0) +
    (if 58 = n then (40032 : ℤ) else 0) +
    (if 59 = n then (8640 : ℤ) else 0) +
    (if 60 = n then (-4158 : ℤ) else 0) +
    (if 61 = n then (-324 : ℤ) else 0) +
    (if 62 = n then (161 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_22 (n : ℕ) :
    fixedRowPData_22.coeff n = fixedRowPCoeff_22 n := by
  simp only [fixedRowPData_22, fixedRowPCoeff_22, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_22 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_22 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_22, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_22 : ∀ k : Fin 63,
    fixedReversedTCoeff_18 (k.val + 2) - 2 * fixedReversedTCoeff_18 (k.val + 1) + fixedReversedTCoeff_18 k.val = fixedRowPCoeff_22 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_22 :
    (1 - X) ^ 2 * fixedReversedTData_18 = fixedRowPData_22 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_18, fixed_rowP_typed_coeff_22]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_18, fixed_rowP_typed_coeff_22]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_18, fixed_rowP_typed_coeff_22]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_22 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_18 _ (by omega),
              fixed_reversedT_typed_tail_18 _ (by omega), fixed_reversedT_typed_tail_18 _ hn',
              fixed_rowP_typed_tail_22 _ (by omega)]
            decide

theorem fixed_rowP_typed_22 : rowP 1 22 = fixedRowPData_22 := by
  calc
    rowP 1 22 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_18 :=
      fixedTyped_rowP_of_parameters 1 22 2 63 18 fixedChebyshevTData_18
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_18
    _ = fixedRowPData_22 := by
      rw [fixed_reversedT_typed_data_18, fixed_rowP_typed_factor_22]

def fixedRowDData_22 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 45 (131072 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-262144 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-393216 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (1048576 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (335872 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-1720320 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (114688 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (1490944 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-379392 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-732160 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (264704 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (202752 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-86592 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-29568 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (13824 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (1920 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-942 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-36 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (18 : ℤ)

def fixedRowDCoeff_22 (n : ℕ) : ℤ :=
    (if 45 = n then (131072 : ℤ) else 0) +
    (if 46 = n then (-262144 : ℤ) else 0) +
    (if 47 = n then (-393216 : ℤ) else 0) +
    (if 48 = n then (1048576 : ℤ) else 0) +
    (if 49 = n then (335872 : ℤ) else 0) +
    (if 50 = n then (-1720320 : ℤ) else 0) +
    (if 51 = n then (114688 : ℤ) else 0) +
    (if 52 = n then (1490944 : ℤ) else 0) +
    (if 53 = n then (-379392 : ℤ) else 0) +
    (if 54 = n then (-732160 : ℤ) else 0) +
    (if 55 = n then (264704 : ℤ) else 0) +
    (if 56 = n then (202752 : ℤ) else 0) +
    (if 57 = n then (-86592 : ℤ) else 0) +
    (if 58 = n then (-29568 : ℤ) else 0) +
    (if 59 = n then (13824 : ℤ) else 0) +
    (if 60 = n then (1920 : ℤ) else 0) +
    (if 61 = n then (-942 : ℤ) else 0) +
    (if 62 = n then (-36 : ℤ) else 0) +
    (if 63 = n then (18 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_22 (n : ℕ) :
    fixedRowDData_22.coeff n = fixedRowDCoeff_22 n := by
  simp only [fixedRowDData_22, fixedRowDCoeff_22, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_22 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_22 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_22, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_22 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_17 (k.val + 2) - 2 * fixedReversedUCoeff_17 (k.val + 1) + fixedReversedUCoeff_17 k.val) = fixedRowDCoeff_22 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_22 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_17 = fixedRowDData_22 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_17, fixed_rowD_typed_coeff_22]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_17, fixed_rowD_typed_coeff_22]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_17, fixed_rowD_typed_coeff_22]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_22 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_17 _ (by omega),
              fixed_reversedU_typed_tail_17 _ (by omega), fixed_reversedU_typed_tail_17 _ hn',
              fixed_rowD_typed_tail_22 _ (by omega)]
            decide

theorem fixed_rowD_typed_22 : rowD 1 22 = fixedRowDData_22 := by
  calc
    rowD 1 22 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_17 :=
      fixedTyped_rowD_of_parameters 1 22 2 63 17 (1)
        fixedChebyshevUData_17 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_17
    _ = fixedRowDData_22 := by
      rw [fixed_reversedU_typed_data_17, fixed_rowD_typed_factor_22]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow23
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_23 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 43 (262144 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-524288 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-983040 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (2490368 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (1245184 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-4980736 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-233472 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (5447680 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-953344 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-3540992 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (1074944 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (1391104 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-535040 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-321024 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (140448 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (40128 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-18924 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-2280 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (1121 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (38 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-19 : ℤ)

def fixedRowPCoeff_23 (n : ℕ) : ℤ :=
    (if 43 = n then (262144 : ℤ) else 0) +
    (if 44 = n then (-524288 : ℤ) else 0) +
    (if 45 = n then (-983040 : ℤ) else 0) +
    (if 46 = n then (2490368 : ℤ) else 0) +
    (if 47 = n then (1245184 : ℤ) else 0) +
    (if 48 = n then (-4980736 : ℤ) else 0) +
    (if 49 = n then (-233472 : ℤ) else 0) +
    (if 50 = n then (5447680 : ℤ) else 0) +
    (if 51 = n then (-953344 : ℤ) else 0) +
    (if 52 = n then (-3540992 : ℤ) else 0) +
    (if 53 = n then (1074944 : ℤ) else 0) +
    (if 54 = n then (1391104 : ℤ) else 0) +
    (if 55 = n then (-535040 : ℤ) else 0) +
    (if 56 = n then (-321024 : ℤ) else 0) +
    (if 57 = n then (140448 : ℤ) else 0) +
    (if 58 = n then (40128 : ℤ) else 0) +
    (if 59 = n then (-18924 : ℤ) else 0) +
    (if 60 = n then (-2280 : ℤ) else 0) +
    (if 61 = n then (1121 : ℤ) else 0) +
    (if 62 = n then (38 : ℤ) else 0) +
    (if 63 = n then (-19 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_23 (n : ℕ) :
    fixedRowPData_23.coeff n = fixedRowPCoeff_23 n := by
  simp only [fixedRowPData_23, fixedRowPCoeff_23, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_23 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_23 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_23, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_23 : ∀ k : Fin 63,
    fixedReversedTCoeff_19 (k.val + 2) - 2 * fixedReversedTCoeff_19 (k.val + 1) + fixedReversedTCoeff_19 k.val = fixedRowPCoeff_23 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_23 :
    (1 - X) ^ 2 * fixedReversedTData_19 = fixedRowPData_23 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_19, fixed_rowP_typed_coeff_23]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_19, fixed_rowP_typed_coeff_23]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_19, fixed_rowP_typed_coeff_23]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_23 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_19 _ (by omega),
              fixed_reversedT_typed_tail_19 _ (by omega), fixed_reversedT_typed_tail_19 _ hn',
              fixed_rowP_typed_tail_23 _ (by omega)]
            decide

theorem fixed_rowP_typed_23 : rowP 1 23 = fixedRowPData_23 := by
  calc
    rowP 1 23 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_19 :=
      fixedTyped_rowP_of_parameters 1 23 2 63 19 fixedChebyshevTData_19
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_19
    _ = fixedRowPData_23 := by
      rw [fixed_reversedT_typed_data_19, fixed_rowP_typed_factor_23]

def fixedRowDData_23 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 44 (262144 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-524288 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-851968 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (2228224 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (851968 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-3932160 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (102400 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (3727360 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-838656 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-2050048 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (695552 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (658944 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-270336 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-118272 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (53856 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (10560 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-5100 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-360 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (179 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowDCoeff_23 (n : ℕ) : ℤ :=
    (if 44 = n then (262144 : ℤ) else 0) +
    (if 45 = n then (-524288 : ℤ) else 0) +
    (if 46 = n then (-851968 : ℤ) else 0) +
    (if 47 = n then (2228224 : ℤ) else 0) +
    (if 48 = n then (851968 : ℤ) else 0) +
    (if 49 = n then (-3932160 : ℤ) else 0) +
    (if 50 = n then (102400 : ℤ) else 0) +
    (if 51 = n then (3727360 : ℤ) else 0) +
    (if 52 = n then (-838656 : ℤ) else 0) +
    (if 53 = n then (-2050048 : ℤ) else 0) +
    (if 54 = n then (695552 : ℤ) else 0) +
    (if 55 = n then (658944 : ℤ) else 0) +
    (if 56 = n then (-270336 : ℤ) else 0) +
    (if 57 = n then (-118272 : ℤ) else 0) +
    (if 58 = n then (53856 : ℤ) else 0) +
    (if 59 = n then (10560 : ℤ) else 0) +
    (if 60 = n then (-5100 : ℤ) else 0) +
    (if 61 = n then (-360 : ℤ) else 0) +
    (if 62 = n then (179 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_23 (n : ℕ) :
    fixedRowDData_23.coeff n = fixedRowDCoeff_23 n := by
  simp only [fixedRowDData_23, fixedRowDCoeff_23, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_23 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_23 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_23, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_23 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_18 (k.val + 2) - 2 * fixedReversedUCoeff_18 (k.val + 1) + fixedReversedUCoeff_18 k.val) = fixedRowDCoeff_23 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_23 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_18 = fixedRowDData_23 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_18, fixed_rowD_typed_coeff_23]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_18, fixed_rowD_typed_coeff_23]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_18, fixed_rowD_typed_coeff_23]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_23 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_18 _ (by omega),
              fixed_reversedU_typed_tail_18 _ (by omega), fixed_reversedU_typed_tail_18 _ hn',
              fixed_rowD_typed_tail_23 _ (by omega)]
            decide

theorem fixed_rowD_typed_23 : rowD 1 23 = fixedRowDData_23 := by
  calc
    rowD 1 23 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_18 :=
      fixedTyped_rowD_of_parameters 1 23 2 63 18 (1)
        fixedChebyshevUData_18 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_18
    _ = fixedRowDData_23 := by
      rw [fixed_reversedU_typed_data_18, fixed_rowD_typed_factor_23]

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













end InternalCatalan

end

end

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_19 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 47 (16384 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-32768 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-45056 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (122880 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (30720 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-184320 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (21760 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (140800 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-41600 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-57600 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (22752 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (12096 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-5488 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-1120 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (545 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (30 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-15 : ℤ)

def fixedRowPCoeff_19 (n : ℕ) : ℤ :=
    (if 47 = n then (16384 : ℤ) else 0) +
    (if 48 = n then (-32768 : ℤ) else 0) +
    (if 49 = n then (-45056 : ℤ) else 0) +
    (if 50 = n then (122880 : ℤ) else 0) +
    (if 51 = n then (30720 : ℤ) else 0) +
    (if 52 = n then (-184320 : ℤ) else 0) +
    (if 53 = n then (21760 : ℤ) else 0) +
    (if 54 = n then (140800 : ℤ) else 0) +
    (if 55 = n then (-41600 : ℤ) else 0) +
    (if 56 = n then (-57600 : ℤ) else 0) +
    (if 57 = n then (22752 : ℤ) else 0) +
    (if 58 = n then (12096 : ℤ) else 0) +
    (if 59 = n then (-5488 : ℤ) else 0) +
    (if 60 = n then (-1120 : ℤ) else 0) +
    (if 61 = n then (545 : ℤ) else 0) +
    (if 62 = n then (30 : ℤ) else 0) +
    (if 63 = n then (-15 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_19 (n : ℕ) :
    fixedRowPData_19.coeff n = fixedRowPCoeff_19 n := by
  simp only [fixedRowPData_19, fixedRowPCoeff_19, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_19 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_19 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_19, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_19 : ∀ k : Fin 63,
    fixedReversedTCoeff_15 (k.val + 2) - 2 * fixedReversedTCoeff_15 (k.val + 1) + fixedReversedTCoeff_15 k.val = fixedRowPCoeff_19 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_19 :
    (1 - X) ^ 2 * fixedReversedTData_15 = fixedRowPData_19 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_15, fixed_rowP_typed_coeff_19]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_15, fixed_rowP_typed_coeff_19]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_15, fixed_rowP_typed_coeff_19]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_19 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_15 _ (by omega),
              fixed_reversedT_typed_tail_15 _ (by omega), fixed_reversedT_typed_tail_15 _ hn',
              fixed_rowP_typed_tail_19 _ (by omega)]
            decide

theorem fixed_rowP_typed_19 : rowP 1 19 = fixedRowPData_19 := by
  calc
    rowP 1 19 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_15 :=
      fixedTyped_rowP_of_parameters 1 19 2 63 15 fixedChebyshevTData_15
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_15
    _ = fixedRowPData_19 := by
      rw [fixed_reversedT_typed_data_15, fixed_rowP_typed_factor_19]

def fixedRowDData_19 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 48 (16384 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-32768 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-36864 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (106496 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (14336 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-135168 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (25344 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (84480 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-28800 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-26880 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (11424 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (4032 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-1904 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-224 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (111 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowDCoeff_19 (n : ℕ) : ℤ :=
    (if 48 = n then (16384 : ℤ) else 0) +
    (if 49 = n then (-32768 : ℤ) else 0) +
    (if 50 = n then (-36864 : ℤ) else 0) +
    (if 51 = n then (106496 : ℤ) else 0) +
    (if 52 = n then (14336 : ℤ) else 0) +
    (if 53 = n then (-135168 : ℤ) else 0) +
    (if 54 = n then (25344 : ℤ) else 0) +
    (if 55 = n then (84480 : ℤ) else 0) +
    (if 56 = n then (-28800 : ℤ) else 0) +
    (if 57 = n then (-26880 : ℤ) else 0) +
    (if 58 = n then (11424 : ℤ) else 0) +
    (if 59 = n then (4032 : ℤ) else 0) +
    (if 60 = n then (-1904 : ℤ) else 0) +
    (if 61 = n then (-224 : ℤ) else 0) +
    (if 62 = n then (111 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_19 (n : ℕ) :
    fixedRowDData_19.coeff n = fixedRowDCoeff_19 n := by
  simp only [fixedRowDData_19, fixedRowDCoeff_19, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_19 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_19 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_19, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_19 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_14 (k.val + 2) - 2 * fixedReversedUCoeff_14 (k.val + 1) + fixedReversedUCoeff_14 k.val) = fixedRowDCoeff_19 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_19 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_14 = fixedRowDData_19 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_14, fixed_rowD_typed_coeff_19]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_14, fixed_rowD_typed_coeff_19]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_14, fixed_rowD_typed_coeff_19]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_19 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_14 _ (by omega),
              fixed_reversedU_typed_tail_14 _ (by omega), fixed_reversedU_typed_tail_14 _ hn',
              fixed_rowD_typed_tail_19 _ (by omega)]
            decide

theorem fixed_rowD_typed_19 : rowD 1 19 = fixedRowDData_19 := by
  calc
    rowD 1 19 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_14 :=
      fixedTyped_rowD_of_parameters 1 19 2 63 14 (1)
        fixedChebyshevUData_14 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_14
    _ = fixedRowDData_19 := by
      rw [fixed_reversedU_typed_data_14, fixed_rowD_typed_factor_19]

end InternalCatalan

end

end

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_20 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 46 (32768 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-65536 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-98304 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (262144 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (81920 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-425984 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (32768 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (360448 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-95744 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-168960 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (62976 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (43008 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-18816 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-5376 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (2560 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (256 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-127 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_20 (n : ℕ) : ℤ :=
    (if 46 = n then (32768 : ℤ) else 0) +
    (if 47 = n then (-65536 : ℤ) else 0) +
    (if 48 = n then (-98304 : ℤ) else 0) +
    (if 49 = n then (262144 : ℤ) else 0) +
    (if 50 = n then (81920 : ℤ) else 0) +
    (if 51 = n then (-425984 : ℤ) else 0) +
    (if 52 = n then (32768 : ℤ) else 0) +
    (if 53 = n then (360448 : ℤ) else 0) +
    (if 54 = n then (-95744 : ℤ) else 0) +
    (if 55 = n then (-168960 : ℤ) else 0) +
    (if 56 = n then (62976 : ℤ) else 0) +
    (if 57 = n then (43008 : ℤ) else 0) +
    (if 58 = n then (-18816 : ℤ) else 0) +
    (if 59 = n then (-5376 : ℤ) else 0) +
    (if 60 = n then (2560 : ℤ) else 0) +
    (if 61 = n then (256 : ℤ) else 0) +
    (if 62 = n then (-127 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_20 (n : ℕ) :
    fixedRowPData_20.coeff n = fixedRowPCoeff_20 n := by
  simp only [fixedRowPData_20, fixedRowPCoeff_20, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_20 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_20 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_20, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_20 : ∀ k : Fin 63,
    fixedReversedTCoeff_16 (k.val + 2) - 2 * fixedReversedTCoeff_16 (k.val + 1) + fixedReversedTCoeff_16 k.val = fixedRowPCoeff_20 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_20 :
    (1 - X) ^ 2 * fixedReversedTData_16 = fixedRowPData_20 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_16, fixed_rowP_typed_coeff_20]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_16, fixed_rowP_typed_coeff_20]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_16, fixed_rowP_typed_coeff_20]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_20 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_16 _ (by omega),
              fixed_reversedT_typed_tail_16 _ (by omega), fixed_reversedT_typed_tail_16 _ hn',
              fixed_rowP_typed_tail_20 _ (by omega)]
            decide

theorem fixed_rowP_typed_20 : rowP 1 20 = fixedRowPData_20 := by
  calc
    rowP 1 20 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_16 :=
      fixedTyped_rowP_of_parameters 1 20 2 63 16 fixedChebyshevTData_16
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_16
    _ = fixedRowPData_20 := by
      rw [fixed_reversedT_typed_data_16, fixed_rowP_typed_factor_20]

def fixedRowDData_20 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 47 (32768 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-65536 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-81920 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (229376 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (45056 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-319488 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (47104 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (225280 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-70400 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-84480 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (34176 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (16128 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-7392 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-1344 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (656 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (32 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-16 : ℤ)

def fixedRowDCoeff_20 (n : ℕ) : ℤ :=
    (if 47 = n then (32768 : ℤ) else 0) +
    (if 48 = n then (-65536 : ℤ) else 0) +
    (if 49 = n then (-81920 : ℤ) else 0) +
    (if 50 = n then (229376 : ℤ) else 0) +
    (if 51 = n then (45056 : ℤ) else 0) +
    (if 52 = n then (-319488 : ℤ) else 0) +
    (if 53 = n then (47104 : ℤ) else 0) +
    (if 54 = n then (225280 : ℤ) else 0) +
    (if 55 = n then (-70400 : ℤ) else 0) +
    (if 56 = n then (-84480 : ℤ) else 0) +
    (if 57 = n then (34176 : ℤ) else 0) +
    (if 58 = n then (16128 : ℤ) else 0) +
    (if 59 = n then (-7392 : ℤ) else 0) +
    (if 60 = n then (-1344 : ℤ) else 0) +
    (if 61 = n then (656 : ℤ) else 0) +
    (if 62 = n then (32 : ℤ) else 0) +
    (if 63 = n then (-16 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_20 (n : ℕ) :
    fixedRowDData_20.coeff n = fixedRowDCoeff_20 n := by
  simp only [fixedRowDData_20, fixedRowDCoeff_20, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_20 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_20 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_20, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_20 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_15 (k.val + 2) - 2 * fixedReversedUCoeff_15 (k.val + 1) + fixedReversedUCoeff_15 k.val) = fixedRowDCoeff_20 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_20 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_15 = fixedRowDData_20 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_15, fixed_rowD_typed_coeff_20]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_15, fixed_rowD_typed_coeff_20]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_15, fixed_rowD_typed_coeff_20]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_20 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_15 _ (by omega),
              fixed_reversedU_typed_tail_15 _ (by omega), fixed_reversedU_typed_tail_15 _ hn',
              fixed_rowD_typed_tail_20 _ (by omega)]
            decide

theorem fixed_rowD_typed_20 : rowD 1 20 = fixedRowDData_20 := by
  calc
    rowD 1 20 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_15 :=
      fixedTyped_rowD_of_parameters 1 20 2 63 15 (1)
        fixedChebyshevUData_15 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_15
    _ = fixedRowDData_20 := by
      rw [fixed_reversedU_typed_data_15, fixed_rowD_typed_factor_20]

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
-- module Solutions.OAICatalan.Split.IntBaseRows12
namespace OAI

namespace InternalCatalan

theorem splitBaseMod_row_12 (k : Fin 48) :
    (fixedIntegerBaseCanonical (12 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (12 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (12 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_12 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_12 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 12).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 12).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_12, fixed_rowD_typed_12]
    simp only [fixed_rowP_typed_coeff_12, fixed_rowD_typed_coeff_12,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_13 (k : Fin 48) :
    (fixedIntegerBaseCanonical (13 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (13 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (13 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_13 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_13 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 13).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 13).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_13, fixed_rowD_typed_13]
    simp only [fixed_rowP_typed_coeff_13, fixed_rowD_typed_coeff_13,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_14 (k : Fin 48) :
    (fixedIntegerBaseCanonical (14 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (14 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (14 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_14 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_14 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 14).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 14).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_14, fixed_rowD_typed_14]
    simp only [fixed_rowP_typed_coeff_14, fixed_rowD_typed_coeff_14,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_15 (k : Fin 48) :
    (fixedIntegerBaseCanonical (15 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (15 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (15 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_15 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_15 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 15).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 15).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_15, fixed_rowD_typed_15]
    simp only [fixed_rowP_typed_coeff_15, fixed_rowD_typed_coeff_15,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_16 (k : Fin 48) :
    (fixedIntegerBaseCanonical (16 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (16 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (16 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_16 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_16 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 16).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 16).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_16, fixed_rowD_typed_16]
    simp only [fixed_rowP_typed_coeff_16, fixed_rowD_typed_coeff_16,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_17 (k : Fin 48) :
    (fixedIntegerBaseCanonical (17 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (17 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (17 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_17 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_17 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 17).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 17).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_17, fixed_rowD_typed_17]
    simp only [fixed_rowP_typed_coeff_17, fixed_rowD_typed_coeff_17,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_18 (k : Fin 48) :
    (fixedIntegerBaseCanonical (18 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (18 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (18 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_18 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_18 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 18).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 18).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_18, fixed_rowD_typed_18]
    simp only [fixed_rowP_typed_coeff_18, fixed_rowD_typed_coeff_18,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_19 (k : Fin 48) :
    (fixedIntegerBaseCanonical (19 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (19 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (19 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_19 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_19 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 19).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 19).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_19, fixed_rowD_typed_19]
    simp only [fixed_rowP_typed_coeff_19, fixed_rowD_typed_coeff_19,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_20 (k : Fin 48) :
    (fixedIntegerBaseCanonical (20 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (20 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (20 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_20 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_20 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 20).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 20).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_20, fixed_rowD_typed_20]
    simp only [fixed_rowP_typed_coeff_20, fixed_rowD_typed_coeff_20,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_21 (k : Fin 48) :
    (fixedIntegerBaseCanonical (21 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (21 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (21 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_21 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_21 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 21).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 21).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_21, fixed_rowD_typed_21]
    simp only [fixed_rowP_typed_coeff_21, fixed_rowD_typed_coeff_21,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_22 (k : Fin 48) :
    (fixedIntegerBaseCanonical (22 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (22 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (22 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_22 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_22 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 22).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 22).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_22, fixed_rowD_typed_22]
    simp only [fixed_rowP_typed_coeff_22, fixed_rowD_typed_coeff_22,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_23 (k : Fin 48) :
    (fixedIntegerBaseCanonical (23 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (23 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (23 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_23 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_23 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 23).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 23).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_23, fixed_rowD_typed_23]
    simp only [fixed_rowP_typed_coeff_23, fixed_rowD_typed_coeff_23,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem fixedIntegerBaseCanonical_mod101_rows_12_23 (r : Fin 49) (hr : 12 ≤ r.val ∧ r.val < 24)
    (k : Fin 48) :
    (fixedIntegerBaseCanonical r k : ZMod 101) = fixedLiteralBaseMod r k := by
  obtain ⟨r, hr'⟩ := r
  obtain ⟨hra, hrb⟩ := hr
  simp only at hra hrb
  interval_cases r
  · exact splitBaseMod_row_12 k
  · exact splitBaseMod_row_13 k
  · exact splitBaseMod_row_14 k
  · exact splitBaseMod_row_15 k
  · exact splitBaseMod_row_16 k
  · exact splitBaseMod_row_17 k
  · exact splitBaseMod_row_18 k
  · exact splitBaseMod_row_19 k
  · exact splitBaseMod_row_20 k
  · exact splitBaseMod_row_21 k
  · exact splitBaseMod_row_22 k
  · exact splitBaseMod_row_23 k

end InternalCatalan

end OAI

end

section
open OAI.InternalCatalan

theorem solution (r : Fin 49) (hr : 12 ≤ r.val ∧ r.val < 24)
    (k : Fin 48) :
    (fixedIntegerBaseCanonical r k : ZMod 101) = fixedLiteralBaseMod r k := by
  first
  | exact @OAI.InternalCatalan.fixedIntegerBaseCanonical_mod101_rows_12_23
  | (apply OAI.InternalCatalan.fixedIntegerBaseCanonical_mod101_rows_12_23 <;> assumption)

end
