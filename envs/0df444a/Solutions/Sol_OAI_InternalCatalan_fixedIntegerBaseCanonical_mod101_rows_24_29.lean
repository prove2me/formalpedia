-- Prove2me | solution 1 for OAI.InternalCatalan.fixedIntegerBaseCanonical_mod101_rows_24_29
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T19:18:26.394021+00:00
-- url     : https://prove2.me/submissions/952f02e2-04ee-419e-af14-da2f70c22ef5

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

def fixedChebyshevTData_23 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-23 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (2024 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-52624 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (631488 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-4209920 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (17145856 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (-44843008 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (76873728 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (-85917696 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (60293120 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-24117248 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (4194304 : ℤ)

def fixedChebyshevTData_24 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-288 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (13728 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-256256 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (2471040 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-14057472 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (50692096 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (-120324096 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (190513152 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (-199229440 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (132120576 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-50331648 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (8388608 : ℤ)

def fixedChebyshevTData_25 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (25 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (-2600 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (80080 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (-1144000 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (9152000 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (-45260800 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (146227200 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (-317521920 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (466944000 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (-458752000 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (288358400 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-104857600 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (16777216 : ℤ)




















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

def fixedChebyshevUData_22 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (264 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (-11440 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (192192 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (-1647360 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (8200192 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (-25346048 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (50135040 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (-63504384 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (49807360 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (-22020096 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (4194304 : ℤ)

def fixedChebyshevUData_23 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 1 (-24 : ℤ) +
    Polynomial.monomial (R := ℤ) 3 (2288 : ℤ) +
    Polynomial.monomial (R := ℤ) 5 (-64064 : ℤ) +
    Polynomial.monomial (R := ℤ) 7 (823680 : ℤ) +
    Polynomial.monomial (R := ℤ) 9 (-5857280 : ℤ) +
    Polynomial.monomial (R := ℤ) 11 (25346048 : ℤ) +
    Polynomial.monomial (R := ℤ) 13 (-70189056 : ℤ) +
    Polynomial.monomial (R := ℤ) 15 (127008768 : ℤ) +
    Polynomial.monomial (R := ℤ) 17 (-149422080 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (110100480 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-46137344 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (8388608 : ℤ)

def fixedChebyshevUData_24 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 0 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 2 (-312 : ℤ) +
    Polynomial.monomial (R := ℤ) 4 (16016 : ℤ) +
    Polynomial.monomial (R := ℤ) 6 (-320320 : ℤ) +
    Polynomial.monomial (R := ℤ) 8 (3294720 : ℤ) +
    Polynomial.monomial (R := ℤ) 10 (-19914752 : ℤ) +
    Polynomial.monomial (R := ℤ) 12 (76038144 : ℤ) +
    Polynomial.monomial (R := ℤ) 14 (-190513152 : ℤ) +
    Polynomial.monomial (R := ℤ) 16 (317521920 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (-348651520 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (242221056 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-96468992 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (16777216 : ℤ)




















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

theorem fixed_chebyshevU_typed_22 :
    Chebyshev.U ℤ 22 = fixedChebyshevUData_22 := by
  calc
    Chebyshev.U ℤ 22 =
        (2 : ℤ[X]) * X * Chebyshev.U ℤ 21 - Chebyshev.U ℤ 20 :=
      Chebyshev.U_add_two ℤ 20
    _ = (2 : ℤ[X]) * X * fixedChebyshevUData_21 - fixedChebyshevUData_20 := by
      rw [fixed_chebyshevU_typed_21, fixed_chebyshevU_typed_20]
    _ = fixedChebyshevUData_22 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_21, fixedChebyshevUData_20, fixedChebyshevUData_22, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_21, fixedChebyshevUData_20, fixedChebyshevUData_22, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 22
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 22, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 22 ≤ k := Nat.le_of_not_gt hk
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

theorem fixedTyped_chebyshevU_link (a b c : ℤ) (P Q : ℤ[X])
    (hba : b = a + 1) (hca : c = a + 2)
    (hP : Chebyshev.U ℤ a = P) (hQ : Chebyshev.U ℤ b = Q) :
    Chebyshev.U ℤ c = (2 : ℤ[X]) * X * Q - P := by
  rw [hca, Chebyshev.U_add_two, ← hba, hP, hQ]

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

theorem fixed_chebyshevT_typed_23 :
    Chebyshev.T ℤ 23 = fixedChebyshevTData_23 := by
  calc
    Chebyshev.T ℤ 23 =
        (2 : ℤ[X]) * X * Chebyshev.T ℤ 22 - Chebyshev.T ℤ 21 :=
      Chebyshev.T_add_two ℤ 21
    _ = (2 : ℤ[X]) * X * fixedChebyshevTData_22 - fixedChebyshevTData_21 := by
      rw [fixed_chebyshevT_typed_22, fixed_chebyshevT_typed_21]
    _ = fixedChebyshevTData_23 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_22, fixedChebyshevTData_21, fixedChebyshevTData_23, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_22, fixedChebyshevTData_21, fixedChebyshevTData_23, coeff_sub,
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

theorem fixed_chebyshevT_typed_25 :
    Chebyshev.T ℤ 25 = fixedChebyshevTData_25 := by
  calc
    Chebyshev.T ℤ 25 =
        (2 : ℤ[X]) * X * fixedChebyshevTData_24 - fixedChebyshevTData_23 :=
      fixedTyped_chebyshevT_link 23 24 25 fixedChebyshevTData_23 fixedChebyshevTData_24
        (by decide) (by decide) fixed_chebyshevT_typed_23 fixed_chebyshevT_typed_24
    _ = fixedChebyshevTData_25 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevTData_24, fixedChebyshevTData_23, fixedChebyshevTData_25, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevTData_24, fixedChebyshevTData_23, fixedChebyshevTData_25, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul, coeff_add, coeff_monomial]
          by_cases hk : k < 25
          · obtain ⟨i, rfl⟩ : ∃ i : Fin 25, (i : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
            clear hk
            revert i
            decide +kernel
          · have hk' : 25 ≤ k := Nat.le_of_not_gt hk
            simp (disch := omega) only [if_neg, mul_zero, sub_zero, add_zero]




end InternalCatalan

end



noncomputable section
open Polynomial
namespace InternalCatalan

theorem fixed_chebyshevU_typed_24 :
    Chebyshev.U ℤ 24 = fixedChebyshevUData_24 := by
  calc
    Chebyshev.U ℤ 24 =
        (2 : ℤ[X]) * X * fixedChebyshevUData_23 - fixedChebyshevUData_22 :=
      fixedTyped_chebyshevU_link 22 23 24 fixedChebyshevUData_22 fixedChebyshevUData_23
        (by decide) (by decide) fixed_chebyshevU_typed_22 fixed_chebyshevU_typed_23
    _ = fixedChebyshevUData_24 := by
      rw [mul_assoc]
      ext k
      cases k with
      | zero =>
          simp only [fixedChebyshevUData_23, fixedChebyshevUData_22, fixedChebyshevUData_24, coeff_sub,
            coeff_ofNat_mul, coeff_X_mul_zero, coeff_add, coeff_monomial]
          decide
      | succ k =>
          simp only [fixedChebyshevUData_23, fixedChebyshevUData_22, fixedChebyshevUData_24, coeff_sub,
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

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.FixedCompactReversedT16To23
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan





















def fixedReversedTData_20 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-200 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (6600 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-84480 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (549120 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-2050048 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (4659200 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-6553600 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (5570560 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-2621440 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (524288 : ℤ)

def fixedReversedTCoeff_20 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-200 : ℤ) else 0) +
    (if 58 = n then (6600 : ℤ) else 0) +
    (if 56 = n then (-84480 : ℤ) else 0) +
    (if 54 = n then (549120 : ℤ) else 0) +
    (if 52 = n then (-2050048 : ℤ) else 0) +
    (if 50 = n then (4659200 : ℤ) else 0) +
    (if 48 = n then (-6553600 : ℤ) else 0) +
    (if 46 = n then (5570560 : ℤ) else 0) +
    (if 44 = n then (-2621440 : ℤ) else 0) +
    (if 42 = n then (524288 : ℤ) else 0)

theorem fixed_reversedT_typed_data_20 : reversedRow 63 fixedChebyshevTData_20 = fixedReversedTData_20 := by
  simp only [fixedChebyshevTData_20, fixedReversedTData_20, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-200 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (6600 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-84480 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (549120 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-2050048 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (4659200 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-6553600 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (5570560 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-2621440 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (524288 : ℤ) 20 (by decide)]

theorem fixed_reversedT_typed_coeff_20 (n : ℕ) :
    fixedReversedTData_20.coeff n = fixedReversedTCoeff_20 n := by
  simp only [fixedReversedTData_20, fixedReversedTCoeff_20, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_20 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_20 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_20, if_neg, add_zero]

def fixedReversedTData_21 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (21 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-1540 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (33264 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-329472 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (1793792 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-5870592 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (12042240 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-15597568 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (12386304 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-5505024 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (1048576 : ℤ)

def fixedReversedTCoeff_21 (n : ℕ) : ℤ :=
    (if 61 = n then (21 : ℤ) else 0) +
    (if 59 = n then (-1540 : ℤ) else 0) +
    (if 57 = n then (33264 : ℤ) else 0) +
    (if 55 = n then (-329472 : ℤ) else 0) +
    (if 53 = n then (1793792 : ℤ) else 0) +
    (if 51 = n then (-5870592 : ℤ) else 0) +
    (if 49 = n then (12042240 : ℤ) else 0) +
    (if 47 = n then (-15597568 : ℤ) else 0) +
    (if 45 = n then (12386304 : ℤ) else 0) +
    (if 43 = n then (-5505024 : ℤ) else 0) +
    (if 41 = n then (1048576 : ℤ) else 0)

theorem fixed_reversedT_typed_data_21 : reversedRow 63 fixedChebyshevTData_21 = fixedReversedTData_21 := by
  simp only [fixedChebyshevTData_21, fixedReversedTData_21, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (21 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-1540 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (33264 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-329472 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (1793792 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-5870592 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (12042240 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-15597568 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (12386304 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (-5505024 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (1048576 : ℤ) 21 (by decide)]

theorem fixed_reversedT_typed_coeff_21 (n : ℕ) :
    fixedReversedTData_21.coeff n = fixedReversedTCoeff_21 n := by
  simp only [fixedReversedTData_21, fixedReversedTCoeff_21, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_21 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_21 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_21, if_neg, add_zero]

def fixedReversedTData_22 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (242 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-9680 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (151008 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-1208064 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (5637632 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-16400384 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (30638080 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-36765696 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (27394048 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-11534336 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (2097152 : ℤ)

def fixedReversedTCoeff_22 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (242 : ℤ) else 0) +
    (if 58 = n then (-9680 : ℤ) else 0) +
    (if 56 = n then (151008 : ℤ) else 0) +
    (if 54 = n then (-1208064 : ℤ) else 0) +
    (if 52 = n then (5637632 : ℤ) else 0) +
    (if 50 = n then (-16400384 : ℤ) else 0) +
    (if 48 = n then (30638080 : ℤ) else 0) +
    (if 46 = n then (-36765696 : ℤ) else 0) +
    (if 44 = n then (27394048 : ℤ) else 0) +
    (if 42 = n then (-11534336 : ℤ) else 0) +
    (if 40 = n then (2097152 : ℤ) else 0)

theorem fixed_reversedT_typed_data_22 : reversedRow 63 fixedChebyshevTData_22 = fixedReversedTData_22 := by
  simp only [fixedChebyshevTData_22, fixedReversedTData_22, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (242 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-9680 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (151008 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-1208064 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (5637632 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-16400384 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (30638080 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-36765696 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (27394048 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (-11534336 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (2097152 : ℤ) 22 (by decide)]

theorem fixed_reversedT_typed_coeff_22 (n : ℕ) :
    fixedReversedTData_22.coeff n = fixedReversedTCoeff_22 n := by
  simp only [fixedReversedTData_22, fixedReversedTCoeff_22, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_22 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_22 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_22, if_neg, add_zero]

def fixedReversedTData_23 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-23 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (2024 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-52624 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (631488 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-4209920 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (17145856 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-44843008 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (76873728 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-85917696 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (60293120 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-24117248 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (4194304 : ℤ)

def fixedReversedTCoeff_23 (n : ℕ) : ℤ :=
    (if 61 = n then (-23 : ℤ) else 0) +
    (if 59 = n then (2024 : ℤ) else 0) +
    (if 57 = n then (-52624 : ℤ) else 0) +
    (if 55 = n then (631488 : ℤ) else 0) +
    (if 53 = n then (-4209920 : ℤ) else 0) +
    (if 51 = n then (17145856 : ℤ) else 0) +
    (if 49 = n then (-44843008 : ℤ) else 0) +
    (if 47 = n then (76873728 : ℤ) else 0) +
    (if 45 = n then (-85917696 : ℤ) else 0) +
    (if 43 = n then (60293120 : ℤ) else 0) +
    (if 41 = n then (-24117248 : ℤ) else 0) +
    (if 39 = n then (4194304 : ℤ) else 0)

theorem fixed_reversedT_typed_data_23 : reversedRow 63 fixedChebyshevTData_23 = fixedReversedTData_23 := by
  simp only [fixedChebyshevTData_23, fixedReversedTData_23, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-23 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (2024 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-52624 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (631488 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-4209920 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (17145856 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-44843008 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (76873728 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-85917696 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (60293120 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (-24117248 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (4194304 : ℤ) 23 (by decide)]

theorem fixed_reversedT_typed_coeff_23 (n : ℕ) :
    fixedReversedTData_23.coeff n = fixedReversedTCoeff_23 n := by
  simp only [fixedReversedTData_23, fixedReversedTCoeff_23, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_23 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_23 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_23, if_neg, add_zero]

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
















def fixedReversedUData_19 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-20 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (1320 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-25344 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (219648 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-1025024 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (2795520 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-4587520 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (4456448 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-2359296 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (524288 : ℤ)

def fixedReversedUCoeff_19 (n : ℕ) : ℤ :=
    (if 61 = n then (-20 : ℤ) else 0) +
    (if 59 = n then (1320 : ℤ) else 0) +
    (if 57 = n then (-25344 : ℤ) else 0) +
    (if 55 = n then (219648 : ℤ) else 0) +
    (if 53 = n then (-1025024 : ℤ) else 0) +
    (if 51 = n then (2795520 : ℤ) else 0) +
    (if 49 = n then (-4587520 : ℤ) else 0) +
    (if 47 = n then (4456448 : ℤ) else 0) +
    (if 45 = n then (-2359296 : ℤ) else 0) +
    (if 43 = n then (524288 : ℤ) else 0)

theorem fixed_reversedU_typed_data_19 : reversedRow 63 fixedChebyshevUData_19 = fixedReversedUData_19 := by
  simp only [fixedChebyshevUData_19, fixedReversedUData_19, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-20 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (1320 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-25344 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (219648 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-1025024 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (2795520 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-4587520 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (4456448 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-2359296 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (524288 : ℤ) 19 (by decide)]

theorem fixed_reversedU_typed_coeff_19 (n : ℕ) :
    fixedReversedUData_19.coeff n = fixedReversedUCoeff_19 n := by
  simp only [fixedReversedUData_19, fixedReversedUCoeff_19, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_19 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_19 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_19, if_neg, add_zero]

def fixedReversedUData_20 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-220 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (7920 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-109824 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (768768 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-3075072 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (7454720 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-11141120 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (10027008 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-4980736 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (1048576 : ℤ)

def fixedReversedUCoeff_20 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-220 : ℤ) else 0) +
    (if 58 = n then (7920 : ℤ) else 0) +
    (if 56 = n then (-109824 : ℤ) else 0) +
    (if 54 = n then (768768 : ℤ) else 0) +
    (if 52 = n then (-3075072 : ℤ) else 0) +
    (if 50 = n then (7454720 : ℤ) else 0) +
    (if 48 = n then (-11141120 : ℤ) else 0) +
    (if 46 = n then (10027008 : ℤ) else 0) +
    (if 44 = n then (-4980736 : ℤ) else 0) +
    (if 42 = n then (1048576 : ℤ) else 0)

theorem fixed_reversedU_typed_data_20 : reversedRow 63 fixedChebyshevUData_20 = fixedReversedUData_20 := by
  simp only [fixedChebyshevUData_20, fixedReversedUData_20, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-220 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (7920 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-109824 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (768768 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-3075072 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (7454720 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-11141120 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (10027008 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-4980736 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (1048576 : ℤ) 20 (by decide)]

theorem fixed_reversedU_typed_coeff_20 (n : ℕ) :
    fixedReversedUData_20.coeff n = fixedReversedUCoeff_20 n := by
  simp only [fixedReversedUData_20, fixedReversedUCoeff_20, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_20 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_20 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_20, if_neg, add_zero]

def fixedReversedUData_21 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (22 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-1760 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (41184 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-439296 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (2562560 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-8945664 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (19496960 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-26738688 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (22413312 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-10485760 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (2097152 : ℤ)

def fixedReversedUCoeff_21 (n : ℕ) : ℤ :=
    (if 61 = n then (22 : ℤ) else 0) +
    (if 59 = n then (-1760 : ℤ) else 0) +
    (if 57 = n then (41184 : ℤ) else 0) +
    (if 55 = n then (-439296 : ℤ) else 0) +
    (if 53 = n then (2562560 : ℤ) else 0) +
    (if 51 = n then (-8945664 : ℤ) else 0) +
    (if 49 = n then (19496960 : ℤ) else 0) +
    (if 47 = n then (-26738688 : ℤ) else 0) +
    (if 45 = n then (22413312 : ℤ) else 0) +
    (if 43 = n then (-10485760 : ℤ) else 0) +
    (if 41 = n then (2097152 : ℤ) else 0)

theorem fixed_reversedU_typed_data_21 : reversedRow 63 fixedChebyshevUData_21 = fixedReversedUData_21 := by
  simp only [fixedChebyshevUData_21, fixedReversedUData_21, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (22 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-1760 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (41184 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-439296 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (2562560 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-8945664 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (19496960 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-26738688 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (22413312 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (-10485760 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (2097152 : ℤ) 21 (by decide)]

theorem fixed_reversedU_typed_coeff_21 (n : ℕ) :
    fixedReversedUData_21.coeff n = fixedReversedUCoeff_21 n := by
  simp only [fixedReversedUData_21, fixedReversedUCoeff_21, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_21 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_21 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_21, if_neg, add_zero]

def fixedReversedUData_22 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (264 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-11440 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (192192 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-1647360 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (8200192 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-25346048 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (50135040 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-63504384 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (49807360 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-22020096 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (4194304 : ℤ)

def fixedReversedUCoeff_22 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (264 : ℤ) else 0) +
    (if 58 = n then (-11440 : ℤ) else 0) +
    (if 56 = n then (192192 : ℤ) else 0) +
    (if 54 = n then (-1647360 : ℤ) else 0) +
    (if 52 = n then (8200192 : ℤ) else 0) +
    (if 50 = n then (-25346048 : ℤ) else 0) +
    (if 48 = n then (50135040 : ℤ) else 0) +
    (if 46 = n then (-63504384 : ℤ) else 0) +
    (if 44 = n then (49807360 : ℤ) else 0) +
    (if 42 = n then (-22020096 : ℤ) else 0) +
    (if 40 = n then (4194304 : ℤ) else 0)

theorem fixed_reversedU_typed_data_22 : reversedRow 63 fixedChebyshevUData_22 = fixedReversedUData_22 := by
  simp only [fixedChebyshevUData_22, fixedReversedUData_22, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (264 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-11440 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (192192 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-1647360 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (8200192 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-25346048 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (50135040 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-63504384 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (49807360 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (-22020096 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (4194304 : ℤ) 22 (by decide)]

theorem fixed_reversedU_typed_coeff_22 (n : ℕ) :
    fixedReversedUData_22.coeff n = fixedReversedUCoeff_22 n := by
  simp only [fixedReversedUData_22, fixedReversedUCoeff_22, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_22 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_22 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_22, if_neg, add_zero]

def fixedReversedUData_23 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-24 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (2288 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-64064 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (823680 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-5857280 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (25346048 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-70189056 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (127008768 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-149422080 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (110100480 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-46137344 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (8388608 : ℤ)

def fixedReversedUCoeff_23 (n : ℕ) : ℤ :=
    (if 61 = n then (-24 : ℤ) else 0) +
    (if 59 = n then (2288 : ℤ) else 0) +
    (if 57 = n then (-64064 : ℤ) else 0) +
    (if 55 = n then (823680 : ℤ) else 0) +
    (if 53 = n then (-5857280 : ℤ) else 0) +
    (if 51 = n then (25346048 : ℤ) else 0) +
    (if 49 = n then (-70189056 : ℤ) else 0) +
    (if 47 = n then (127008768 : ℤ) else 0) +
    (if 45 = n then (-149422080 : ℤ) else 0) +
    (if 43 = n then (110100480 : ℤ) else 0) +
    (if 41 = n then (-46137344 : ℤ) else 0) +
    (if 39 = n then (8388608 : ℤ) else 0)

theorem fixed_reversedU_typed_data_23 : reversedRow 63 fixedChebyshevUData_23 = fixedReversedUData_23 := by
  simp only [fixedChebyshevUData_23, fixedReversedUData_23, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-24 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (2288 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-64064 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (823680 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-5857280 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (25346048 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-70189056 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (127008768 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-149422080 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (110100480 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (-46137344 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (8388608 : ℤ) 23 (by decide)]

theorem fixed_reversedU_typed_coeff_23 (n : ℕ) :
    fixedReversedUData_23.coeff n = fixedReversedUCoeff_23 n := by
  simp only [fixedReversedUData_23, fixedReversedUCoeff_23, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_23 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_23 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_23, if_neg, add_zero]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow24
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_24 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 42 (524288 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-1048576 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-2097152 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (5242880 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (2949120 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-11141120 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-983040 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (13107200 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-1894400 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-9318400 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (2609152 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (4100096 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-1500928 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-1098240 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (464640 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (168960 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-77880 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-13200 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (6400 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (400 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-199 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_24 (n : ℕ) : ℤ :=
    (if 42 = n then (524288 : ℤ) else 0) +
    (if 43 = n then (-1048576 : ℤ) else 0) +
    (if 44 = n then (-2097152 : ℤ) else 0) +
    (if 45 = n then (5242880 : ℤ) else 0) +
    (if 46 = n then (2949120 : ℤ) else 0) +
    (if 47 = n then (-11141120 : ℤ) else 0) +
    (if 48 = n then (-983040 : ℤ) else 0) +
    (if 49 = n then (13107200 : ℤ) else 0) +
    (if 50 = n then (-1894400 : ℤ) else 0) +
    (if 51 = n then (-9318400 : ℤ) else 0) +
    (if 52 = n then (2609152 : ℤ) else 0) +
    (if 53 = n then (4100096 : ℤ) else 0) +
    (if 54 = n then (-1500928 : ℤ) else 0) +
    (if 55 = n then (-1098240 : ℤ) else 0) +
    (if 56 = n then (464640 : ℤ) else 0) +
    (if 57 = n then (168960 : ℤ) else 0) +
    (if 58 = n then (-77880 : ℤ) else 0) +
    (if 59 = n then (-13200 : ℤ) else 0) +
    (if 60 = n then (6400 : ℤ) else 0) +
    (if 61 = n then (400 : ℤ) else 0) +
    (if 62 = n then (-199 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_24 (n : ℕ) :
    fixedRowPData_24.coeff n = fixedRowPCoeff_24 n := by
  simp only [fixedRowPData_24, fixedRowPCoeff_24, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_24 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_24 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_24, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_24 : ∀ k : Fin 63,
    fixedReversedTCoeff_20 (k.val + 2) - 2 * fixedReversedTCoeff_20 (k.val + 1) + fixedReversedTCoeff_20 k.val = fixedRowPCoeff_24 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_24 :
    (1 - X) ^ 2 * fixedReversedTData_20 = fixedRowPData_24 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_20, fixed_rowP_typed_coeff_24]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_20, fixed_rowP_typed_coeff_24]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_20, fixed_rowP_typed_coeff_24]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_24 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_20 _ (by omega),
              fixed_reversedT_typed_tail_20 _ (by omega), fixed_reversedT_typed_tail_20 _ hn',
              fixed_rowP_typed_tail_24 _ (by omega)]
            decide

theorem fixed_rowP_typed_24 : rowP 1 24 = fixedRowPData_24 := by
  calc
    rowP 1 24 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_20 :=
      fixedTyped_rowP_of_parameters 1 24 2 63 20 fixedChebyshevTData_20
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_20
    _ = fixedRowPData_24 := by
      rw [fixed_reversedT_typed_data_20, fixed_rowP_typed_factor_24]

def fixedRowDData_24 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 43 (524288 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-1048576 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-1835008 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (4718592 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (2097152 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-8912896 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-131072 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (9175040 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-1792000 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-5591040 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (1770496 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (2050048 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-805376 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-439296 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (194304 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (50688 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-24024 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-2640 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (1300 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (40 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-20 : ℤ)

def fixedRowDCoeff_24 (n : ℕ) : ℤ :=
    (if 43 = n then (524288 : ℤ) else 0) +
    (if 44 = n then (-1048576 : ℤ) else 0) +
    (if 45 = n then (-1835008 : ℤ) else 0) +
    (if 46 = n then (4718592 : ℤ) else 0) +
    (if 47 = n then (2097152 : ℤ) else 0) +
    (if 48 = n then (-8912896 : ℤ) else 0) +
    (if 49 = n then (-131072 : ℤ) else 0) +
    (if 50 = n then (9175040 : ℤ) else 0) +
    (if 51 = n then (-1792000 : ℤ) else 0) +
    (if 52 = n then (-5591040 : ℤ) else 0) +
    (if 53 = n then (1770496 : ℤ) else 0) +
    (if 54 = n then (2050048 : ℤ) else 0) +
    (if 55 = n then (-805376 : ℤ) else 0) +
    (if 56 = n then (-439296 : ℤ) else 0) +
    (if 57 = n then (194304 : ℤ) else 0) +
    (if 58 = n then (50688 : ℤ) else 0) +
    (if 59 = n then (-24024 : ℤ) else 0) +
    (if 60 = n then (-2640 : ℤ) else 0) +
    (if 61 = n then (1300 : ℤ) else 0) +
    (if 62 = n then (40 : ℤ) else 0) +
    (if 63 = n then (-20 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_24 (n : ℕ) :
    fixedRowDData_24.coeff n = fixedRowDCoeff_24 n := by
  simp only [fixedRowDData_24, fixedRowDCoeff_24, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_24 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_24 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_24, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_24 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_19 (k.val + 2) - 2 * fixedReversedUCoeff_19 (k.val + 1) + fixedReversedUCoeff_19 k.val) = fixedRowDCoeff_24 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_24 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_19 = fixedRowDData_24 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_19, fixed_rowD_typed_coeff_24]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_19, fixed_rowD_typed_coeff_24]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_19, fixed_rowD_typed_coeff_24]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_24 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_19 _ (by omega),
              fixed_reversedU_typed_tail_19 _ (by omega), fixed_reversedU_typed_tail_19 _ hn',
              fixed_rowD_typed_tail_24 _ (by omega)]
            decide

theorem fixed_rowD_typed_24 : rowD 1 24 = fixedRowDData_24 := by
  calc
    rowD 1 24 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_19 :=
      fixedTyped_rowD_of_parameters 1 24 2 63 19 (1)
        fixedChebyshevUData_19 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_19
    _ = fixedRowDData_24 := by
      rw [fixed_reversedU_typed_data_19, fixed_rowD_typed_factor_24]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow25
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_25 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 41 (1048576 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-2097152 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-4456448 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (11010048 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (6881280 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-24772608 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-3211264 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (31195136 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-3555328 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-24084480 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (6171648 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (11741184 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-4076800 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-3587584 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (1464320 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (658944 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-296208 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-66528 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (31724 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (3080 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-1519 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-42 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (21 : ℤ)

def fixedRowPCoeff_25 (n : ℕ) : ℤ :=
    (if 41 = n then (1048576 : ℤ) else 0) +
    (if 42 = n then (-2097152 : ℤ) else 0) +
    (if 43 = n then (-4456448 : ℤ) else 0) +
    (if 44 = n then (11010048 : ℤ) else 0) +
    (if 45 = n then (6881280 : ℤ) else 0) +
    (if 46 = n then (-24772608 : ℤ) else 0) +
    (if 47 = n then (-3211264 : ℤ) else 0) +
    (if 48 = n then (31195136 : ℤ) else 0) +
    (if 49 = n then (-3555328 : ℤ) else 0) +
    (if 50 = n then (-24084480 : ℤ) else 0) +
    (if 51 = n then (6171648 : ℤ) else 0) +
    (if 52 = n then (11741184 : ℤ) else 0) +
    (if 53 = n then (-4076800 : ℤ) else 0) +
    (if 54 = n then (-3587584 : ℤ) else 0) +
    (if 55 = n then (1464320 : ℤ) else 0) +
    (if 56 = n then (658944 : ℤ) else 0) +
    (if 57 = n then (-296208 : ℤ) else 0) +
    (if 58 = n then (-66528 : ℤ) else 0) +
    (if 59 = n then (31724 : ℤ) else 0) +
    (if 60 = n then (3080 : ℤ) else 0) +
    (if 61 = n then (-1519 : ℤ) else 0) +
    (if 62 = n then (-42 : ℤ) else 0) +
    (if 63 = n then (21 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_25 (n : ℕ) :
    fixedRowPData_25.coeff n = fixedRowPCoeff_25 n := by
  simp only [fixedRowPData_25, fixedRowPCoeff_25, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_25 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_25 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_25, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_25 : ∀ k : Fin 63,
    fixedReversedTCoeff_21 (k.val + 2) - 2 * fixedReversedTCoeff_21 (k.val + 1) + fixedReversedTCoeff_21 k.val = fixedRowPCoeff_25 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_25 :
    (1 - X) ^ 2 * fixedReversedTData_21 = fixedRowPData_25 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_21, fixed_rowP_typed_coeff_25]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_21, fixed_rowP_typed_coeff_25]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_21, fixed_rowP_typed_coeff_25]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_25 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_21 _ (by omega),
              fixed_reversedT_typed_tail_21 _ (by omega), fixed_reversedT_typed_tail_21 _ hn',
              fixed_rowP_typed_tail_25 _ (by omega)]
            decide

theorem fixed_rowP_typed_25 : rowP 1 25 = fixedRowPData_25 := by
  calc
    rowP 1 25 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_21 :=
      fixedTyped_rowP_of_parameters 1 25 2 63 21 fixedChebyshevTData_21
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_21
    _ = fixedRowPData_25 := by
      rw [fixed_reversedT_typed_data_21, fixed_rowP_typed_factor_25]

def fixedRowDData_25 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 42 (1048576 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-2097152 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-3932160 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (9961472 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (5046272 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-20054016 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-1114112 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (22282240 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-3686400 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-14909440 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (4379648 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (6150144 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-2306304 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-1537536 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (658944 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (219648 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-101904 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-15840 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (7700 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (440 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-219 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowDCoeff_25 (n : ℕ) : ℤ :=
    (if 42 = n then (1048576 : ℤ) else 0) +
    (if 43 = n then (-2097152 : ℤ) else 0) +
    (if 44 = n then (-3932160 : ℤ) else 0) +
    (if 45 = n then (9961472 : ℤ) else 0) +
    (if 46 = n then (5046272 : ℤ) else 0) +
    (if 47 = n then (-20054016 : ℤ) else 0) +
    (if 48 = n then (-1114112 : ℤ) else 0) +
    (if 49 = n then (22282240 : ℤ) else 0) +
    (if 50 = n then (-3686400 : ℤ) else 0) +
    (if 51 = n then (-14909440 : ℤ) else 0) +
    (if 52 = n then (4379648 : ℤ) else 0) +
    (if 53 = n then (6150144 : ℤ) else 0) +
    (if 54 = n then (-2306304 : ℤ) else 0) +
    (if 55 = n then (-1537536 : ℤ) else 0) +
    (if 56 = n then (658944 : ℤ) else 0) +
    (if 57 = n then (219648 : ℤ) else 0) +
    (if 58 = n then (-101904 : ℤ) else 0) +
    (if 59 = n then (-15840 : ℤ) else 0) +
    (if 60 = n then (7700 : ℤ) else 0) +
    (if 61 = n then (440 : ℤ) else 0) +
    (if 62 = n then (-219 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_25 (n : ℕ) :
    fixedRowDData_25.coeff n = fixedRowDCoeff_25 n := by
  simp only [fixedRowDData_25, fixedRowDCoeff_25, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_25 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_25 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_25, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_25 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_20 (k.val + 2) - 2 * fixedReversedUCoeff_20 (k.val + 1) + fixedReversedUCoeff_20 k.val) = fixedRowDCoeff_25 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_25 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_20 = fixedRowDData_25 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_20, fixed_rowD_typed_coeff_25]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_20, fixed_rowD_typed_coeff_25]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_20, fixed_rowD_typed_coeff_25]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_25 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_20 _ (by omega),
              fixed_reversedU_typed_tail_20 _ (by omega), fixed_reversedU_typed_tail_20 _ hn',
              fixed_rowD_typed_tail_25 _ (by omega)]
            decide

theorem fixed_rowD_typed_25 : rowD 1 25 = fixedRowDData_25 := by
  calc
    rowD 1 25 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_20 :=
      fixedTyped_rowD_of_parameters 1 25 2 63 20 (1)
        fixedChebyshevUData_20 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_20
    _ = fixedRowDData_25 := by
      rw [fixed_reversedU_typed_data_20, fixed_rowD_typed_factor_25]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow26
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_26 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 40 (2097152 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-4194304 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-9437184 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (23068672 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (15859712 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-54788096 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-9371648 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (73531392 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-6127616 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-61276160 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (14237696 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (32800768 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-10762752 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-11275264 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (4429568 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (2416128 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-1057056 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-302016 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (141328 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (19360 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-9438 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-484 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (241 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowPCoeff_26 (n : ℕ) : ℤ :=
    (if 40 = n then (2097152 : ℤ) else 0) +
    (if 41 = n then (-4194304 : ℤ) else 0) +
    (if 42 = n then (-9437184 : ℤ) else 0) +
    (if 43 = n then (23068672 : ℤ) else 0) +
    (if 44 = n then (15859712 : ℤ) else 0) +
    (if 45 = n then (-54788096 : ℤ) else 0) +
    (if 46 = n then (-9371648 : ℤ) else 0) +
    (if 47 = n then (73531392 : ℤ) else 0) +
    (if 48 = n then (-6127616 : ℤ) else 0) +
    (if 49 = n then (-61276160 : ℤ) else 0) +
    (if 50 = n then (14237696 : ℤ) else 0) +
    (if 51 = n then (32800768 : ℤ) else 0) +
    (if 52 = n then (-10762752 : ℤ) else 0) +
    (if 53 = n then (-11275264 : ℤ) else 0) +
    (if 54 = n then (4429568 : ℤ) else 0) +
    (if 55 = n then (2416128 : ℤ) else 0) +
    (if 56 = n then (-1057056 : ℤ) else 0) +
    (if 57 = n then (-302016 : ℤ) else 0) +
    (if 58 = n then (141328 : ℤ) else 0) +
    (if 59 = n then (19360 : ℤ) else 0) +
    (if 60 = n then (-9438 : ℤ) else 0) +
    (if 61 = n then (-484 : ℤ) else 0) +
    (if 62 = n then (241 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_26 (n : ℕ) :
    fixedRowPData_26.coeff n = fixedRowPCoeff_26 n := by
  simp only [fixedRowPData_26, fixedRowPCoeff_26, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_26 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_26 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_26, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_26 : ∀ k : Fin 63,
    fixedReversedTCoeff_22 (k.val + 2) - 2 * fixedReversedTCoeff_22 (k.val + 1) + fixedReversedTCoeff_22 k.val = fixedRowPCoeff_26 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_26 :
    (1 - X) ^ 2 * fixedReversedTData_22 = fixedRowPData_26 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_22, fixed_rowP_typed_coeff_26]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_22, fixed_rowP_typed_coeff_26]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_22, fixed_rowP_typed_coeff_26]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_26 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_22 _ (by omega),
              fixed_reversedT_typed_tail_22 _ (by omega), fixed_reversedT_typed_tail_22 _ hn',
              fixed_rowP_typed_tail_26 _ (by omega)]
            decide

theorem fixed_rowP_typed_26 : rowP 1 26 = fixedRowPData_26 := by
  calc
    rowP 1 26 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_22 :=
      fixedTyped_rowP_of_parameters 1 26 2 63 22 fixedChebyshevTData_22
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_22
    _ = fixedRowPData_26 := by
      rw [fixed_reversedT_typed_data_22, fixed_rowP_typed_factor_26]

def fixedRowDData_26 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 41 (2097152 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-4194304 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-8388608 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (20971520 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (11927552 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-44826624 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-4325376 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (53477376 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-7241728 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-38993920 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (10551296 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (17891328 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-6383104 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-5125120 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (2123264 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (878592 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-398112 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-82368 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (39424 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (3520 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-1738 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-44 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (22 : ℤ)

def fixedRowDCoeff_26 (n : ℕ) : ℤ :=
    (if 41 = n then (2097152 : ℤ) else 0) +
    (if 42 = n then (-4194304 : ℤ) else 0) +
    (if 43 = n then (-8388608 : ℤ) else 0) +
    (if 44 = n then (20971520 : ℤ) else 0) +
    (if 45 = n then (11927552 : ℤ) else 0) +
    (if 46 = n then (-44826624 : ℤ) else 0) +
    (if 47 = n then (-4325376 : ℤ) else 0) +
    (if 48 = n then (53477376 : ℤ) else 0) +
    (if 49 = n then (-7241728 : ℤ) else 0) +
    (if 50 = n then (-38993920 : ℤ) else 0) +
    (if 51 = n then (10551296 : ℤ) else 0) +
    (if 52 = n then (17891328 : ℤ) else 0) +
    (if 53 = n then (-6383104 : ℤ) else 0) +
    (if 54 = n then (-5125120 : ℤ) else 0) +
    (if 55 = n then (2123264 : ℤ) else 0) +
    (if 56 = n then (878592 : ℤ) else 0) +
    (if 57 = n then (-398112 : ℤ) else 0) +
    (if 58 = n then (-82368 : ℤ) else 0) +
    (if 59 = n then (39424 : ℤ) else 0) +
    (if 60 = n then (3520 : ℤ) else 0) +
    (if 61 = n then (-1738 : ℤ) else 0) +
    (if 62 = n then (-44 : ℤ) else 0) +
    (if 63 = n then (22 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_26 (n : ℕ) :
    fixedRowDData_26.coeff n = fixedRowDCoeff_26 n := by
  simp only [fixedRowDData_26, fixedRowDCoeff_26, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_26 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_26 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_26, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_26 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_21 (k.val + 2) - 2 * fixedReversedUCoeff_21 (k.val + 1) + fixedReversedUCoeff_21 k.val) = fixedRowDCoeff_26 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_26 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_21 = fixedRowDData_26 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_21, fixed_rowD_typed_coeff_26]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_21, fixed_rowD_typed_coeff_26]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_21, fixed_rowD_typed_coeff_26]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_26 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_21 _ (by omega),
              fixed_reversedU_typed_tail_21 _ (by omega), fixed_reversedU_typed_tail_21 _ hn',
              fixed_rowD_typed_tail_26 _ (by omega)]
            decide

theorem fixed_rowD_typed_26 : rowD 1 26 = fixedRowDData_26 := by
  calc
    rowD 1 26 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_21 :=
      fixedTyped_rowD_of_parameters 1 26 2 63 21 (1)
        fixedChebyshevUData_21 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_21
    _ = fixedRowDData_26 := by
      rw [fixed_reversedU_typed_data_21, fixed_rowD_typed_factor_26]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow27
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_27 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 39 (4194304 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-8388608 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-19922944 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (48234496 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (36175872 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-120586240 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-25624576 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (171835392 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-9043968 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-153747456 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (32030720 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (89686016 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-27697152 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-34291712 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (12935936 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (8419840 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-3578432 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-1262976 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (578864 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (105248 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-50600 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-4048 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (2001 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (46 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-23 : ℤ)

def fixedRowPCoeff_27 (n : ℕ) : ℤ :=
    (if 39 = n then (4194304 : ℤ) else 0) +
    (if 40 = n then (-8388608 : ℤ) else 0) +
    (if 41 = n then (-19922944 : ℤ) else 0) +
    (if 42 = n then (48234496 : ℤ) else 0) +
    (if 43 = n then (36175872 : ℤ) else 0) +
    (if 44 = n then (-120586240 : ℤ) else 0) +
    (if 45 = n then (-25624576 : ℤ) else 0) +
    (if 46 = n then (171835392 : ℤ) else 0) +
    (if 47 = n then (-9043968 : ℤ) else 0) +
    (if 48 = n then (-153747456 : ℤ) else 0) +
    (if 49 = n then (32030720 : ℤ) else 0) +
    (if 50 = n then (89686016 : ℤ) else 0) +
    (if 51 = n then (-27697152 : ℤ) else 0) +
    (if 52 = n then (-34291712 : ℤ) else 0) +
    (if 53 = n then (12935936 : ℤ) else 0) +
    (if 54 = n then (8419840 : ℤ) else 0) +
    (if 55 = n then (-3578432 : ℤ) else 0) +
    (if 56 = n then (-1262976 : ℤ) else 0) +
    (if 57 = n then (578864 : ℤ) else 0) +
    (if 58 = n then (105248 : ℤ) else 0) +
    (if 59 = n then (-50600 : ℤ) else 0) +
    (if 60 = n then (-4048 : ℤ) else 0) +
    (if 61 = n then (2001 : ℤ) else 0) +
    (if 62 = n then (46 : ℤ) else 0) +
    (if 63 = n then (-23 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_27 (n : ℕ) :
    fixedRowPData_27.coeff n = fixedRowPCoeff_27 n := by
  simp only [fixedRowPData_27, fixedRowPCoeff_27, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_27 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_27 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_27, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_27 : ∀ k : Fin 63,
    fixedReversedTCoeff_23 (k.val + 2) - 2 * fixedReversedTCoeff_23 (k.val + 1) + fixedReversedTCoeff_23 k.val = fixedRowPCoeff_27 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_27 :
    (1 - X) ^ 2 * fixedReversedTData_23 = fixedRowPData_27 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_23, fixed_rowP_typed_coeff_27]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_23, fixed_rowP_typed_coeff_27]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_23, fixed_rowP_typed_coeff_27]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_27 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_23 _ (by omega),
              fixed_reversedT_typed_tail_23 _ (by omega), fixed_reversedT_typed_tail_23 _ hn',
              fixed_rowP_typed_tail_27 _ (by omega)]
            decide

theorem fixed_rowP_typed_27 : rowP 1 27 = fixedRowPData_27 := by
  calc
    rowP 1 27 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_23 :=
      fixedTyped_rowP_of_parameters 1 27 2 63 23 fixedChebyshevTData_23
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_23
    _ = fixedRowPData_27 := by
      rw [fixed_reversedT_typed_data_23, fixed_rowP_typed_factor_27]

def fixedRowDData_27 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 40 (4194304 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-8388608 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-17825792 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (44040192 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (27787264 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-99614720 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-13697024 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (127008768 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-13369344 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-100270080 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (24788992 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (50692096 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-17145856 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-16400384 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (6552832 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (3294720 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-1455168 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-384384 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (180752 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (22880 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-11176 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-528 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (263 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowDCoeff_27 (n : ℕ) : ℤ :=
    (if 40 = n then (4194304 : ℤ) else 0) +
    (if 41 = n then (-8388608 : ℤ) else 0) +
    (if 42 = n then (-17825792 : ℤ) else 0) +
    (if 43 = n then (44040192 : ℤ) else 0) +
    (if 44 = n then (27787264 : ℤ) else 0) +
    (if 45 = n then (-99614720 : ℤ) else 0) +
    (if 46 = n then (-13697024 : ℤ) else 0) +
    (if 47 = n then (127008768 : ℤ) else 0) +
    (if 48 = n then (-13369344 : ℤ) else 0) +
    (if 49 = n then (-100270080 : ℤ) else 0) +
    (if 50 = n then (24788992 : ℤ) else 0) +
    (if 51 = n then (50692096 : ℤ) else 0) +
    (if 52 = n then (-17145856 : ℤ) else 0) +
    (if 53 = n then (-16400384 : ℤ) else 0) +
    (if 54 = n then (6552832 : ℤ) else 0) +
    (if 55 = n then (3294720 : ℤ) else 0) +
    (if 56 = n then (-1455168 : ℤ) else 0) +
    (if 57 = n then (-384384 : ℤ) else 0) +
    (if 58 = n then (180752 : ℤ) else 0) +
    (if 59 = n then (22880 : ℤ) else 0) +
    (if 60 = n then (-11176 : ℤ) else 0) +
    (if 61 = n then (-528 : ℤ) else 0) +
    (if 62 = n then (263 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_27 (n : ℕ) :
    fixedRowDData_27.coeff n = fixedRowDCoeff_27 n := by
  simp only [fixedRowDData_27, fixedRowDCoeff_27, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_27 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_27 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_27, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_27 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_22 (k.val + 2) - 2 * fixedReversedUCoeff_22 (k.val + 1) + fixedReversedUCoeff_22 k.val) = fixedRowDCoeff_27 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_27 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_22 = fixedRowDData_27 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_22, fixed_rowD_typed_coeff_27]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_22, fixed_rowD_typed_coeff_27]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_22, fixed_rowD_typed_coeff_27]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_27 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_22 _ (by omega),
              fixed_reversedU_typed_tail_22 _ (by omega), fixed_reversedU_typed_tail_22 _ hn',
              fixed_rowD_typed_tail_27 _ (by omega)]
            decide

theorem fixed_rowD_typed_27 : rowD 1 27 = fixedRowDData_27 := by
  calc
    rowD 1 27 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_22 :=
      fixedTyped_rowD_of_parameters 1 27 2 63 22 (1)
        fixedChebyshevUData_22 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_22
    _ = fixedRowDData_27 := by
      rw [fixed_reversedU_typed_data_22, fixed_rowD_typed_factor_27]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.FixedCompactReversedT24To31
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedReversedTData_24 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-288 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (13728 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-256256 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (2471040 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-14057472 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (50692096 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-120324096 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (190513152 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-199229440 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (132120576 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-50331648 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (8388608 : ℤ)

def fixedReversedTCoeff_24 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-288 : ℤ) else 0) +
    (if 58 = n then (13728 : ℤ) else 0) +
    (if 56 = n then (-256256 : ℤ) else 0) +
    (if 54 = n then (2471040 : ℤ) else 0) +
    (if 52 = n then (-14057472 : ℤ) else 0) +
    (if 50 = n then (50692096 : ℤ) else 0) +
    (if 48 = n then (-120324096 : ℤ) else 0) +
    (if 46 = n then (190513152 : ℤ) else 0) +
    (if 44 = n then (-199229440 : ℤ) else 0) +
    (if 42 = n then (132120576 : ℤ) else 0) +
    (if 40 = n then (-50331648 : ℤ) else 0) +
    (if 38 = n then (8388608 : ℤ) else 0)

theorem fixed_reversedT_typed_data_24 : reversedRow 63 fixedChebyshevTData_24 = fixedReversedTData_24 := by
  simp only [fixedChebyshevTData_24, fixedReversedTData_24, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-288 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (13728 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-256256 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (2471040 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-14057472 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (50692096 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-120324096 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (190513152 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-199229440 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (132120576 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (-50331648 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (8388608 : ℤ) 24 (by decide)]

theorem fixed_reversedT_typed_coeff_24 (n : ℕ) :
    fixedReversedTData_24.coeff n = fixedReversedTCoeff_24 n := by
  simp only [fixedReversedTData_24, fixedReversedTCoeff_24, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_24 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_24 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_24, if_neg, add_zero]

def fixedReversedTData_25 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (25 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-2600 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (80080 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-1144000 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (9152000 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-45260800 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (146227200 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-317521920 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (466944000 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-458752000 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (288358400 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-104857600 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (16777216 : ℤ)

def fixedReversedTCoeff_25 (n : ℕ) : ℤ :=
    (if 61 = n then (25 : ℤ) else 0) +
    (if 59 = n then (-2600 : ℤ) else 0) +
    (if 57 = n then (80080 : ℤ) else 0) +
    (if 55 = n then (-1144000 : ℤ) else 0) +
    (if 53 = n then (9152000 : ℤ) else 0) +
    (if 51 = n then (-45260800 : ℤ) else 0) +
    (if 49 = n then (146227200 : ℤ) else 0) +
    (if 47 = n then (-317521920 : ℤ) else 0) +
    (if 45 = n then (466944000 : ℤ) else 0) +
    (if 43 = n then (-458752000 : ℤ) else 0) +
    (if 41 = n then (288358400 : ℤ) else 0) +
    (if 39 = n then (-104857600 : ℤ) else 0) +
    (if 37 = n then (16777216 : ℤ) else 0)

theorem fixed_reversedT_typed_data_25 : reversedRow 63 fixedChebyshevTData_25 = fixedReversedTData_25 := by
  simp only [fixedChebyshevTData_25, fixedReversedTData_25, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (25 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-2600 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (80080 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-1144000 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (9152000 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-45260800 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (146227200 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-317521920 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (466944000 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (-458752000 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (288358400 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (-104857600 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (16777216 : ℤ) 25 (by decide)]

theorem fixed_reversedT_typed_coeff_25 (n : ℕ) :
    fixedReversedTData_25.coeff n = fixedReversedTCoeff_25 n := by
  simp only [fixedReversedTData_25, fixedReversedTCoeff_25, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_25 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_25 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_25, if_neg, add_zero]































end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow28
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_28 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 38 (8388608 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-16777216 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-41943040 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (100663296 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (81788928 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-264241152 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-67108864 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (398458880 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-8716288 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-381026304 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (70189056 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (240648192 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-69632000 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-101384192 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (36634624 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (28114944 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-11586432 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-4942080 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (2214784 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (512512 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-242528 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-27456 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (13440 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (576 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-287 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_28 (n : ℕ) : ℤ :=
    (if 38 = n then (8388608 : ℤ) else 0) +
    (if 39 = n then (-16777216 : ℤ) else 0) +
    (if 40 = n then (-41943040 : ℤ) else 0) +
    (if 41 = n then (100663296 : ℤ) else 0) +
    (if 42 = n then (81788928 : ℤ) else 0) +
    (if 43 = n then (-264241152 : ℤ) else 0) +
    (if 44 = n then (-67108864 : ℤ) else 0) +
    (if 45 = n then (398458880 : ℤ) else 0) +
    (if 46 = n then (-8716288 : ℤ) else 0) +
    (if 47 = n then (-381026304 : ℤ) else 0) +
    (if 48 = n then (70189056 : ℤ) else 0) +
    (if 49 = n then (240648192 : ℤ) else 0) +
    (if 50 = n then (-69632000 : ℤ) else 0) +
    (if 51 = n then (-101384192 : ℤ) else 0) +
    (if 52 = n then (36634624 : ℤ) else 0) +
    (if 53 = n then (28114944 : ℤ) else 0) +
    (if 54 = n then (-11586432 : ℤ) else 0) +
    (if 55 = n then (-4942080 : ℤ) else 0) +
    (if 56 = n then (2214784 : ℤ) else 0) +
    (if 57 = n then (512512 : ℤ) else 0) +
    (if 58 = n then (-242528 : ℤ) else 0) +
    (if 59 = n then (-27456 : ℤ) else 0) +
    (if 60 = n then (13440 : ℤ) else 0) +
    (if 61 = n then (576 : ℤ) else 0) +
    (if 62 = n then (-287 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_28 (n : ℕ) :
    fixedRowPData_28.coeff n = fixedRowPCoeff_28 n := by
  simp only [fixedRowPData_28, fixedRowPCoeff_28, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_28 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_28 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_28, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_28 : ∀ k : Fin 63,
    fixedReversedTCoeff_24 (k.val + 2) - 2 * fixedReversedTCoeff_24 (k.val + 1) + fixedReversedTCoeff_24 k.val = fixedRowPCoeff_28 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_28 :
    (1 - X) ^ 2 * fixedReversedTData_24 = fixedRowPData_28 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_24, fixed_rowP_typed_coeff_28]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_24, fixed_rowP_typed_coeff_28]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_24, fixed_rowP_typed_coeff_28]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_28 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_24 _ (by omega),
              fixed_reversedT_typed_tail_24 _ (by omega), fixed_reversedT_typed_tail_24 _ hn',
              fixed_rowP_typed_tail_28 _ (by omega)]
            decide

theorem fixed_rowP_typed_28 : rowP 1 28 = fixedRowPData_28 := by
  calc
    rowP 1 28 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_24 :=
      fixedTyped_rowP_of_parameters 1 28 2 63 24 fixedChebyshevTData_24
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_24
    _ = fixedRowPData_28 := by
      rw [fixed_reversedT_typed_data_24, fixed_rowP_typed_factor_28]

def fixedRowDData_28 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 39 (8388608 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-16777216 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-37748736 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (92274688 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (63963136 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-220200960 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-39321600 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (298844160 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-22413312 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-254017536 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (56819712 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (140378112 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-44843008 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-50692096 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (19488768 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (11714560 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-5033600 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-1647360 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (759616 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (128128 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-61776 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-4576 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (2264 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (48 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-24 : ℤ)

def fixedRowDCoeff_28 (n : ℕ) : ℤ :=
    (if 39 = n then (8388608 : ℤ) else 0) +
    (if 40 = n then (-16777216 : ℤ) else 0) +
    (if 41 = n then (-37748736 : ℤ) else 0) +
    (if 42 = n then (92274688 : ℤ) else 0) +
    (if 43 = n then (63963136 : ℤ) else 0) +
    (if 44 = n then (-220200960 : ℤ) else 0) +
    (if 45 = n then (-39321600 : ℤ) else 0) +
    (if 46 = n then (298844160 : ℤ) else 0) +
    (if 47 = n then (-22413312 : ℤ) else 0) +
    (if 48 = n then (-254017536 : ℤ) else 0) +
    (if 49 = n then (56819712 : ℤ) else 0) +
    (if 50 = n then (140378112 : ℤ) else 0) +
    (if 51 = n then (-44843008 : ℤ) else 0) +
    (if 52 = n then (-50692096 : ℤ) else 0) +
    (if 53 = n then (19488768 : ℤ) else 0) +
    (if 54 = n then (11714560 : ℤ) else 0) +
    (if 55 = n then (-5033600 : ℤ) else 0) +
    (if 56 = n then (-1647360 : ℤ) else 0) +
    (if 57 = n then (759616 : ℤ) else 0) +
    (if 58 = n then (128128 : ℤ) else 0) +
    (if 59 = n then (-61776 : ℤ) else 0) +
    (if 60 = n then (-4576 : ℤ) else 0) +
    (if 61 = n then (2264 : ℤ) else 0) +
    (if 62 = n then (48 : ℤ) else 0) +
    (if 63 = n then (-24 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_28 (n : ℕ) :
    fixedRowDData_28.coeff n = fixedRowDCoeff_28 n := by
  simp only [fixedRowDData_28, fixedRowDCoeff_28, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_28 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_28 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_28, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_28 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_23 (k.val + 2) - 2 * fixedReversedUCoeff_23 (k.val + 1) + fixedReversedUCoeff_23 k.val) = fixedRowDCoeff_28 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_28 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_23 = fixedRowDData_28 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_23, fixed_rowD_typed_coeff_28]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_23, fixed_rowD_typed_coeff_28]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_23, fixed_rowD_typed_coeff_28]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_28 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_23 _ (by omega),
              fixed_reversedU_typed_tail_23 _ (by omega), fixed_reversedU_typed_tail_23 _ hn',
              fixed_rowD_typed_tail_28 _ (by omega)]
            decide

theorem fixed_rowD_typed_28 : rowD 1 28 = fixedRowDData_28 := by
  calc
    rowD 1 28 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_23 :=
      fixedTyped_rowD_of_parameters 1 28 2 63 23 (1)
        fixedChebyshevUData_23 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_23
    _ = fixedRowDData_28 := by
      rw [fixed_reversedU_typed_data_23, fixed_rowD_typed_factor_28]

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.FixedCompactReversedU24To31
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedReversedUData_24 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-312 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (16016 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-320320 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (3294720 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-19914752 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (76038144 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-190513152 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (317521920 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-348651520 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (242221056 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-96468992 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (16777216 : ℤ)

def fixedReversedUCoeff_24 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-312 : ℤ) else 0) +
    (if 58 = n then (16016 : ℤ) else 0) +
    (if 56 = n then (-320320 : ℤ) else 0) +
    (if 54 = n then (3294720 : ℤ) else 0) +
    (if 52 = n then (-19914752 : ℤ) else 0) +
    (if 50 = n then (76038144 : ℤ) else 0) +
    (if 48 = n then (-190513152 : ℤ) else 0) +
    (if 46 = n then (317521920 : ℤ) else 0) +
    (if 44 = n then (-348651520 : ℤ) else 0) +
    (if 42 = n then (242221056 : ℤ) else 0) +
    (if 40 = n then (-96468992 : ℤ) else 0) +
    (if 38 = n then (16777216 : ℤ) else 0)

theorem fixed_reversedU_typed_data_24 : reversedRow 63 fixedChebyshevUData_24 = fixedReversedUData_24 := by
  simp only [fixedChebyshevUData_24, fixedReversedUData_24, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-312 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (16016 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-320320 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (3294720 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-19914752 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (76038144 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-190513152 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (317521920 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-348651520 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (242221056 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (-96468992 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (16777216 : ℤ) 24 (by decide)]

theorem fixed_reversedU_typed_coeff_24 (n : ℕ) :
    fixedReversedUData_24.coeff n = fixedReversedUCoeff_24 n := by
  simp only [fixedReversedUData_24, fixedReversedUCoeff_24, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_24 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_24 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_24, if_neg, add_zero]




































end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedCompactRow29
namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_29 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 37 (16777216 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-33554432 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-88080384 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (209715200 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (183500800 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-576716800 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-170393600 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (917504000 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (8192000 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-933888000 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (149422080 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (635043840 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-171294720 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-292454400 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (100966400 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (90521600 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-36108800 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-18304000 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (8008000 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (2288000 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-1063920 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-160160 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (77480 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (5200 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-2575 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-50 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (25 : ℤ)

def fixedRowPCoeff_29 (n : ℕ) : ℤ :=
    (if 37 = n then (16777216 : ℤ) else 0) +
    (if 38 = n then (-33554432 : ℤ) else 0) +
    (if 39 = n then (-88080384 : ℤ) else 0) +
    (if 40 = n then (209715200 : ℤ) else 0) +
    (if 41 = n then (183500800 : ℤ) else 0) +
    (if 42 = n then (-576716800 : ℤ) else 0) +
    (if 43 = n then (-170393600 : ℤ) else 0) +
    (if 44 = n then (917504000 : ℤ) else 0) +
    (if 45 = n then (8192000 : ℤ) else 0) +
    (if 46 = n then (-933888000 : ℤ) else 0) +
    (if 47 = n then (149422080 : ℤ) else 0) +
    (if 48 = n then (635043840 : ℤ) else 0) +
    (if 49 = n then (-171294720 : ℤ) else 0) +
    (if 50 = n then (-292454400 : ℤ) else 0) +
    (if 51 = n then (100966400 : ℤ) else 0) +
    (if 52 = n then (90521600 : ℤ) else 0) +
    (if 53 = n then (-36108800 : ℤ) else 0) +
    (if 54 = n then (-18304000 : ℤ) else 0) +
    (if 55 = n then (8008000 : ℤ) else 0) +
    (if 56 = n then (2288000 : ℤ) else 0) +
    (if 57 = n then (-1063920 : ℤ) else 0) +
    (if 58 = n then (-160160 : ℤ) else 0) +
    (if 59 = n then (77480 : ℤ) else 0) +
    (if 60 = n then (5200 : ℤ) else 0) +
    (if 61 = n then (-2575 : ℤ) else 0) +
    (if 62 = n then (-50 : ℤ) else 0) +
    (if 63 = n then (25 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_29 (n : ℕ) :
    fixedRowPData_29.coeff n = fixedRowPCoeff_29 n := by
  simp only [fixedRowPData_29, fixedRowPCoeff_29, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_29 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_29 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_29, if_neg, add_zero]

theorem fixed_rowP_typed_scalar_29 : ∀ k : Fin 63,
    fixedReversedTCoeff_25 (k.val + 2) - 2 * fixedReversedTCoeff_25 (k.val + 1) + fixedReversedTCoeff_25 k.val = fixedRowPCoeff_29 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_29 :
    (1 - X) ^ 2 * fixedReversedTData_25 = fixedRowPData_29 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_25, fixed_rowP_typed_coeff_29]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_25, fixed_rowP_typed_coeff_29]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_25, fixed_rowP_typed_coeff_29]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_29 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_25 _ (by omega),
              fixed_reversedT_typed_tail_25 _ (by omega), fixed_reversedT_typed_tail_25 _ hn',
              fixed_rowP_typed_tail_29 _ (by omega)]
            decide

theorem fixed_rowP_typed_29 : rowP 1 29 = fixedRowPData_29 := by
  calc
    rowP 1 29 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_25 :=
      fixedTyped_rowP_of_parameters 1 29 2 63 25 fixedChebyshevTData_25
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_25
    _ = fixedRowPData_29 := by
      rw [fixed_reversedT_typed_data_25, fixed_rowP_typed_factor_29]

def fixedRowDData_29 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 38 (16777216 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-33554432 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-79691776 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (192937984 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (145752064 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-484442112 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-106430464 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (697303040 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-31129600 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-635043840 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (127008768 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (381026304 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-114475008 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-152076288 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (56123392 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (39829504 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-16620032 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-6589440 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (2974400 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (640640 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-304304 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-32032 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (15704 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (624 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-311 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowDCoeff_29 (n : ℕ) : ℤ :=
    (if 38 = n then (16777216 : ℤ) else 0) +
    (if 39 = n then (-33554432 : ℤ) else 0) +
    (if 40 = n then (-79691776 : ℤ) else 0) +
    (if 41 = n then (192937984 : ℤ) else 0) +
    (if 42 = n then (145752064 : ℤ) else 0) +
    (if 43 = n then (-484442112 : ℤ) else 0) +
    (if 44 = n then (-106430464 : ℤ) else 0) +
    (if 45 = n then (697303040 : ℤ) else 0) +
    (if 46 = n then (-31129600 : ℤ) else 0) +
    (if 47 = n then (-635043840 : ℤ) else 0) +
    (if 48 = n then (127008768 : ℤ) else 0) +
    (if 49 = n then (381026304 : ℤ) else 0) +
    (if 50 = n then (-114475008 : ℤ) else 0) +
    (if 51 = n then (-152076288 : ℤ) else 0) +
    (if 52 = n then (56123392 : ℤ) else 0) +
    (if 53 = n then (39829504 : ℤ) else 0) +
    (if 54 = n then (-16620032 : ℤ) else 0) +
    (if 55 = n then (-6589440 : ℤ) else 0) +
    (if 56 = n then (2974400 : ℤ) else 0) +
    (if 57 = n then (640640 : ℤ) else 0) +
    (if 58 = n then (-304304 : ℤ) else 0) +
    (if 59 = n then (-32032 : ℤ) else 0) +
    (if 60 = n then (15704 : ℤ) else 0) +
    (if 61 = n then (624 : ℤ) else 0) +
    (if 62 = n then (-311 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_29 (n : ℕ) :
    fixedRowDData_29.coeff n = fixedRowDCoeff_29 n := by
  simp only [fixedRowDData_29, fixedRowDCoeff_29, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_29 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_29 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_29, if_neg, add_zero]

theorem fixed_rowD_typed_scalar_29 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_24 (k.val + 2) - 2 * fixedReversedUCoeff_24 (k.val + 1) + fixedReversedUCoeff_24 k.val) = fixedRowDCoeff_29 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_29 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_24 = fixedRowDData_29 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_24, fixed_rowD_typed_coeff_29]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_24, fixed_rowD_typed_coeff_29]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_24, fixed_rowD_typed_coeff_29]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_29 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_24 _ (by omega),
              fixed_reversedU_typed_tail_24 _ (by omega), fixed_reversedU_typed_tail_24 _ hn',
              fixed_rowD_typed_tail_29 _ (by omega)]
            decide

theorem fixed_rowD_typed_29 : rowD 1 29 = fixedRowDData_29 := by
  calc
    rowD 1 29 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_24 :=
      fixedTyped_rowD_of_parameters 1 29 2 63 24 (1)
        fixedChebyshevUData_24 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_24
    _ = fixedRowDData_29 := by
      rw [fixed_reversedU_typed_data_24, fixed_rowD_typed_factor_29]

end InternalCatalan

end

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
-- module Solutions.OAICatalan.Split.IntBaseRows24
namespace OAI

namespace InternalCatalan

theorem splitBaseMod_row_24 (k : Fin 48) :
    (fixedIntegerBaseCanonical (24 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (24 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (24 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_24 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_24 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 24).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 24).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_24, fixed_rowD_typed_24]
    simp only [fixed_rowP_typed_coeff_24, fixed_rowD_typed_coeff_24,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_25 (k : Fin 48) :
    (fixedIntegerBaseCanonical (25 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (25 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (25 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_25 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_25 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 25).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 25).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_25, fixed_rowD_typed_25]
    simp only [fixed_rowP_typed_coeff_25, fixed_rowD_typed_coeff_25,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_26 (k : Fin 48) :
    (fixedIntegerBaseCanonical (26 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (26 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (26 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_26 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_26 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 26).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 26).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_26, fixed_rowD_typed_26]
    simp only [fixed_rowP_typed_coeff_26, fixed_rowD_typed_coeff_26,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_27 (k : Fin 48) :
    (fixedIntegerBaseCanonical (27 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (27 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (27 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_27 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_27 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 27).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 27).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_27, fixed_rowD_typed_27]
    simp only [fixed_rowP_typed_coeff_27, fixed_rowD_typed_coeff_27,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_28 (k : Fin 48) :
    (fixedIntegerBaseCanonical (28 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (28 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (28 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_28 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_28 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 28).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 28).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_28, fixed_rowD_typed_28]
    simp only [fixed_rowP_typed_coeff_28, fixed_rowD_typed_coeff_28,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem splitBaseMod_row_29 (k : Fin 48) :
    (fixedIntegerBaseCanonical (29 : Fin 49) k : ZMod 101) = fixedLiteralBaseMod (29 : Fin 49) k := by
  have h : (fixedIntegerBaseCanonical (29 : Fin 49) k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedRowPCoeff_29 i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedRowDCoeff_29 i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
    show ((2 * (∑ i ∈ Finset.range 65, (rowP 1 29).coeff i * fixedClearedMoment i k) -
      3 * (∑ i ∈ Finset.range 65, (rowD 1 29).coeff i * fixedClearedZeta i k) : ℤ) : ZMod 101) = _
    rw [fixed_rowP_typed_29, fixed_rowD_typed_29]
    simp only [fixed_rowP_typed_coeff_29, fixed_rowD_typed_coeff_29,
      Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]
  rw [h]
  clear h
  revert k
  decide +kernel

theorem fixedIntegerBaseCanonical_mod101_rows_24_29 (r : Fin 49) (hr : 24 ≤ r.val ∧ r.val < 30)
    (k : Fin 48) :
    (fixedIntegerBaseCanonical r k : ZMod 101) = fixedLiteralBaseMod r k := by
  obtain ⟨r, hr'⟩ := r
  obtain ⟨hra, hrb⟩ := hr
  simp only at hra hrb
  interval_cases r
  · exact splitBaseMod_row_24 k
  · exact splitBaseMod_row_25 k
  · exact splitBaseMod_row_26 k
  · exact splitBaseMod_row_27 k
  · exact splitBaseMod_row_28 k
  · exact splitBaseMod_row_29 k

end InternalCatalan

end OAI

end

section
open OAI.InternalCatalan

theorem solution (r : Fin 49) (hr : 24 ≤ r.val ∧ r.val < 30)
    (k : Fin 48) :
    (fixedIntegerBaseCanonical r k : ZMod 101) = fixedLiteralBaseMod r k := by
  first
  | exact @OAI.InternalCatalan.fixedIntegerBaseCanonical_mod101_rows_24_29
  | (apply OAI.InternalCatalan.fixedIntegerBaseCanonical_mod101_rows_24_29 <;> assumption)

end
