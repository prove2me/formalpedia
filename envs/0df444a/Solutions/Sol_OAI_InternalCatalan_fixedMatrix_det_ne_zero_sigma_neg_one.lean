-- Prove2me | solution 1 for OAI.InternalCatalan.fixedMatrix_det_ne_zero_sigma_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T19:27:56.972627+00:00
-- url     : https://prove2.me/submissions/da075039-aa94-41bb-b64c-b5969007335b

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
import Theorems.Thm_OAI_InternalCatalan_fixedIntegerBaseCanonical_cast_cols_0_11
import Theorems.Thm_OAI_InternalCatalan_fixedIntegerBaseCanonical_cast_cols_12_23
import Theorems.Thm_OAI_InternalCatalan_fixedIntegerBaseCanonical_cast_cols_24_35
import Theorems.Thm_OAI_InternalCatalan_fixedIntegerBaseCanonical_cast_cols_36_47
import Theorems.Thm_OAI_InternalCatalan_fixedIntegerBaseCanonical_mod101_rows_0_11
import Theorems.Thm_OAI_InternalCatalan_fixedIntegerBaseCanonical_mod101_rows_12_23
import Theorems.Thm_OAI_InternalCatalan_fixedIntegerBaseCanonical_mod101_rows_24_29
import Theorems.Thm_OAI_InternalCatalan_fixedIntegerBaseCanonical_mod101_rows_30_35
import Theorems.Thm_OAI_InternalCatalan_fixedIntegerBaseCanonical_mod101_rows_36_42
import Theorems.Thm_OAI_InternalCatalan_fixedIntegerBaseCanonical_mod101_rows_43_48
import Theorems.Thm_OAI_InternalCatalan_fixedLiteralModMinus_rightInverse_rows_0_23
import Theorems.Thm_OAI_InternalCatalan_fixedLiteralModMinus_rightInverse_rows_24_47

section
-- module Solutions.OAICatalan.Catalan.Estimates.TwoAdicQuadratic
namespace OAI

namespace InternalCatalan

section

def A (N : ℕ) : ℕ := 19 * N






















end

noncomputable section
open Set
open scoped BigOperators



end


end InternalCatalan

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
-- module Solutions.OAICatalan.Catalan.Polynomial.FixedBaseCertificateTransfer
namespace OAI

section

noncomputable section

namespace InternalCatalan

theorem fixedMatrix_det_ne_zero_of_integer_certificate
    (sigma : ℚ) (den : ℤ) (A : Matrix (Fin 48) (Fin 48) ℤ)
    (hA : A.map (fun x : ℤ => (x : ℚ)) = (den : ℚ) • fixedMatrix sigma)
    (hmod : (A.map (fun x : ℤ => (x : ZMod 101))).det ≠ 0) :
    (fixedMatrix sigma).det ≠ 0 := by
  intro hzero
  have hrat : (A.det : ℚ) = 0 := by
    rw [Int.cast_det, hA, Matrix.det_smul, hzero, mul_zero]
  have hint : A.det = 0 := by exact_mod_cast hrat
  apply hmod
  rw [← Int.cast_det, hint, Int.cast_zero]

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan

def fixedIntegerMatrix (A : Matrix (Fin 49) (Fin 48) ℤ) (sigma : ℤ) :
    Matrix (Fin 48) (Fin 48) ℤ :=
  fun r k => A r.castSucc k + sigma * A r.succ k

theorem fixedIntegerMatrix_cast_of_base_lift
    (A : Matrix (Fin 49) (Fin 48) ℤ) (den sigma : ℤ)
    (hbase : ∀ (r : Fin 49) (k : Fin 48),
      (A r k : ℚ) = (den : ℚ) * fixedBaseEntryRat r k) :
    (fixedIntegerMatrix A sigma).map (fun x : ℤ => (x : ℚ)) =
      (den : ℚ) • fixedMatrix (sigma : ℚ) := by
  ext r k
  change ((A r.castSucc k + sigma * A r.succ k : ℤ) : ℚ) =
    (den : ℚ) * (fixedBaseEntryRat r.castSucc k +
      (sigma : ℚ) * fixedBaseEntryRat r.succ k)
  rw [Int.cast_add, Int.cast_mul, hbase, hbase]
  ring

theorem fixedMatrix_det_ne_zero_of_base_certificate
    (A : Matrix (Fin 49) (Fin 48) ℤ) (den sigma : ℤ)
    (hbase : ∀ (r : Fin 49) (k : Fin 48),
      (A r k : ℚ) = (den : ℚ) * fixedBaseEntryRat r k)
    (hmod : ((fixedIntegerMatrix A sigma).map
      (fun x : ℤ => (x : ZMod 101))).det ≠ 0) :
    (fixedMatrix (sigma : ℚ)).det ≠ 0 :=
  fixedMatrix_det_ne_zero_of_integer_certificate (sigma : ℚ) den
    (fixedIntegerMatrix A sigma)
    (fixedIntegerMatrix_cast_of_base_lift A den sigma hbase) hmod

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows0To1
namespace OAI

section

namespace InternalCatalan













end InternalCatalan

end

section

namespace InternalCatalan



end InternalCatalan

end

section

namespace InternalCatalan




end InternalCatalan

end

section

namespace InternalCatalan



end InternalCatalan

end

section

namespace InternalCatalan



end InternalCatalan

end

section

namespace InternalCatalan



end InternalCatalan

end

section

namespace InternalCatalan



end InternalCatalan

end

section

namespace InternalCatalan



end InternalCatalan

end

section

namespace InternalCatalan



end InternalCatalan

end

section

namespace InternalCatalan



end InternalCatalan

end

section

namespace InternalCatalan



end InternalCatalan

end

section

namespace InternalCatalan



end InternalCatalan

end

section

namespace InternalCatalan



end InternalCatalan

end

section

namespace InternalCatalan



end InternalCatalan

end

section

namespace InternalCatalan



end InternalCatalan

end

section

namespace InternalCatalan



end InternalCatalan

end

section

namespace InternalCatalan



end InternalCatalan

end

section

namespace InternalCatalan



end InternalCatalan

end

section

namespace InternalCatalan



end InternalCatalan

end

section

namespace InternalCatalan



end InternalCatalan

end

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus_row_0 : ∀ k : Fin 48,
    fixedLiteralBaseMod (0 : Fin 48).castSucc k -
      fixedLiteralBaseMod (0 : Fin 48).succ k = fixedLiteralModMinus 0 k := by
  decide +kernel


theorem fixedLiteralBaseMod_minus_row_1 : ∀ k : Fin 48,
    fixedLiteralBaseMod (1 : Fin 48).castSucc k -
      fixedLiteralBaseMod (1 : Fin 48).succ k = fixedLiteralModMinus 1 k := by
  decide +kernel

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows10To11
namespace OAI

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus_row_10 : ∀ k : Fin 48,
    fixedLiteralBaseMod (10 : Fin 48).castSucc k -
      fixedLiteralBaseMod (10 : Fin 48).succ k = fixedLiteralModMinus 10 k := by
  decide +kernel


theorem fixedLiteralBaseMod_minus_row_11 : ∀ k : Fin 48,
    fixedLiteralBaseMod (11 : Fin 48).castSucc k -
      fixedLiteralBaseMod (11 : Fin 48).succ k = fixedLiteralModMinus 11 k := by
  decide +kernel

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows12To13
namespace OAI

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus_row_12 : ∀ k : Fin 48,
    fixedLiteralBaseMod (12 : Fin 48).castSucc k -
      fixedLiteralBaseMod (12 : Fin 48).succ k = fixedLiteralModMinus 12 k := by
  decide +kernel


theorem fixedLiteralBaseMod_minus_row_13 : ∀ k : Fin 48,
    fixedLiteralBaseMod (13 : Fin 48).castSucc k -
      fixedLiteralBaseMod (13 : Fin 48).succ k = fixedLiteralModMinus 13 k := by
  decide +kernel

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows14To15
namespace OAI

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus_row_14 : ∀ k : Fin 48,
    fixedLiteralBaseMod (14 : Fin 48).castSucc k -
      fixedLiteralBaseMod (14 : Fin 48).succ k = fixedLiteralModMinus 14 k := by
  decide +kernel


theorem fixedLiteralBaseMod_minus_row_15 : ∀ k : Fin 48,
    fixedLiteralBaseMod (15 : Fin 48).castSucc k -
      fixedLiteralBaseMod (15 : Fin 48).succ k = fixedLiteralModMinus 15 k := by
  decide +kernel

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows16To17
namespace OAI

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus_row_16 : ∀ k : Fin 48,
    fixedLiteralBaseMod (16 : Fin 48).castSucc k -
      fixedLiteralBaseMod (16 : Fin 48).succ k = fixedLiteralModMinus 16 k := by
  decide +kernel


theorem fixedLiteralBaseMod_minus_row_17 : ∀ k : Fin 48,
    fixedLiteralBaseMod (17 : Fin 48).castSucc k -
      fixedLiteralBaseMod (17 : Fin 48).succ k = fixedLiteralModMinus 17 k := by
  decide +kernel

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows18To19
namespace OAI

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus_row_18 : ∀ k : Fin 48,
    fixedLiteralBaseMod (18 : Fin 48).castSucc k -
      fixedLiteralBaseMod (18 : Fin 48).succ k = fixedLiteralModMinus 18 k := by
  decide +kernel


theorem fixedLiteralBaseMod_minus_row_19 : ∀ k : Fin 48,
    fixedLiteralBaseMod (19 : Fin 48).castSucc k -
      fixedLiteralBaseMod (19 : Fin 48).succ k = fixedLiteralModMinus 19 k := by
  decide +kernel

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows20To21
namespace OAI

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus_row_20 : ∀ k : Fin 48,
    fixedLiteralBaseMod (20 : Fin 48).castSucc k -
      fixedLiteralBaseMod (20 : Fin 48).succ k = fixedLiteralModMinus 20 k := by
  decide +kernel


theorem fixedLiteralBaseMod_minus_row_21 : ∀ k : Fin 48,
    fixedLiteralBaseMod (21 : Fin 48).castSucc k -
      fixedLiteralBaseMod (21 : Fin 48).succ k = fixedLiteralModMinus 21 k := by
  decide +kernel

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows22To23
namespace OAI

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus_row_22 : ∀ k : Fin 48,
    fixedLiteralBaseMod (22 : Fin 48).castSucc k -
      fixedLiteralBaseMod (22 : Fin 48).succ k = fixedLiteralModMinus 22 k := by
  decide +kernel


theorem fixedLiteralBaseMod_minus_row_23 : ∀ k : Fin 48,
    fixedLiteralBaseMod (23 : Fin 48).castSucc k -
      fixedLiteralBaseMod (23 : Fin 48).succ k = fixedLiteralModMinus 23 k := by
  decide +kernel

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows24To25
namespace OAI

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus_row_24 : ∀ k : Fin 48,
    fixedLiteralBaseMod (24 : Fin 48).castSucc k -
      fixedLiteralBaseMod (24 : Fin 48).succ k = fixedLiteralModMinus 24 k := by
  decide +kernel


theorem fixedLiteralBaseMod_minus_row_25 : ∀ k : Fin 48,
    fixedLiteralBaseMod (25 : Fin 48).castSucc k -
      fixedLiteralBaseMod (25 : Fin 48).succ k = fixedLiteralModMinus 25 k := by
  decide +kernel

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows26To27
namespace OAI

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus_row_26 : ∀ k : Fin 48,
    fixedLiteralBaseMod (26 : Fin 48).castSucc k -
      fixedLiteralBaseMod (26 : Fin 48).succ k = fixedLiteralModMinus 26 k := by
  decide +kernel


theorem fixedLiteralBaseMod_minus_row_27 : ∀ k : Fin 48,
    fixedLiteralBaseMod (27 : Fin 48).castSucc k -
      fixedLiteralBaseMod (27 : Fin 48).succ k = fixedLiteralModMinus 27 k := by
  decide +kernel

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows28To29
namespace OAI

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus_row_28 : ∀ k : Fin 48,
    fixedLiteralBaseMod (28 : Fin 48).castSucc k -
      fixedLiteralBaseMod (28 : Fin 48).succ k = fixedLiteralModMinus 28 k := by
  decide +kernel


theorem fixedLiteralBaseMod_minus_row_29 : ∀ k : Fin 48,
    fixedLiteralBaseMod (29 : Fin 48).castSucc k -
      fixedLiteralBaseMod (29 : Fin 48).succ k = fixedLiteralModMinus 29 k := by
  decide +kernel

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows2To3
namespace OAI

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus_row_2 : ∀ k : Fin 48,
    fixedLiteralBaseMod (2 : Fin 48).castSucc k -
      fixedLiteralBaseMod (2 : Fin 48).succ k = fixedLiteralModMinus 2 k := by
  decide +kernel


theorem fixedLiteralBaseMod_minus_row_3 : ∀ k : Fin 48,
    fixedLiteralBaseMod (3 : Fin 48).castSucc k -
      fixedLiteralBaseMod (3 : Fin 48).succ k = fixedLiteralModMinus 3 k := by
  decide +kernel

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows30To31
namespace OAI

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus_row_30 : ∀ k : Fin 48,
    fixedLiteralBaseMod (30 : Fin 48).castSucc k -
      fixedLiteralBaseMod (30 : Fin 48).succ k = fixedLiteralModMinus 30 k := by
  decide +kernel


theorem fixedLiteralBaseMod_minus_row_31 : ∀ k : Fin 48,
    fixedLiteralBaseMod (31 : Fin 48).castSucc k -
      fixedLiteralBaseMod (31 : Fin 48).succ k = fixedLiteralModMinus 31 k := by
  decide +kernel

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FiniteMatrices.FixedDeterminantsNonzero
namespace OAI

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus_row_32 : ∀ k : Fin 48,
    fixedLiteralBaseMod (32 : Fin 48).castSucc k -
      fixedLiteralBaseMod (32 : Fin 48).succ k = fixedLiteralModMinus 32 k := by
  decide +kernel


theorem fixedLiteralBaseMod_minus_row_33 : ∀ k : Fin 48,
    fixedLiteralBaseMod (33 : Fin 48).castSucc k -
      fixedLiteralBaseMod (33 : Fin 48).succ k = fixedLiteralModMinus 33 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus_row_34 : ∀ k : Fin 48,
    fixedLiteralBaseMod (34 : Fin 48).castSucc k -
      fixedLiteralBaseMod (34 : Fin 48).succ k = fixedLiteralModMinus 34 k := by
  decide +kernel


theorem fixedLiteralBaseMod_minus_row_35 : ∀ k : Fin 48,
    fixedLiteralBaseMod (35 : Fin 48).castSucc k -
      fixedLiteralBaseMod (35 : Fin 48).succ k = fixedLiteralModMinus 35 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus_row_36 : ∀ k : Fin 48,
    fixedLiteralBaseMod (36 : Fin 48).castSucc k -
      fixedLiteralBaseMod (36 : Fin 48).succ k = fixedLiteralModMinus 36 k := by
  decide +kernel


theorem fixedLiteralBaseMod_minus_row_37 : ∀ k : Fin 48,
    fixedLiteralBaseMod (37 : Fin 48).castSucc k -
      fixedLiteralBaseMod (37 : Fin 48).succ k = fixedLiteralModMinus 37 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus_row_38 : ∀ k : Fin 48,
    fixedLiteralBaseMod (38 : Fin 48).castSucc k -
      fixedLiteralBaseMod (38 : Fin 48).succ k = fixedLiteralModMinus 38 k := by
  decide +kernel


theorem fixedLiteralBaseMod_minus_row_39 : ∀ k : Fin 48,
    fixedLiteralBaseMod (39 : Fin 48).castSucc k -
      fixedLiteralBaseMod (39 : Fin 48).succ k = fixedLiteralModMinus 39 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus_row_40 : ∀ k : Fin 48,
    fixedLiteralBaseMod (40 : Fin 48).castSucc k -
      fixedLiteralBaseMod (40 : Fin 48).succ k = fixedLiteralModMinus 40 k := by
  decide +kernel


theorem fixedLiteralBaseMod_minus_row_41 : ∀ k : Fin 48,
    fixedLiteralBaseMod (41 : Fin 48).castSucc k -
      fixedLiteralBaseMod (41 : Fin 48).succ k = fixedLiteralModMinus 41 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus_row_42 : ∀ k : Fin 48,
    fixedLiteralBaseMod (42 : Fin 48).castSucc k -
      fixedLiteralBaseMod (42 : Fin 48).succ k = fixedLiteralModMinus 42 k := by
  decide +kernel


theorem fixedLiteralBaseMod_minus_row_43 : ∀ k : Fin 48,
    fixedLiteralBaseMod (43 : Fin 48).castSucc k -
      fixedLiteralBaseMod (43 : Fin 48).succ k = fixedLiteralModMinus 43 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus_row_44 : ∀ k : Fin 48,
    fixedLiteralBaseMod (44 : Fin 48).castSucc k -
      fixedLiteralBaseMod (44 : Fin 48).succ k = fixedLiteralModMinus 44 k := by
  decide +kernel


theorem fixedLiteralBaseMod_minus_row_45 : ∀ k : Fin 48,
    fixedLiteralBaseMod (45 : Fin 48).castSucc k -
      fixedLiteralBaseMod (45 : Fin 48).succ k = fixedLiteralModMinus 45 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus_row_46 : ∀ k : Fin 48,
    fixedLiteralBaseMod (46 : Fin 48).castSucc k -
      fixedLiteralBaseMod (46 : Fin 48).succ k = fixedLiteralModMinus 46 k := by
  decide +kernel


theorem fixedLiteralBaseMod_minus_row_47 : ∀ k : Fin 48,
    fixedLiteralBaseMod (47 : Fin 48).castSucc k -
      fixedLiteralBaseMod (47 : Fin 48).succ k = fixedLiteralModMinus 47 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus_row_4 : ∀ k : Fin 48,
    fixedLiteralBaseMod (4 : Fin 48).castSucc k -
      fixedLiteralBaseMod (4 : Fin 48).succ k = fixedLiteralModMinus 4 k := by
  decide +kernel


theorem fixedLiteralBaseMod_minus_row_5 : ∀ k : Fin 48,
    fixedLiteralBaseMod (5 : Fin 48).castSucc k -
      fixedLiteralBaseMod (5 : Fin 48).succ k = fixedLiteralModMinus 5 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus_row_6 : ∀ k : Fin 48,
    fixedLiteralBaseMod (6 : Fin 48).castSucc k -
      fixedLiteralBaseMod (6 : Fin 48).succ k = fixedLiteralModMinus 6 k := by
  decide +kernel


theorem fixedLiteralBaseMod_minus_row_7 : ∀ k : Fin 48,
    fixedLiteralBaseMod (7 : Fin 48).castSucc k -
      fixedLiteralBaseMod (7 : Fin 48).succ k = fixedLiteralModMinus 7 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus_row_8 : ∀ k : Fin 48,
    fixedLiteralBaseMod (8 : Fin 48).castSucc k -
      fixedLiteralBaseMod (8 : Fin 48).succ k = fixedLiteralModMinus 8 k := by
  decide +kernel


theorem fixedLiteralBaseMod_minus_row_9 : ∀ k : Fin 48,
    fixedLiteralBaseMod (9 : Fin 48).castSucc k -
      fixedLiteralBaseMod (9 : Fin 48).succ k = fixedLiteralModMinus 9 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan


theorem fixedLiteralBaseMod_minus (r k : Fin 48) :
    fixedLiteralBaseMod r.castSucc k - fixedLiteralBaseMod r.succ k =
      fixedLiteralModMinus r k := by
  fin_cases r
  · exact fixedLiteralBaseMod_minus_row_0 k
  · exact fixedLiteralBaseMod_minus_row_1 k
  · exact fixedLiteralBaseMod_minus_row_2 k
  · exact fixedLiteralBaseMod_minus_row_3 k
  · exact fixedLiteralBaseMod_minus_row_4 k
  · exact fixedLiteralBaseMod_minus_row_5 k
  · exact fixedLiteralBaseMod_minus_row_6 k
  · exact fixedLiteralBaseMod_minus_row_7 k
  · exact fixedLiteralBaseMod_minus_row_8 k
  · exact fixedLiteralBaseMod_minus_row_9 k
  · exact fixedLiteralBaseMod_minus_row_10 k
  · exact fixedLiteralBaseMod_minus_row_11 k
  · exact fixedLiteralBaseMod_minus_row_12 k
  · exact fixedLiteralBaseMod_minus_row_13 k
  · exact fixedLiteralBaseMod_minus_row_14 k
  · exact fixedLiteralBaseMod_minus_row_15 k
  · exact fixedLiteralBaseMod_minus_row_16 k
  · exact fixedLiteralBaseMod_minus_row_17 k
  · exact fixedLiteralBaseMod_minus_row_18 k
  · exact fixedLiteralBaseMod_minus_row_19 k
  · exact fixedLiteralBaseMod_minus_row_20 k
  · exact fixedLiteralBaseMod_minus_row_21 k
  · exact fixedLiteralBaseMod_minus_row_22 k
  · exact fixedLiteralBaseMod_minus_row_23 k
  · exact fixedLiteralBaseMod_minus_row_24 k
  · exact fixedLiteralBaseMod_minus_row_25 k
  · exact fixedLiteralBaseMod_minus_row_26 k
  · exact fixedLiteralBaseMod_minus_row_27 k
  · exact fixedLiteralBaseMod_minus_row_28 k
  · exact fixedLiteralBaseMod_minus_row_29 k
  · exact fixedLiteralBaseMod_minus_row_30 k
  · exact fixedLiteralBaseMod_minus_row_31 k
  · exact fixedLiteralBaseMod_minus_row_32 k
  · exact fixedLiteralBaseMod_minus_row_33 k
  · exact fixedLiteralBaseMod_minus_row_34 k
  · exact fixedLiteralBaseMod_minus_row_35 k
  · exact fixedLiteralBaseMod_minus_row_36 k
  · exact fixedLiteralBaseMod_minus_row_37 k
  · exact fixedLiteralBaseMod_minus_row_38 k
  · exact fixedLiteralBaseMod_minus_row_39 k
  · exact fixedLiteralBaseMod_minus_row_40 k
  · exact fixedLiteralBaseMod_minus_row_41 k
  · exact fixedLiteralBaseMod_minus_row_42 k
  · exact fixedLiteralBaseMod_minus_row_43 k
  · exact fixedLiteralBaseMod_minus_row_44 k
  · exact fixedLiteralBaseMod_minus_row_45 k
  · exact fixedLiteralBaseMod_minus_row_46 k
  · exact fixedLiteralBaseMod_minus_row_47 k

end InternalCatalan

end

section

noncomputable section
namespace InternalCatalan




end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan




end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Split.FixedInv
/-! Glue for the split of OpenAI's Catalan development (not OpenAI code): the right-inverse
certificates of the three fixed matrices modulo 101, in halves, and the determinants from them. -/

namespace OAI

namespace InternalCatalan









theorem splitLiteralModMinus_det_ne_zero : fixedLiteralModMinus.det ≠ 0 := by
  have hinv : fixedLiteralModMinus * fixedLiteralInvMinus = (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) := by
    ext i k
    by_cases h : i.val < 24
    · exact fixedLiteralModMinus_rightInverse_rows_0_23 i ⟨by omega, h⟩ k
    · exact fixedLiteralModMinus_rightInverse_rows_24_47 i ⟨by omega, i.isLt⟩ k
  intro hz
  have h := congrArg Matrix.det hinv
  rw [Matrix.det_mul, Matrix.det_one, hz, zero_mul] at h
  have hzero_ne_one : (0 : ZMod 101) ≠ 1 := by decide
  exact hzero_ne_one h


end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Split.FixedDet
/-! Glue for the split of OpenAI's Catalan development (not OpenAI code): the three fixed
determinants of Eq. (48), one statement each. -/

namespace OAI

namespace InternalCatalan

theorem splitIntegerBaseCanonical_cast_all (r : Fin 49) (k : Fin 48) :
    (fixedIntegerBaseCanonical r k : ℚ) =
      ((854041599922236190937524347070927377276592590715779683450880000 : ℤ) : ℚ) * fixedBaseEntryRat r k := by
  have h : (fixedIntegerBaseCanonical r k : ℚ) = (854041599922236190937524347070927377276592590715779683450880000 : ℚ) * fixedBaseEntryRat r k := by
    by_cases h0 : k.val < 12
    · exact fixedIntegerBaseCanonical_cast_cols_0_11 r k ⟨by omega, h0⟩
    by_cases h1 : k.val < 24
    · exact fixedIntegerBaseCanonical_cast_cols_12_23 r k ⟨by omega, h1⟩
    by_cases h2 : k.val < 36
    · exact fixedIntegerBaseCanonical_cast_cols_24_35 r k ⟨by omega, h2⟩
    exact fixedIntegerBaseCanonical_cast_cols_36_47 r k ⟨by omega, k.isLt⟩
  rw [h]
  norm_num

theorem splitIntegerBaseCanonical_mod_all (r : Fin 49) (k : Fin 48) :
    (fixedIntegerBaseCanonical r k : ZMod 101) = fixedLiteralBaseMod r k := by
  by_cases h0 : r.val < 12
  · exact fixedIntegerBaseCanonical_mod101_rows_0_11 r ⟨by omega, h0⟩ k
  by_cases h1 : r.val < 24
  · exact fixedIntegerBaseCanonical_mod101_rows_12_23 r ⟨by omega, h1⟩ k
  by_cases h2 : r.val < 30
  · exact fixedIntegerBaseCanonical_mod101_rows_24_29 r ⟨by omega, h2⟩ k
  by_cases h3 : r.val < 36
  · exact fixedIntegerBaseCanonical_mod101_rows_30_35 r ⟨by omega, h3⟩ k
  by_cases h4 : r.val < 43
  · exact fixedIntegerBaseCanonical_mod101_rows_36_42 r ⟨by omega, h4⟩ k
  exact fixedIntegerBaseCanonical_mod101_rows_43_48 r ⟨by omega, r.isLt⟩ k




theorem fixedMatrix_det_ne_zero_sigma_neg_one : (fixedMatrix (-1)).det ≠ 0 := by
  have hmod : ((fixedIntegerMatrix fixedIntegerBaseCanonical (-1)).map
      (fun x : ℤ => (x : ZMod 101))).det ≠ 0 := by
    have he : (fixedIntegerMatrix fixedIntegerBaseCanonical (-1)).map
        (fun x : ℤ => (x : ZMod 101)) = fixedLiteralModMinus := by
      ext r k
      change ((fixedIntegerBaseCanonical r.castSucc k + (-1) * fixedIntegerBaseCanonical r.succ k : ℤ) :
        ZMod 101) = _
      rw [neg_one_mul, Int.cast_add, Int.cast_neg, splitIntegerBaseCanonical_mod_all,
        splitIntegerBaseCanonical_mod_all]
      simpa only [sub_eq_add_neg] using fixedLiteralBaseMod_minus r k
    rw [he]
    exact splitLiteralModMinus_det_ne_zero
  simpa only [Int.cast_neg, Int.cast_one] using
    fixedMatrix_det_ne_zero_of_base_certificate fixedIntegerBaseCanonical
      854041599922236190937524347070927377276592590715779683450880000 (-1) splitIntegerBaseCanonical_cast_all hmod

end InternalCatalan

end OAI

end

section
open OAI.InternalCatalan

theorem solution : (fixedMatrix (-1)).det ≠ 0 := by
  first
  | exact @OAI.InternalCatalan.fixedMatrix_det_ne_zero_sigma_neg_one
  | (apply OAI.InternalCatalan.fixedMatrix_det_ne_zero_sigma_neg_one <;> assumption)

end
