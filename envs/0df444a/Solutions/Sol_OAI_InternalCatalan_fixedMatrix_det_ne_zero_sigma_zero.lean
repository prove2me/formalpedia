-- Prove2me | solution 1 for OAI.InternalCatalan.fixedMatrix_det_ne_zero_sigma_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T19:29:48.111166+00:00
-- url     : https://prove2.me/submissions/83daf11f-2937-4231-bd76-3748048d2b3d

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
import Theorems.Thm_OAI_InternalCatalan_fixedLiteralModZero_rightInverse_rows_0_23
import Theorems.Thm_OAI_InternalCatalan_fixedLiteralModZero_rightInverse_rows_24_47

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


theorem fixedLiteralBaseMod_zero (r k : Fin 48) :
    fixedLiteralBaseMod r.castSucc k = fixedLiteralModZero r k := by
  fin_cases r <;> rfl


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

end OAI

end

section
-- module Solutions.OAICatalan.Split.FixedInv
/-! Glue for the split of OpenAI's Catalan development (not OpenAI code): the right-inverse
certificates of the three fixed matrices modulo 101, in halves, and the determinants from them. -/

namespace OAI

namespace InternalCatalan



theorem splitLiteralModZero_det_ne_zero : fixedLiteralModZero.det ≠ 0 := by
  have hinv : fixedLiteralModZero * fixedLiteralInvZero = (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) := by
    ext i k
    by_cases h : i.val < 24
    · exact fixedLiteralModZero_rightInverse_rows_0_23 i ⟨by omega, h⟩ k
    · exact fixedLiteralModZero_rightInverse_rows_24_47 i ⟨by omega, i.isLt⟩ k
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


theorem fixedMatrix_det_ne_zero_sigma_zero : (fixedMatrix 0).det ≠ 0 := by
  have hmod : ((fixedIntegerMatrix fixedIntegerBaseCanonical 0).map
      (fun x : ℤ => (x : ZMod 101))).det ≠ 0 := by
    have he : (fixedIntegerMatrix fixedIntegerBaseCanonical 0).map
        (fun x : ℤ => (x : ZMod 101)) = fixedLiteralModZero := by
      ext r k
      change ((fixedIntegerBaseCanonical r.castSucc k + 0 * fixedIntegerBaseCanonical r.succ k : ℤ) :
        ZMod 101) = _
      rw [zero_mul, add_zero, splitIntegerBaseCanonical_mod_all]
      exact fixedLiteralBaseMod_zero r k
    rw [he]
    exact splitLiteralModZero_det_ne_zero
  simpa only [Int.cast_zero] using
    fixedMatrix_det_ne_zero_of_base_certificate fixedIntegerBaseCanonical
      854041599922236190937524347070927377276592590715779683450880000 0 splitIntegerBaseCanonical_cast_all hmod



end InternalCatalan

end OAI

end

section
open OAI.InternalCatalan

theorem solution : (fixedMatrix 0).det ≠ 0 := by
  first
  | exact @OAI.InternalCatalan.fixedMatrix_det_ne_zero_sigma_zero
  | (apply OAI.InternalCatalan.fixedMatrix_det_ne_zero_sigma_zero <;> assumption)

end
