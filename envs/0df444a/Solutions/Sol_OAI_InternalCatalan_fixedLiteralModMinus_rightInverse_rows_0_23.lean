-- Prove2me | solution 1 for OAI.InternalCatalan.fixedLiteralModMinus_rightInverse_rows_0_23
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T19:21:29.816748+00:00
-- url     : https://prove2.me/submissions/792fa654-75d7-4125-a4f4-36ffff77cfa1

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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_OAICatalanIrrationality

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
-- module Solutions.OAICatalan.Catalan.FiniteMatrices.FixedModularMinusProductRows40To41
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

theorem fixedLiteralModMinus_rightInverse_row_0 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 0 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 0 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_1 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 1 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 1 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_10 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 10 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 10 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_11 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 11 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 11 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_12 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 12 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 12 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_13 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 13 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 13 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_14 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 14 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 14 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_15 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 15 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 15 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_16 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 16 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 16 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_17 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 17 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 17 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_18 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 18 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 18 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_19 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 19 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 19 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_20 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 20 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 20 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_21 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 21 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 21 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_22 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 22 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 22 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_23 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 23 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 23 k := by
  decide +kernel

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

theorem fixedLiteralModMinus_rightInverse_row_2 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 2 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 2 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_3 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 3 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 3 k := by
  decide +kernel

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
-- module Solutions.OAICatalan.Catalan.FiniteMatrices.FixedModularMinusRightInverse
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

theorem fixedLiteralModMinus_rightInverse_row_4 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 4 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 4 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_5 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 5 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 5 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_6 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 6 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 6 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_7 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 7 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 7 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModMinus_rightInverse_row_8 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 8 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 8 k := by
  decide +kernel

theorem fixedLiteralModMinus_rightInverse_row_9 : ∀ k : Fin 48,
    (fixedLiteralModMinus * fixedLiteralInvMinus) 9 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 9 k := by
  decide +kernel

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







theorem fixedLiteralModMinus_rightInverse_rows_0_23 (i : Fin 48)
    (hi : 0 ≤ i.val ∧ i.val < 24) (k : Fin 48) :
    (fixedLiteralModMinus * fixedLiteralInvMinus) i k = (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) i k := by
  obtain ⟨i, hi'⟩ := i
  obtain ⟨hia, hib⟩ := hi
  simp only at hia hib
  interval_cases i
  · exact fixedLiteralModMinus_rightInverse_row_0 k
  · exact fixedLiteralModMinus_rightInverse_row_1 k
  · exact fixedLiteralModMinus_rightInverse_row_2 k
  · exact fixedLiteralModMinus_rightInverse_row_3 k
  · exact fixedLiteralModMinus_rightInverse_row_4 k
  · exact fixedLiteralModMinus_rightInverse_row_5 k
  · exact fixedLiteralModMinus_rightInverse_row_6 k
  · exact fixedLiteralModMinus_rightInverse_row_7 k
  · exact fixedLiteralModMinus_rightInverse_row_8 k
  · exact fixedLiteralModMinus_rightInverse_row_9 k
  · exact fixedLiteralModMinus_rightInverse_row_10 k
  · exact fixedLiteralModMinus_rightInverse_row_11 k
  · exact fixedLiteralModMinus_rightInverse_row_12 k
  · exact fixedLiteralModMinus_rightInverse_row_13 k
  · exact fixedLiteralModMinus_rightInverse_row_14 k
  · exact fixedLiteralModMinus_rightInverse_row_15 k
  · exact fixedLiteralModMinus_rightInverse_row_16 k
  · exact fixedLiteralModMinus_rightInverse_row_17 k
  · exact fixedLiteralModMinus_rightInverse_row_18 k
  · exact fixedLiteralModMinus_rightInverse_row_19 k
  · exact fixedLiteralModMinus_rightInverse_row_20 k
  · exact fixedLiteralModMinus_rightInverse_row_21 k
  · exact fixedLiteralModMinus_rightInverse_row_22 k
  · exact fixedLiteralModMinus_rightInverse_row_23 k




end InternalCatalan

end OAI

end

section
open OAI.InternalCatalan

theorem solution (i : Fin 48)
    (hi : 0 ≤ i.val ∧ i.val < 24) (k : Fin 48) :
    (fixedLiteralModMinus * fixedLiteralInvMinus) i k = (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) i k := by
  first
  | exact @OAI.InternalCatalan.fixedLiteralModMinus_rightInverse_rows_0_23
  | (apply OAI.InternalCatalan.fixedLiteralModMinus_rightInverse_rows_0_23 <;> assumption)

end
