-- Prove2me | solution 1 for OAI.InternalCatalan.fixedLiteralModZero_rightInverse_rows_24_47
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T19:27:00.794839+00:00
-- url     : https://prove2.me/submissions/3f4fdbc6-9ff4-4821-9fe3-ef5828a28632

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

theorem fixedLiteralModZero_rightInverse_row_24 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 24 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 24 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_25 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 25 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 25 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_26 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 26 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 26 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_27 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 27 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 27 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_28 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 28 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 28 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_29 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 29 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 29 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan



end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_30 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 30 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 30 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_31 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 31 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 31 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_32 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 32 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 32 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_33 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 33 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 33 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_34 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 34 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 34 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_35 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 35 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 35 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_36 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 36 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 36 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_37 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 37 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 37 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_38 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 38 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 38 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_39 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 39 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 39 k := by
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
-- module Solutions.OAICatalan.Catalan.FiniteMatrices.FixedModularZeroRightInverse
namespace OAI

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_40 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 40 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 40 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_41 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 41 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 41 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_42 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 42 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 42 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_43 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 43 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 43 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_44 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 44 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 44 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_45 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 45 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 45 k := by
  decide +kernel

end InternalCatalan

end

section

namespace InternalCatalan

theorem fixedLiteralModZero_rightInverse_row_46 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 46 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 46 k := by
  decide +kernel

theorem fixedLiteralModZero_rightInverse_row_47 : ∀ k : Fin 48,
    (fixedLiteralModZero * fixedLiteralInvZero) 47 k =
      (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) 47 k := by
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

end OAI

end

section
-- module Solutions.OAICatalan.Split.FixedInv
/-! Glue for the split of OpenAI's Catalan development (not OpenAI code): the right-inverse
certificates of the three fixed matrices modulo 101, in halves, and the determinants from them. -/

namespace OAI

namespace InternalCatalan


theorem fixedLiteralModZero_rightInverse_rows_24_47 (i : Fin 48)
    (hi : 24 ≤ i.val ∧ i.val < 48) (k : Fin 48) :
    (fixedLiteralModZero * fixedLiteralInvZero) i k = (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) i k := by
  obtain ⟨i, hi'⟩ := i
  obtain ⟨hia, hib⟩ := hi
  simp only at hia hib
  interval_cases i
  · exact fixedLiteralModZero_rightInverse_row_24 k
  · exact fixedLiteralModZero_rightInverse_row_25 k
  · exact fixedLiteralModZero_rightInverse_row_26 k
  · exact fixedLiteralModZero_rightInverse_row_27 k
  · exact fixedLiteralModZero_rightInverse_row_28 k
  · exact fixedLiteralModZero_rightInverse_row_29 k
  · exact fixedLiteralModZero_rightInverse_row_30 k
  · exact fixedLiteralModZero_rightInverse_row_31 k
  · exact fixedLiteralModZero_rightInverse_row_32 k
  · exact fixedLiteralModZero_rightInverse_row_33 k
  · exact fixedLiteralModZero_rightInverse_row_34 k
  · exact fixedLiteralModZero_rightInverse_row_35 k
  · exact fixedLiteralModZero_rightInverse_row_36 k
  · exact fixedLiteralModZero_rightInverse_row_37 k
  · exact fixedLiteralModZero_rightInverse_row_38 k
  · exact fixedLiteralModZero_rightInverse_row_39 k
  · exact fixedLiteralModZero_rightInverse_row_40 k
  · exact fixedLiteralModZero_rightInverse_row_41 k
  · exact fixedLiteralModZero_rightInverse_row_42 k
  · exact fixedLiteralModZero_rightInverse_row_43 k
  · exact fixedLiteralModZero_rightInverse_row_44 k
  · exact fixedLiteralModZero_rightInverse_row_45 k
  · exact fixedLiteralModZero_rightInverse_row_46 k
  · exact fixedLiteralModZero_rightInverse_row_47 k









end InternalCatalan

end OAI

end

section
open OAI.InternalCatalan

theorem solution (i : Fin 48)
    (hi : 24 ≤ i.val ∧ i.val < 48) (k : Fin 48) :
    (fixedLiteralModZero * fixedLiteralInvZero) i k = (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) i k := by
  first
  | exact @OAI.InternalCatalan.fixedLiteralModZero_rightInverse_rows_24_47
  | (apply OAI.InternalCatalan.fixedLiteralModZero_rightInverse_rows_24_47 <;> assumption)

end
