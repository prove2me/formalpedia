-- Prove2me | solution 1 for OAI.InternalCatalan.fixedIntegerBaseCanonical_cast_cols_42_47
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T21:26:04.369056+00:00
-- url     : https://prove2.me/submissions/08954306-770d-401c-9269-a03df02d281a

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.Defs
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
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue
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



theorem reversedRow_coeff_eq_zero_of_lt (C d : ℕ) (F : ℤ[X])
    (hF : F.natDegree ≤ d) (hd : d < C) {i : ℕ} (hi : i < C - 1 - d) :
    (reversedRow C F).coeff i = 0 := by
  rw [reversedRow_coeff, if_pos (by omega)]
  apply coeff_eq_zero_of_natDegree_lt
  omega

theorem coeff_mul_eq_zero_below_right (P Q : ℤ[X]) (B : ℕ)
    (hQ : ∀ i < B, Q.coeff i = 0) {k : ℕ} (hk : k < B) :
    (P * Q).coeff k = 0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  have hij' : i + j = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [hQ j (by omega), mul_zero]






theorem rowD_eq_zero_of_distance_zero {N r : ℕ} (hd : rowDistance N r = 0) :
    rowD N r = 0 := by
  simp [rowD, hd]





















theorem fixed_rowDistance_le44 (r : Fin 49) : rowDistance 1 r.val ≤ 44 := by
  have hr := r.isLt
  unfold rowDistance rowOffset g
  omega

theorem fixed_rowP_coeff_eq_zero_below18 (r : Fin 49) {i : ℕ} (hi : i < 18) :
    (rowP 1 r.val).coeff i = 0 := by
  have hdist := fixed_rowDistance_le44 r
  unfold rowP
  apply coeff_mul_eq_zero_below_right _ _ 18 _ hi
  intro j hj
  apply reversedRow_coeff_eq_zero_of_lt _ (rowDistance 1 r.val) _
  · simp [Chebyshev.natDegree_T]
  · change rowDistance 1 r.val < 63
    omega
  · change j < 63 - 1 - rowDistance 1 r.val
    omega

theorem fixed_rowD_coeff_eq_zero_below19 (r : Fin 49) {i : ℕ} (hi : i < 19) :
    (rowD 1 r.val).coeff i = 0 := by
  by_cases hd : rowDistance 1 r.val = 0
  · simp [rowD_eq_zero_of_distance_zero hd]
  · have hdist := fixed_rowDistance_le44 r
    unfold rowD
    apply coeff_mul_eq_zero_below_right _ _ 19 _ hi
    intro j hj
    apply reversedRow_coeff_eq_zero_of_lt _ (rowDistance 1 r.val - 1) _
    · simp [Chebyshev.natDegree_U]
    · change rowDistance 1 r.val - 1 < 63
      omega
    · change j < 63 - 1 - (rowDistance 1 r.val - 1)
      omega

end

section

open scoped BigOperators






theorem rawEntryRat_zero (N r j : ℕ) :
    rawEntryRat 0 N r j =
      (∑ i ∈ Finset.range (H N), ((rowP N r).coeff i : ℚ) * momentRat i j) -
      (3 / 2 : ℚ) *
        ∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℚ) * zetaRat i j := by
  simp [rawEntryRat]



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

def fixedFilteredMomentRat (i k : ℕ) : ℚ :=
  ∑ v ∈ Finset.range 5, filterCoeffRat 1 v * momentRat i (7 + k + v)

def fixedFilteredZetaRat (i k : ℕ) : ℚ :=
  ∑ v ∈ Finset.range 5, filterCoeffRat 1 v * zetaRat i (7 + k + v)

theorem fixedBaseEntry_dot_filtered (r : Fin 49) (k : Fin 48) :
    fixedBaseEntryRat r k =
      (∑ i ∈ Finset.range 65, ((rowP 1 r.val).coeff i : ℚ) *
        fixedFilteredMomentRat i k.val) -
      (3 / 2 : ℚ) * ∑ i ∈ Finset.range 65,
        ((rowD 1 r.val).coeff i : ℚ) * fixedFilteredZetaRat i k.val := by
  change (∑ v ∈ Finset.range 5,
    filterCoeffRat 1 v * rawEntryRat 0 1 r.val (7 + k.val + v)) = _
  simp_rw [rawEntryRat_zero]
  change (∑ v ∈ Finset.range 5, filterCoeffRat 1 v *
    ((∑ i ∈ Finset.range 65, ((rowP 1 r.val).coeff i : ℚ) *
      momentRat i (7 + k.val + v)) -
    (3 / 2 : ℚ) * ∑ i ∈ Finset.range 65, ((rowD 1 r.val).coeff i : ℚ) *
      zetaRat i (7 + k.val + v))) = _
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  unfold fixedFilteredMomentRat fixedFilteredZetaRat
  congr 1
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro v hv
    ring
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro v hv
    ring

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
-- module Solutions.OAICatalan.Catalan.Arithmetic.FixedAuxiliaryIntegerPilot
namespace OAI


noncomputable section
open scoped BigOperators
namespace InternalCatalan


theorem fixedFilteredMoment47_cleared (i : ℕ) (hlo : 18 ≤ i) (hhi : i < 65) :
    fixedFilteredMomentRat i 47 = (fixedClearedMoment47 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 18 ≤ j.val →
      fixedFilteredMomentRat j.val 47 = (fixedClearedMoment47 j.val : ℚ) /
        427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo


theorem fixedFilteredZeta47_cleared (i : ℕ) (hlo : 19 ≤ i) (hhi : i < 65) :
    fixedFilteredZetaRat i 47 = (fixedClearedZeta47 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 19 ≤ j.val →
      fixedFilteredZetaRat j.val 47 = (fixedClearedZeta47 j.val : ℚ) /
        427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo















































end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedMomentColumn42
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredMoment42_cleared (i : ℕ) (hlo : 18 ≤ i) (hhi : i < 65) :
    fixedFilteredMomentRat i 42 = (fixedClearedMoment42 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 18 ≤ j.val →
      fixedFilteredMomentRat j.val 42 = (fixedClearedMoment42 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedMomentColumn43
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredMoment43_cleared (i : ℕ) (hlo : 18 ≤ i) (hhi : i < 65) :
    fixedFilteredMomentRat i 43 = (fixedClearedMoment43 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 18 ≤ j.val →
      fixedFilteredMomentRat j.val 43 = (fixedClearedMoment43 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedMomentColumn44
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredMoment44_cleared (i : ℕ) (hlo : 18 ≤ i) (hhi : i < 65) :
    fixedFilteredMomentRat i 44 = (fixedClearedMoment44 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 18 ≤ j.val →
      fixedFilteredMomentRat j.val 44 = (fixedClearedMoment44 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedMomentColumn45
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredMoment45_cleared (i : ℕ) (hlo : 18 ≤ i) (hhi : i < 65) :
    fixedFilteredMomentRat i 45 = (fixedClearedMoment45 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 18 ≤ j.val →
      fixedFilteredMomentRat j.val 45 = (fixedClearedMoment45 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedMomentColumn46
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredMoment46_cleared (i : ℕ) (hlo : 18 ≤ i) (hhi : i < 65) :
    fixedFilteredMomentRat i 46 = (fixedClearedMoment46 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 18 ≤ j.val →
      fixedFilteredMomentRat j.val 46 = (fixedClearedMoment46 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedZetaColumn42
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredZeta42_cleared (i : ℕ) (hlo : 19 ≤ i) (hhi : i < 65) :
    fixedFilteredZetaRat i 42 = (fixedClearedZeta42 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 19 ≤ j.val →
      fixedFilteredZetaRat j.val 42 = (fixedClearedZeta42 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedZetaColumn43
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredZeta43_cleared (i : ℕ) (hlo : 19 ≤ i) (hhi : i < 65) :
    fixedFilteredZetaRat i 43 = (fixedClearedZeta43 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 19 ≤ j.val →
      fixedFilteredZetaRat j.val 43 = (fixedClearedZeta43 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedZetaColumn44
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredZeta44_cleared (i : ℕ) (hlo : 19 ≤ i) (hhi : i < 65) :
    fixedFilteredZetaRat i 44 = (fixedClearedZeta44 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 19 ≤ j.val →
      fixedFilteredZetaRat j.val 44 = (fixedClearedZeta44 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedZetaColumn45
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredZeta45_cleared (i : ℕ) (hlo : 19 ≤ i) (hhi : i < 65) :
    fixedFilteredZetaRat i 45 = (fixedClearedZeta45 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 19 ≤ j.val →
      fixedFilteredZetaRat j.val 45 = (fixedClearedZeta45 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.FixedClearedZetaColumn46
namespace OAI

section

noncomputable section
namespace InternalCatalan


theorem fixedFilteredZeta46_cleared (i : ℕ) (hlo : 19 ≤ i) (hhi : i < 65) :
    fixedFilteredZetaRat i 46 = (fixedClearedZeta46 i : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  have hfinite : ∀ j : Fin 65, 19 ≤ j.val →
      fixedFilteredZetaRat j.val 46 = (fixedClearedZeta46 j.val : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
    decide +kernel
  exact hfinite ⟨i, hhi⟩ hlo

end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Split.FixedBase
/-! Glue for the split of OpenAI's Catalan development (not OpenAI code): the integrality and the
mod-101 reduction of the fixed matrix, by groups of columns. -/

namespace OAI

namespace InternalCatalan

theorem splitIntegerFractionSum
    (s : Finset ℕ) (p a : ℕ → ℤ) (f : ℕ → ℚ) (d : ℚ)
    (hf : ∀ i ∈ s, (p i : ℚ) * f i = ((p i * a i : ℤ) : ℚ) / d) :
    (∑ i ∈ s, (p i : ℚ) * f i) = ((∑ i ∈ s, p i * a i : ℤ) : ℚ) / d := by
  rw [Int.cast_sum, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [div_eq_mul_inv] using hf i hi


end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Split.Fine
/-! Glue for the split of OpenAI's Catalan development (not OpenAI code): finer groups, and the
coarser published statements recovered from them. -/

namespace OAI

namespace InternalCatalan























theorem splitFilteredMoment_cleared_f42_47 (i : ℕ) (k : Fin 48) (hk : 42 ≤ k.val ∧ k.val < 48)
    (hlo : 18 ≤ i) (hhi : i < 65) :
    fixedFilteredMomentRat i k.val = (fixedClearedMoment i k : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  obtain ⟨k, hk'⟩ := k
  obtain ⟨hka, hkb⟩ := hk
  simp only at hka hkb
  interval_cases k
  · exact fixedFilteredMoment42_cleared i hlo hhi
  · exact fixedFilteredMoment43_cleared i hlo hhi
  · exact fixedFilteredMoment44_cleared i hlo hhi
  · exact fixedFilteredMoment45_cleared i hlo hhi
  · exact fixedFilteredMoment46_cleared i hlo hhi
  · exact fixedFilteredMoment47_cleared i hlo hhi

theorem splitFilteredZeta_cleared_f42_47 (i : ℕ) (k : Fin 48) (hk : 42 ≤ k.val ∧ k.val < 48)
    (hlo : 19 ≤ i) (hhi : i < 65) :
    fixedFilteredZetaRat i k.val = (fixedClearedZeta i k : ℚ) / 427020799961118095468762173535463688638296295357889841725440000 := by
  obtain ⟨k, hk'⟩ := k
  obtain ⟨hka, hkb⟩ := hk
  simp only at hka hkb
  interval_cases k
  · exact fixedFilteredZeta42_cleared i hlo hhi
  · exact fixedFilteredZeta43_cleared i hlo hhi
  · exact fixedFilteredZeta44_cleared i hlo hhi
  · exact fixedFilteredZeta45_cleared i hlo hhi
  · exact fixedFilteredZeta46_cleared i hlo hhi
  · exact fixedFilteredZeta47_cleared i hlo hhi

theorem fixedIntegerBaseCanonical_cast_cols_42_47 (r : Fin 49) (k : Fin 48)
    (hk : 42 ≤ k.val ∧ k.val < 48) :
    (fixedIntegerBaseCanonical r k : ℚ) = (854041599922236190937524347070927377276592590715779683450880000 : ℚ) * fixedBaseEntryRat r k := by
  have hP : (∑ i ∈ Finset.range 65, ((rowP 1 r.val).coeff i : ℚ) *
      fixedFilteredMomentRat i k.val) =
      ((∑ i ∈ Finset.range 65, (rowP 1 r.val).coeff i * fixedClearedMoment i k : ℤ) : ℚ) /
        427020799961118095468762173535463688638296295357889841725440000 := by
    apply splitIntegerFractionSum
    intro i hi
    have hhi : i < 65 := Finset.mem_range.mp hi
    by_cases hlo : 18 ≤ i
    · rw [splitFilteredMoment_cleared_f42_47 i k hk hlo hhi, Int.cast_mul]
      ring
    · have hz := fixed_rowP_coeff_eq_zero_below18 r (i := i) (by omega)
      simp [hz]
  have hD : (∑ i ∈ Finset.range 65, ((rowD 1 r.val).coeff i : ℚ) *
      fixedFilteredZetaRat i k.val) =
      ((∑ i ∈ Finset.range 65, (rowD 1 r.val).coeff i * fixedClearedZeta i k : ℤ) : ℚ) /
        427020799961118095468762173535463688638296295357889841725440000 := by
    apply splitIntegerFractionSum
    intro i hi
    have hhi : i < 65 := Finset.mem_range.mp hi
    by_cases hlo : 19 ≤ i
    · rw [splitFilteredZeta_cleared_f42_47 i k hk hlo hhi, Int.cast_mul]
      ring
    · have hz := fixed_rowD_coeff_eq_zero_below19 r (i := i) (by omega)
      simp [hz]
  rw [fixedBaseEntry_dot_filtered, hP, hD]
  simp only [fixedIntegerBaseCanonical, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
  ring
















end InternalCatalan

end OAI

end

section
open OAI.InternalCatalan

theorem solution (r : Fin 49) (k : Fin 48)
    (hk : 42 ≤ k.val ∧ k.val < 48) :
    (fixedIntegerBaseCanonical r k : ℚ) = (854041599922236190937524347070927377276592590715779683450880000 : ℚ) * fixedBaseEntryRat r k := by
  first
  | exact @OAI.InternalCatalan.fixedIntegerBaseCanonical_cast_cols_42_47
  | (apply OAI.InternalCatalan.fixedIntegerBaseCanonical_cast_cols_42_47 <;> assumption)

end
