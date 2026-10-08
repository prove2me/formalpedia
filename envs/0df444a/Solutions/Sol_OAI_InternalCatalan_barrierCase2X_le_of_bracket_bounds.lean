-- Prove2me | solution 1 for OAI.InternalCatalan.barrierCase2X_le_of_bracket_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T21:30:49.507729+00:00
-- url     : https://prove2.me/submissions/c7758266-0a66-48ab-ae06-6c192c897caf

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Sqrt
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
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
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
import Definitions.Def_OAICatalanBarrierPolynomials
import Theorems.Thm_OAI_InternalCatalan_barrierCase2AX_roots_exhausted

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
-- module Solutions.OAICatalan.Catalan.Energy.BarrierChebyshevUSeries
namespace OAI

noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem barrierChebyshevU_abs_le (k : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |(Chebyshev.U ℝ (k : ℤ)).eval x| ≤ (k : ℝ) + 1 := by
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have h := Chebyshev.abs_iterate_derivative_T_real_le ((k : ℤ) + 1) 1 hx
  simp only [Function.iterate_one] at h
  rw [Chebyshev.derivative_T_eval_one, Chebyshev.T_derivative_eq_U] at h
  have hm : ((k : ℝ) + 1) * |(Chebyshev.U ℝ (k : ℤ)).eval x| ≤
      ((k : ℝ) + 1) * ((k : ℝ) + 1) := by
    simpa only [add_sub_cancel_right, eval_mul, eval_intCast, eval_add, eval_natCast, eval_one,
      Int.cast_add, Int.cast_natCast, Int.cast_one, abs_mul, abs_of_pos hk,
      pow_two] using h
  exact le_of_mul_le_mul_left hm hk

theorem barrierChebyshevU_summable {x : ℝ} (hx : |x| ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ => (((Chebyshev.U ℝ (k : ℤ)).eval x : ℝ) : ℂ) * z ^ k) := by
  have hnorm : ‖(‖z‖ : ℝ)‖ < 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)] using hz
  have hmajor : Summable (fun k : ℕ => ((k : ℝ) + 1) * ‖z‖ ^ k) := by
    simpa only [add_mul, one_mul] using
      (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable.add
        (summable_geometric_of_norm_lt_one hnorm)
  refine hmajor.of_norm_bounded ?_
  intro k
  simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_right (barrierChebyshevU_abs_le k hx)
      (pow_nonneg (norm_nonneg z) k)

private theorem barrierChebyshevU_recurrence_complex (k : ℕ) (x : ℝ) :
    (((Chebyshev.U ℝ ((k + 2 : ℕ) : ℤ)).eval x : ℝ) : ℂ) =
      2 * (x : ℂ) * (((Chebyshev.U ℝ ((k + 1 : ℕ) : ℤ)).eval x : ℝ) : ℂ) -
        (((Chebyshev.U ℝ (k : ℤ)).eval x : ℝ) : ℂ) := by
  have h := congrArg (fun p : ℝ[X] => ((p.eval x : ℝ) : ℂ))
    (Chebyshev.U_add_two ℝ (k : ℤ))
  simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, eval_sub, eval_mul, eval_ofNat, eval_X,
    Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat] using h

theorem barrierChebyshevU_hasSum {x : ℝ} (hx : |x| ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => (((Chebyshev.U ℝ (k : ℤ)).eval x : ℝ) : ℂ) * z ^ k)
      (1 / (1 - 2 * (x : ℂ) * z + z ^ 2)) := by
  let f : ℕ → ℂ := fun k => (((Chebyshev.U ℝ (k : ℤ)).eval x : ℝ) : ℂ) * z ^ k
  let S : ℂ := ∑' k, f k
  have hs : HasSum f S := (barrierChebyshevU_summable hx hz).hasSum
  have hf0 : f 0 = 1 := by simp [f]
  have hf1 : f 1 = 2 * (x : ℂ) * z := by simp [f, Chebyshev.U_one]
  have h1 : HasSum (fun k : ℕ => f (k + 1)) (S - 1) := by
    simpa only [Finset.sum_range_one, hf0] using (hasSum_nat_add_iff' 1).2 hs
  have h2 : HasSum (fun k : ℕ => f (k + 2)) (S - (1 + 2 * (x : ℂ) * z)) := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hf0, hf1] using
      (hasSum_nat_add_iff' 2).2 hs
  have hrec : ∀ k : ℕ, f (k + 2) =
      (2 * (x : ℂ) * z) * f (k + 1) - z ^ 2 * f k := by
    intro k
    dsimp only [f]
    rw [barrierChebyshevU_recurrence_complex k x]
    simp only [pow_add, pow_one]
    ring
  have hrecSum : HasSum (fun k : ℕ => f (k + 2))
      ((2 * (x : ℂ) * z) * (S - 1) - z ^ 2 * S) :=
    ((h1.mul_left (2 * (x : ℂ) * z)).sub (hs.mul_left (z ^ 2))).congr_fun hrec
  have heq := h2.unique hrecSum
  have hmul : (1 - 2 * (x : ℂ) * z + z ^ 2) * S = 1 := by
    linear_combination heq
  have hden : 1 - 2 * (x : ℂ) * z + z ^ 2 ≠ 0 := by
    intro hzero
    simp only [hzero, zero_mul, zero_ne_one] at hmul
  have hS : S = 1 / (1 - 2 * (x : ℂ) * z + z ^ 2) := by
    apply (eq_div_iff hden).2
    simpa only [mul_comm] using hmul
  rw [hS] at hs
  exact hs

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierTailPairRational
namespace OAI

noncomputable section

namespace InternalCatalan













theorem barrier_finite_lengths :
    barrierP2Finite.length = 10 ∧ barrierV2Finite.length = 10 ∧
    barrierP1Finite.length = 8 ∧ barrierV1Finite.length = 8 := by decide

theorem barrier_tail_lengths : barrierP2Tail.length = 10 ∧ barrierV2Tail.length = 13 := by
  norm_num [barrierP2Tail, barrierV2Tail, barrierConjugatePair]


theorem barrierP2_finite_abs_lt_one :
    ∀ a ∈ barrierP2Finite, |(a : ℝ) / 100000000| < 1 := by
  norm_num [barrierP2Finite]

theorem barrierV2_finite_abs_lt_one :
    ∀ a ∈ barrierV2Finite, |(a : ℝ) / 100000000| < 1 := by
  norm_num [barrierV2Finite]

theorem barrierP1_finite_abs_lt_one :
    ∀ a ∈ barrierP1Finite, |(a : ℝ) / 100000000| < 1 := by
  norm_num [barrierP1Finite]

theorem barrierV1_finite_abs_lt_one :
    ∀ a ∈ barrierV1Finite, |(a : ℝ) / 100000000| < 1 := by
  norm_num [barrierV1Finite]

theorem barrierP2_tail_norm_bounds :
    ∀ zr ∈ barrierP2Tail, ‖zr.1‖ ≤ (94 / 100 : ℝ) ∧ ‖zr.2‖ < 1 := by
  have hs : ∀ zr ∈ barrierP2Tail,
      Complex.normSq zr.1 ≤ (94 / 100 : ℝ) ^ 2 ∧ Complex.normSq zr.2 < 1 := by
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex,
      Complex.star_def, Complex.normSq_conj, Complex.normSq_mk]
  intro zr hzr
  obtain ⟨hb, hr⟩ := hs zr hzr
  rw [Complex.normSq_eq_norm_sq] at hb hr
  constructor
  · nlinarith only [hb, norm_nonneg zr.1]
  · nlinarith only [hr, norm_nonneg zr.2]

theorem barrierV2_tail_norm_bounds :
    ∀ zr ∈ barrierV2Tail, ‖zr.1‖ ≤ (984 / 1000 : ℝ) ∧ ‖zr.2‖ < 1 := by
  have hs : ∀ zr ∈ barrierV2Tail,
      Complex.normSq zr.1 ≤ (984 / 1000 : ℝ) ^ 2 ∧ Complex.normSq zr.2 < 1 := by
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex,
      Complex.star_def, Complex.normSq_conj, Complex.normSq_mk]
  intro zr hzr
  obtain ⟨hb, hr⟩ := hs zr hzr
  rw [Complex.normSq_eq_norm_sq] at hb hr
  constructor
  · nlinarith only [hb, norm_nonneg zr.1]
  · nlinarith only [hr, norm_nonneg zr.2]

theorem barrierFiniteCoeff_abs_le (cs : List ℤ) (hlen : cs.length ≤ 10)
    (hcoeff : ∀ a ∈ cs, |(a : ℝ) / 100000000| < 1) (k : ℕ) :
    |barrierFiniteCoeff cs k| ≤ 2 * (99 / 100 : ℝ) ^ k := by
  by_cases hk : k = 0
  · subst k
    norm_num [barrierFiniteCoeff]
  rw [barrierFiniteCoeff, if_neg hk]
  by_cases hi : k - 1 < cs.length
  · have hmem : cs.getD (k - 1) 0 ∈ cs := by
      rw [List.getD_eq_getElem cs 0 hi]
      exact List.getElem_mem hi
    have hk10 : k ≤ 10 := by omega
    have hpow : (99 / 100 : ℝ) ^ 10 ≤ (99 / 100 : ℝ) ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hk10
    calc
      |(cs.getD (k - 1) 0 : ℝ) / 100000000| ≤ 1 :=
        le_of_lt (hcoeff _ hmem)
      _ ≤ 2 * (99 / 100 : ℝ) ^ 10 := by norm_num
      _ ≤ 2 * (99 / 100 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_left hpow (by norm_num)
  · rw [List.getD_eq_default cs 0 (Nat.le_of_not_gt hi)]
    simp only [Int.cast_zero, zero_div, abs_zero]
    exact mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _)

def barrierTailLinearDen (z : ℂ) (x : ℝ) : ℂ := 1 - (x : ℂ) * z


theorem barrierTailLinearDen_ne_zero {x : ℝ} {z : ℂ}
    (hx : |x| ≤ 1) (hz : ‖z‖ < 1) : barrierTailLinearDen z x ≠ 0 := by
  have hnorm : ‖(x : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |x| * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg z)
      _ < 1 := by simpa only [one_mul] using hz
  intro hzero
  have hmul : (x : ℂ) * z = 1 := (sub_eq_zero.mp hzero).symm
  rw [hmul, norm_one] at hnorm
  exact (lt_irrefl (1 : ℝ)) hnorm

theorem barrierTailQuadraticDen_ne_zero {x : ℝ} {z : ℂ}
    (hx : |x| ≤ 1) (hz : ‖z‖ < 1) : barrierTailQuadraticDen z x ≠ 0 := by
  have hx2 : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hx
  have hn : Complex.normSq z < 1 :=
    lt_of_not_ge (fun h => (not_le_of_gt hz) (Complex.one_le_normSq_iff.mp h))
  have hnorm : z.re ^ 2 + z.im ^ 2 < 1 := by
    simpa only [Complex.normSq_apply, pow_two] using hn
  intro hzero
  have hre := congrArg Complex.re hzero
  have him := congrArg Complex.im hzero
  norm_num [barrierTailQuadraticDen, pow_two] at hre him
  have hprod : z.im * (z.re - x) = 0 := by nlinarith [him]
  have hax : z.re = x := by
    rcases mul_eq_zero.mp hprod with hb | ha
    · have hre0 := hre
      rw [hb] at hre0
      have hs : (z.re - x) ^ 2 = 0 := by
        nlinarith [sq_nonneg (z.re - x)]
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
    · exact sub_eq_zero.mp ha
  rw [hax] at hre hnorm
  nlinarith

theorem barrierTailLinearDen_prod_ne_zero (tail : List (ℂ × ℂ))
    (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1) {x : ℝ} (hx : |x| ≤ 1) :
    (tail.map (fun zr : ℂ × ℂ => barrierTailLinearDen zr.1 x)).prod ≠ 0 := by
  apply List.prod_ne_zero
  intro hzero
  obtain ⟨zr, hzr, hz⟩ := List.mem_map.mp hzero
  exact barrierTailLinearDen_ne_zero hx (htail zr hzr) hz

theorem barrierTailQuadraticDen_prod_ne_zero (tail : List (ℂ × ℂ))
    (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1) {x : ℝ} (hx : |x| ≤ 1) :
    (tail.map (fun zr : ℂ × ℂ => barrierTailQuadraticDen zr.1 x)).prod ≠ 0 := by
  apply List.prod_ne_zero
  intro hzero
  obtain ⟨zr, hzr, hz⟩ := List.mem_map.mp hzero
  exact barrierTailQuadraticDen_ne_zero hx (htail zr hzr) hz

def barrierCase2QXValue (x : ℝ) : ℂ :=
  (x : ℂ) * (1 - (x : ℂ)) * (1 + (x : ℂ) ^ 2) *
    (barrierP2Tail.map (fun zr : ℂ × ℂ => barrierTailQuadraticDen zr.1 x)).prod *
    (barrierV2Tail.map (fun zr : ℂ × ℂ => barrierTailLinearDen zr.1 x)).prod


private theorem barrierP2_tail_base_lt_one :
    ∀ zr ∈ barrierP2Tail, ‖zr.1‖ < 1 := by
  intro zr hzr
  exact lt_of_le_of_lt (barrierP2_tail_norm_bounds zr hzr).1 (by norm_num)

private theorem barrierV2_tail_base_lt_one :
    ∀ zr ∈ barrierV2Tail, ‖zr.1‖ < 1 := by
  intro zr hzr
  exact lt_of_le_of_lt (barrierV2_tail_norm_bounds zr hzr).1 (by norm_num)

theorem barrierCase2QXValue_ne_zero {x : ℝ} (hx : |x| ≤ 1)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) : barrierCase2QXValue x ≠ 0 := by
  have hx0' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
  have hx1' : 1 - (x : ℂ) ≠ 0 := by
    have h : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.symm
    exact_mod_cast h
  have hsq : 1 + (x : ℂ) ^ 2 ≠ 0 := by
    have h : (1 + x ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
    exact_mod_cast h
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero hx0' hx1') hsq)
      (barrierTailQuadraticDen_prod_ne_zero barrierP2Tail barrierP2_tail_base_lt_one hx))
    (barrierTailLinearDen_prod_ne_zero barrierV2Tail barrierV2_tail_base_lt_one hx)























open Polynomial

private theorem barrier_conjugate_quotient_re (n d : ℂ) :
    (n / d + star n / star d).re =
      2 * (n.re * d.re + n.im * d.im) / (d.re ^ 2 + d.im ^ 2) := by
  have hc : star n / star d = star (n / d) := by
    simp only [Complex.star_def, map_div₀]
  rw [hc]
  simp only [Complex.star_def, Complex.add_re, Complex.conj_re, Complex.div_re,
    Complex.normSq_apply, pow_two]
  ring

private theorem barrierTailLinearDen_star (z : ℂ) (x : ℝ) :
    barrierTailLinearDen (star z) x = star (barrierTailLinearDen z x) := by
  simp [barrierTailLinearDen]

private theorem barrierTailQuadraticDen_star (z : ℂ) (x : ℝ) :
    barrierTailQuadraticDen (star z) x = star (barrierTailQuadraticDen z x) := by
  simp [barrierTailQuadraticDen]

theorem barrierConjugatePair_linear_re (z r : ℂ) (x : ℝ) :
    ((barrierConjugatePair z r).map (fun zr : ℂ × ℂ =>
      zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re =
      2 * ((r * z).re * (1 - x * z.re) - (r * z).im * x * z.im) /
        ((1 - x * z.re) ^ 2 + (x * z.im) ^ 2) := by
  simp only [barrierConjugatePair, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  have hn : star r * star z = star (r * z) := by simp
  rw [barrierTailLinearDen_star, hn, barrier_conjugate_quotient_re]
  simp only [barrierTailLinearDen, Complex.sub_re, Complex.one_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.sub_im, Complex.one_im, Complex.mul_im]
  congr 1 <;> ring

theorem barrierConjugatePair_quadratic_re (z r : ℂ) (x : ℝ) :
    ((barrierConjugatePair z r).map (fun zr : ℂ × ℂ =>
      zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re =
      2 * ((r * z).re * (1 - 2 * x * z.re + z.re ^ 2 - z.im ^ 2) +
        (r * z).im * (2 * z.im * (z.re - x))) /
        ((1 - 2 * x * z.re + z.re ^ 2 - z.im ^ 2) ^ 2 +
          (2 * z.im * (z.re - x)) ^ 2) := by
  simp only [barrierConjugatePair, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  have hn : star r * star z = star (r * z) := by simp
  rw [barrierTailQuadraticDen_star, hn, barrier_conjugate_quotient_re]
  have hre : (barrierTailQuadraticDen z x).re =
      1 - 2 * x * z.re + z.re ^ 2 - z.im ^ 2 := by
    simp [barrierTailQuadraticDen, pow_two]
    ring
  have him : (barrierTailQuadraticDen z x).im = 2 * z.im * (z.re - x) := by
    simp [barrierTailQuadraticDen, pow_two]
    ring
  rw [hre, him]





theorem barrierConjugatePair_linear_eq_ratPolynomial
    (a b c d : ℚ) (x : ℝ) :
    ((barrierConjugatePair (barrierComplex a b) (barrierComplex c d)).map
      (fun zr : ℂ × ℂ => zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re =
      (barrierPairLinearA a b c d).eval₂ (Rat.castHom ℝ) x /
        (barrierPairLinearQ a b).eval₂ (Rat.castHom ℝ) x := by
  rw [barrierConjugatePair_linear_re]
  simp only [barrierPairLinearA, barrierPairLinearQ, eval₂_mul, eval₂_add,
    eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, eval₂_one, eval₂_ofNat,
    map_mul, map_sub, map_add, Rat.coe_castHom, barrierComplex, Complex.mul_re, Complex.mul_im]
  congr 1 <;> ring

theorem barrierConjugatePair_quadratic_eq_ratPolynomial
    (a b c d : ℚ) (x : ℝ) :
    ((barrierConjugatePair (barrierComplex a b) (barrierComplex c d)).map
      (fun zr : ℂ × ℂ => zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re =
      (barrierPairQuadraticA a b c d).eval₂ (Rat.castHom ℝ) x /
        (barrierPairQuadraticQ a b).eval₂ (Rat.castHom ℝ) x := by
  rw [barrierConjugatePair_quadratic_re]
  simp only [barrierPairQuadraticA, barrierPairQuadraticQ, eval₂_mul, eval₂_add,
    eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, eval₂_one, eval₂_ofNat,
    map_mul, map_sub, map_add, map_pow, Rat.coe_castHom, barrierComplex, Complex.mul_re, Complex.mul_im]
  congr 1 <;> ring





end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierFinitePotentialRat
namespace OAI

noncomputable section

namespace InternalCatalan

section

private theorem barrierTail_norm_le (tail : List (ℂ × ℂ)) (k : ℕ) :
    (∀ zr ∈ tail, ‖zr.1‖ ≤ (99 / 100 : ℝ) ∧ ‖zr.2‖ ≤ 1) →
      ‖(tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum‖ ≤
        (tail.length : ℝ) * (99 / 100 : ℝ) ^ k := by
  induction tail with
  | nil => simp
  | cons zr tail ih =>
    intro hb
    have hz := hb zr (List.mem_cons_self)
    have ht := ih (fun w hw => hb w (List.mem_cons_of_mem _ hw))
    have hone : ‖zr.2 * zr.1 ^ k‖ ≤ (99 / 100 : ℝ) ^ k := by
      rw [norm_mul, norm_pow]
      calc
        _ ≤ 1 * (99 / 100 : ℝ) ^ k := by
          gcongr
          · exact hz.2
          · exact hz.1
        _ = _ := one_mul _
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ ‖zr.2 * zr.1 ^ k‖ + ‖(tail.map (fun w : ℂ × ℂ => w.2 * w.1 ^ k)).sum‖ :=
        norm_add_le _ _
      _ ≤ (99 / 100 : ℝ) ^ k + (tail.length : ℝ) * (99 / 100 : ℝ) ^ k :=
        add_le_add hone ht
      _ = _ := by ring

private theorem barrierTrial_abs_le (cs : List ℤ) (tail : List (ℂ × ℂ))
    (hc : cs.length ≤ 10)
    (ha : ∀ a ∈ cs, |(a : ℝ) / 100000000| < 1)
    (ht : tail.length ≤ 13)
    (hb : ∀ zr ∈ tail, ‖zr.1‖ ≤ (99 / 100 : ℝ) ∧ ‖zr.2‖ ≤ 1) (k : ℕ) :
    |barrierTrial cs tail k| ≤ 15 * (99 / 100 : ℝ) ^ k := by
  by_cases hk : k = 0
  · simp [barrierTrial, hk]
  have htail : |(tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re| ≤
      13 * (99 / 100 : ℝ) ^ k := by
    exact (Complex.abs_re_le_norm _).trans ((barrierTail_norm_le tail k hb).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast ht) (by positivity)))
  simp only [barrierTrial, if_neg hk]
  calc
    _ ≤ |barrierFiniteCoeff cs k| +
        |(tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re| := by
      simpa only [Real.norm_eq_abs] using norm_add_le (barrierFiniteCoeff cs k)
        ((tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re)
    _ ≤ 2 * (99 / 100 : ℝ) ^ k + 13 * (99 / 100 : ℝ) ^ k :=
      add_le_add (barrierFiniteCoeff_abs_le cs hc ha k) htail
    _ = _ := by ring

theorem barrier_trials_abs_le (k : ℕ) :
    |barrierP2 k| ≤ 15 * (99 / 100 : ℝ) ^ k ∧
    |barrierV2 k| ≤ 15 * (99 / 100 : ℝ) ^ k ∧
    |barrierP1 k| ≤ 15 * (99 / 100 : ℝ) ^ k ∧
    |barrierV1 k| ≤ 15 * (99 / 100 : ℝ) ^ k := by
  have hp : ∀ zr ∈ barrierP2Tail, ‖zr.1‖ ≤ (99 / 100 : ℝ) ∧ ‖zr.2‖ ≤ 1 := by
    intro zr hz
    have h := barrierP2_tail_norm_bounds zr hz
    exact ⟨h.1.trans (by norm_num), h.2.le⟩
  have hv : ∀ zr ∈ barrierV2Tail, ‖zr.1‖ ≤ (99 / 100 : ℝ) ∧ ‖zr.2‖ ≤ 1 := by
    intro zr hz
    have h := barrierV2_tail_norm_bounds zr hz
    exact ⟨h.1.trans (by norm_num), h.2.le⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact barrierTrial_abs_le barrierP2Finite barrierP2Tail
      barrier_finite_lengths.1.le barrierP2_finite_abs_lt_one
      (barrier_tail_lengths.1.le.trans (by norm_num)) hp k
  · exact barrierTrial_abs_le barrierV2Finite barrierV2Tail
      barrier_finite_lengths.2.1.le barrierV2_finite_abs_lt_one
      barrier_tail_lengths.2.le hv k
  · exact barrierTrial_abs_le barrierP1Finite []
      (barrier_finite_lengths.2.2.1.le.trans (by norm_num)) barrierP1_finite_abs_lt_one
      (by simp) (by simp) k
  · exact barrierTrial_abs_le barrierV1Finite []
      (barrier_finite_lengths.2.2.2.le.trans (by norm_num)) barrierV1_finite_abs_lt_one
      (by simp) (by simp) k

theorem barrier_trials_abs_summable :
    Summable (fun k => |barrierP2 k|) ∧ Summable (fun k => |barrierV2 k|) ∧
    Summable (fun k => |barrierP1 k|) ∧ Summable (fun k => |barrierV1 k|) := by
  have hg : Summable (fun k : ℕ => (15 : ℝ) * (99 / 100 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(99 / 100 : ℝ)‖ < 1)).mul_left 15
  refine ⟨hg.of_norm_bounded (by intro k; simpa using (barrier_trials_abs_le k).1),
    hg.of_norm_bounded (by intro k; simpa using (barrier_trials_abs_le k).2.1),
    hg.of_norm_bounded (by intro k; simpa using (barrier_trials_abs_le k).2.2.1),
    hg.of_norm_bounded (by intro k; simpa using (barrier_trials_abs_le k).2.2.2)⟩





open Polynomial Filter
open scoped BigOperators



private theorem barrierTrialT_term_norm_le (u : ℕ → ℝ) (k : ℕ) {x : ℝ}
    (hx : |x| ≤ 1) :
    ‖u (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x /
      ((k + 1 : ℕ) : ℝ)‖ ≤ |u (k + 1)| := by
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 k
  have hkp : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num) hk
  have ht := Chebyshev.abs_eval_T_real_le_one ((k + 1 : ℕ) : ℤ) hx
  rw [norm_div, norm_mul]
  simp only [Real.norm_eq_abs, abs_of_pos hkp]
  calc
    _ ≤ |u (k + 1)| * 1 / ((k + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht (abs_nonneg _)) hkp.le
    _ = |u (k + 1)| / ((k + 1 : ℕ) : ℝ) := by rw [mul_one]
    _ ≤ |u (k + 1)| := div_le_self (abs_nonneg _) hk

private theorem barrierTrialS_term_norm_le (u : ℕ → ℝ) (k : ℕ) {x : ℝ}
    (hx : |x| ≤ 1) :
    ‖u (k + 1) * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)‖ ≤ |u (k + 1)| := by
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 k
  have hkp : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num) hk
  have ht : |x| ^ (k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
  rw [norm_div, norm_mul]
  simp only [Real.norm_eq_abs, abs_pow, abs_of_pos hkp]
  calc
    _ ≤ |u (k + 1)| * 1 / ((k + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht (abs_nonneg _)) hkp.le
    _ = |u (k + 1)| / ((k + 1 : ℕ) : ℝ) := by rw [mul_one]
    _ ≤ |u (k + 1)| := div_le_self (abs_nonneg _) hk

theorem barrierTrialT_summable (u : ℕ → ℝ) (hu : Summable (fun k => |u k|))
    {x : ℝ} (hx : |x| ≤ 1) :
    Summable (fun k : ℕ => u (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x /
      ((k + 1 : ℕ) : ℝ)) := by
  exact ((summable_nat_add_iff 1).mpr hu).of_norm_bounded
    (fun k => barrierTrialT_term_norm_le u k hx)

theorem barrierTrialS_summable (u : ℕ → ℝ) (hu : Summable (fun k => |u k|))
    {x : ℝ} (hx : |x| ≤ 1) :
    Summable (fun k : ℕ => u (k + 1) * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
  exact ((summable_nat_add_iff 1).mpr hu).of_norm_bounded
    (fun k => barrierTrialS_term_norm_le u k hx)

theorem barrierTrialT_tendstoUniformlyOn (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) :
    TendstoUniformlyOn
      (fun m x => ∑ k ∈ Finset.range m,
        u (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ))
      (barrierTrialT u) atTop (Set.Icc (-1) 1) := by
  unfold barrierTrialT
  apply tendstoUniformlyOn_tsum_nat ((summable_nat_add_iff 1).mpr hu)
  intro k x hx
  exact barrierTrialT_term_norm_le u k (abs_le.mpr hx)

theorem barrierTrialS_tendstoUniformlyOn (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) :
    TendstoUniformlyOn
      (fun m x => ∑ k ∈ Finset.range m,
        u (k + 1) * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ))
      (barrierTrialS u) atTop (Set.Icc (-1) 1) := by
  unfold barrierTrialS
  apply tendstoUniformlyOn_tsum_nat ((summable_nat_add_iff 1).mpr hu)
  intro k x hx
  exact barrierTrialS_term_norm_le u k (abs_le.mpr hx)


end

section

open scoped BigOperators





end
section

open Polynomial
open scoped BigOperators



end

section

open Polynomial Set Filter
open scoped BigOperators

theorem barrierTrialT_continuousOn (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) :
    ContinuousOn (barrierTrialT u) (Icc (-1 : ℝ) 1) := by
  refine (barrierTrialT_tendstoUniformlyOn u hu).continuousOn (Frequently.of_forall ?_)
  intro m
  refine continuousOn_finsetSum _ (fun k _ => ?_)
  have hterm : Continuous (fun x : ℝ =>
      u (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x *
        (((k + 1 : ℕ) : ℝ)⁻¹)) :=
    (continuous_const.mul (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).continuous).mul
      continuous_const
  simpa only [div_eq_mul_inv] using hterm.continuousOn

theorem barrierTrialS_continuousOn (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) :
    ContinuousOn (barrierTrialS u) (Icc (-1 : ℝ) 1) := by
  refine (barrierTrialS_tendstoUniformlyOn u hu).continuousOn (Frequently.of_forall ?_)
  intro m
  refine continuousOn_finsetSum _ (fun k _ => ?_)
  have hterm : Continuous (fun x : ℝ =>
      u (k + 1) * x ^ (k + 1) * (((k + 1 : ℕ) : ℝ)⁻¹)) :=
    (continuous_const.mul (continuous_id.pow (k + 1))).mul continuous_const
  simpa only [div_eq_mul_inv] using hterm.continuousOn

end

open Polynomial

private theorem barrier_Tseries_term_hasDerivAt (a : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => a * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval y /
        ((k + 1 : ℕ) : ℝ))
      (a * (Chebyshev.U ℝ (k : ℤ)).eval x) x := by
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hindex : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by simp
  have ht : HasDerivAt
      (fun y : ℝ => (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval y)
      (((k + 1 : ℕ) : ℝ) * (Chebyshev.U ℝ (k : ℤ)).eval x) x := by
    simpa only [Chebyshev.T_derivative_eq_U, eval_mul, eval_intCast,
      hindex, Int.cast_natCast, eval_natCast] using
      (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).hasDerivAt x
  apply ((ht.const_mul a).div_const ((k + 1 : ℕ) : ℝ)).congr_deriv
  field_simp [hk]

private theorem barrier_Sseries_term_hasDerivAt (a : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => a * y ^ (k + 1) / ((k + 1 : ℕ) : ℝ))
      (a * x ^ k) x := by
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hp : HasDerivAt (fun y : ℝ => y ^ (k + 1))
      (((k + 1 : ℕ) : ℝ) * x ^ k) x := by
    simpa only [Nat.add_sub_cancel] using hasDerivAt_pow (k + 1) x
  apply ((hp.const_mul a).div_const ((k + 1 : ℕ) : ℝ)).congr_deriv
  field_simp [hk]

theorem barrierTrialT_hasDerivAt_series (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|))
    (huw : Summable (fun k : ℕ => (k : ℝ) * |u k|))
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (barrierTrialT u)
      (∑' k : ℕ, u (k + 1) * (Chebyshev.U ℝ (k : ℤ)).eval x) x := by
  unfold barrierTrialT
  apply hasDerivAt_tsum_of_isPreconnected ((summable_nat_add_iff 1).mpr huw)
    isOpen_Ioo isPreconnected_Ioo
    (fun k y _ => barrier_Tseries_term_hasDerivAt (u (k + 1)) k y)
    _ (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1)
    (barrierTrialT_summable u hu (x := 0) (by norm_num)) hx
  intro k y hy
  have hyabs : |y| ≤ 1 := abs_le.mpr ⟨hy.1.le, hy.2.le⟩
  rw [norm_mul]
  simp only [Real.norm_eq_abs]
  calc
    |u (k + 1)| * |(Chebyshev.U ℝ (k : ℤ)).eval y| ≤
        |u (k + 1)| * ((k : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (barrierChebyshevU_abs_le k hyabs) (abs_nonneg _)
    _ = ((k + 1 : ℕ) : ℝ) * |u (k + 1)| := by push_cast; ring

theorem barrierTrialS_hasDerivAt_series (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|))
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (barrierTrialS u) (∑' k : ℕ, u (k + 1) * x ^ k) x := by
  unfold barrierTrialS
  apply hasDerivAt_tsum_of_isPreconnected ((summable_nat_add_iff 1).mpr hu)
    isOpen_Ioo isPreconnected_Ioo
    (fun k y _ => barrier_Sseries_term_hasDerivAt (u (k + 1)) k y)
    _ (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1)
    (barrierTrialS_summable u hu (x := 0) (by norm_num)) hx
  intro k y hy
  have hyabs : |y| ≤ 1 := abs_le.mpr ⟨hy.1.le, hy.2.le⟩
  rw [norm_mul]
  simp only [Real.norm_eq_abs, abs_pow]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg y) hyabs : |y| ^ k ≤ 1)
      (abs_nonneg (u (k + 1)))

private theorem barrier_weighted_abs_summable_of_decay (u : ℕ → ℝ)
    (hu : ∀ k, |u k| ≤ 15 * (99 / 100 : ℝ) ^ k) :
    Summable (fun k : ℕ => (k : ℝ) * |u k|) := by
  have hg : Summable (fun k : ℕ => (15 : ℝ) * ((k : ℝ) * (99 / 100 : ℝ) ^ k)) := by
    simpa only [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one 1
        (by norm_num : ‖(99 / 100 : ℝ)‖ < 1)).mul_left (15 : ℝ)
  apply hg.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) * |u k|)]
  calc
    (k : ℝ) * |u k| ≤ (k : ℝ) * (15 * (99 / 100 : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_left (hu k) (Nat.cast_nonneg k)
    _ = 15 * ((k : ℝ) * (99 / 100 : ℝ) ^ k) := by ring

theorem barrier_trials_weighted_abs_summable :
    Summable (fun k : ℕ => (k : ℝ) * |barrierP2 k|) ∧
    Summable (fun k : ℕ => (k : ℝ) * |barrierV2 k|) ∧
    Summable (fun k : ℕ => (k : ℝ) * |barrierP1 k|) ∧
    Summable (fun k : ℕ => (k : ℝ) * |barrierV1 k|) := by
  exact ⟨barrier_weighted_abs_summable_of_decay _ (fun k => (barrier_trials_abs_le k).1),
    barrier_weighted_abs_summable_of_decay _ (fun k => (barrier_trials_abs_le k).2.1),
    barrier_weighted_abs_summable_of_decay _ (fun k => (barrier_trials_abs_le k).2.2.1),
    barrier_weighted_abs_summable_of_decay _ (fun k => (barrier_trials_abs_le k).2.2.2)⟩

open Polynomial
open scoped BigOperators





end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierGlobalMaxReduction
namespace OAI

noncomputable section

namespace InternalCatalan.GlobalMaxReduction

open Set Filter
open scoped Topology

theorem le_on_Icc_of_critical_le {f : ℝ → ℝ} {a b M : ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (ha : f a ≤ M) (hb : f b ≤ M)
    (hcritical : ∀ c ∈ Ioo a b, deriv f c = 0 → f c ≤ M) :
    ∀ x ∈ Icc a b, f x ≤ M := by
  intro x hx
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨x, hx⟩ hcont
  have hcM : f c ≤ M := by
    by_cases hca : c = a
    · simpa only [hca] using ha
    by_cases hcb : c = b
    · simpa only [hcb] using hb
    have hcint : c ∈ Ioo a b :=
      ⟨lt_of_le_of_ne hc.1 (Ne.symm hca), lt_of_le_of_ne hc.2 hcb⟩
    have hlocal : IsLocalMax f c :=
      hmax.isLocalMax (Icc_mem_nhds hcint.1 hcint.2)
    exact hcritical c hcint hlocal.deriv_eq_zero
  exact (hmax hx).trans hcM

theorem exists_left_cutoff {f : ℝ → ℝ} {a x M : ℝ}
    (hlim : Tendsto f (𝓝[>] a) atBot) (hax : a < x) :
    ∃ l ∈ Ioo a x, f l ≤ M := by
  have hinterval : ∀ᶠ l in 𝓝[>] a, l ∈ Ioo a x := Ioo_mem_nhdsGT hax
  exact (hinterval.and (hlim.eventually (eventually_le_atBot M))).exists

theorem exists_right_cutoff {f : ℝ → ℝ} {x b M : ℝ}
    (hlim : Tendsto f (𝓝[<] b) atBot) (hxb : x < b) :
    ∃ r ∈ Ioo x b, f r ≤ M := by
  have hinterval : ∀ᶠ r in 𝓝[<] b, r ∈ Ioo x b := Ioo_mem_nhdsLT hxb
  exact (hinterval.and (hlim.eventually (eventually_le_atBot M))).exists

theorem le_on_Ioo_of_limits_of_critical_le {f : ℝ → ℝ} {a b M : ℝ}
    (hcont : ContinuousOn f (Ioo a b))
    (hleft : Tendsto f (𝓝[>] a) atBot)
    (hright : Tendsto f (𝓝[<] b) atBot)
    (hcritical : ∀ c ∈ Ioo a b, deriv f c = 0 → f c ≤ M) :
    ∀ x ∈ Ioo a b, f x ≤ M := by
  intro x hx
  obtain ⟨l, hl, hlM⟩ := exists_left_cutoff (M := M) hleft hx.1
  obtain ⟨r, hr, hrM⟩ := exists_right_cutoff (M := M) hright hx.2
  have hsub : Icc l r ⊆ Ioo a b := by
    intro z hz
    exact ⟨lt_of_lt_of_le hl.1 hz.1, lt_of_le_of_lt hz.2 hr.2⟩
  exact le_on_Icc_of_critical_le (hcont.mono hsub) hlM hrM
    (fun c hc hd => hcritical c (hsub ⟨hc.1.le, hc.2.le⟩) hd)
    x ⟨hl.2.le, hr.1.le⟩

theorem le_on_Ico_of_limit_of_critical_le {f : ℝ → ℝ} {a b M : ℝ}
    (hcont : ContinuousOn f (Ico a b))
    (ha : f a ≤ M)
    (hright : Tendsto f (𝓝[<] b) atBot)
    (hcritical : ∀ c ∈ Ioo a b, deriv f c = 0 → f c ≤ M) :
    ∀ x ∈ Ico a b, f x ≤ M := by
  intro x hx
  obtain ⟨r, hr, hrM⟩ := exists_right_cutoff (M := M) hright hx.2
  have hsub : Icc a r ⊆ Ico a b := by
    intro z hz
    exact ⟨hz.1, lt_of_le_of_lt hz.2 hr.2⟩
  exact le_on_Icc_of_critical_le (hcont.mono hsub) ha hrM
    (fun c hc hd => hcritical c ⟨hc.1, hc.2.trans hr.2⟩ hd)
    x ⟨hx.1, hr.1.le⟩


theorem le_on_two_components_of_stationary_cover
    {f : ℝ → ℝ} {a c b M : ℝ} {S : Set ℝ}
    (hcontLeft : ContinuousOn f (Ico a c))
    (hcontRight : ContinuousOn f (Ioo c b))
    (ha : f a ≤ M)
    (hcLeft : Tendsto f (𝓝[<] c) atBot)
    (hcRight : Tendsto f (𝓝[>] c) atBot)
    (hbLeft : Tendsto f (𝓝[<] b) atBot)
    (hcover : ∀ x ∈ Ioo a c ∪ Ioo c b, deriv f x = 0 → x ∈ S)
    (hvalues : ∀ x ∈ S, f x ≤ M) :
    ∀ x ∈ Ico a c ∪ Ioo c b, f x ≤ M := by
  intro x hx
  rcases hx with hx | hx
  · exact le_on_Ico_of_limit_of_critical_le hcontLeft ha hcLeft
      (fun z hz hd => hvalues z (hcover z (Or.inl hz) hd)) x hx
  · exact le_on_Ioo_of_limits_of_critical_le hcontRight hcRight hbLeft
      (fun z hz hd => hvalues z (hcover z (Or.inr hz) hd)) x hx

end InternalCatalan.GlobalMaxReduction

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierRationalSumNumerator
namespace OAI

noncomputable section

namespace InternalCatalan

open Polynomial



def barrierFractionSum (fs : List (ℚ[X] × ℚ[X])) (x : ℝ) : ℝ :=
  (fs.map (fun aq : ℚ[X] × ℚ[X] =>
    aq.1.eval₂ (Rat.castHom ℝ) x / aq.2.eval₂ (Rat.castHom ℝ) x)).sum

theorem barrierFractionNumerator_eval (fs : List (ℚ[X] × ℚ[X])) (x : ℝ)
    (hprod : (barrierFractionProduct fs).eval₂ (Rat.castHom ℝ) x ≠ 0) :
    (barrierFractionNumerator fs).eval₂ (Rat.castHom ℝ) x =
      (barrierFractionProduct fs).eval₂ (Rat.castHom ℝ) x * barrierFractionSum fs x := by
  revert hprod
  induction fs with
  | nil =>
      intro _
      simp [barrierFractionNumerator, barrierFractionProduct, barrierFractionSum]
  | cons aq fs ih =>
      intro hprod
      have hh : aq.2.eval₂ (Rat.castHom ℝ) x *
          (barrierFractionProduct fs).eval₂ (Rat.castHom ℝ) x ≠ 0 := by
        simpa only [barrierFractionProduct, List.map_cons, List.prod_cons, eval₂_mul]
          using hprod
      have hq : aq.2.eval₂ (Rat.castHom ℝ) x ≠ 0 := (mul_ne_zero_iff.mp hh).1
      have ht : (barrierFractionProduct fs).eval₂ (Rat.castHom ℝ) x ≠ 0 :=
        (mul_ne_zero_iff.mp hh).2
      have hrec := ih ht
      change
        (aq.1 * barrierFractionProduct fs + aq.2 * barrierFractionNumerator fs).eval₂
          (Rat.castHom ℝ) x =
        (aq.2 * barrierFractionProduct fs).eval₂ (Rat.castHom ℝ) x *
          (aq.1.eval₂ (Rat.castHom ℝ) x / aq.2.eval₂ (Rat.castHom ℝ) x +
            barrierFractionSum fs x)
      rw [eval₂_add, eval₂_mul, eval₂_mul, eval₂_mul, hrec]
      field_simp [hq]

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierTrialPowerHasSum
namespace OAI

noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

private theorem barrierFiniteCoeff_power_hasSum (cs : List ℤ) (x : ℝ) :
    HasSum (fun k : ℕ => barrierFiniteCoeff cs (k + 1) * x ^ k)
      ((barrierFinitePowerDerivative cs).eval₂ (Rat.castHom ℝ) x) := by
  have hs : HasSum
      (fun k : ℕ => ((cs.getD k 0 : ℝ) / 100000000) * x ^ k)
      (∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) * x ^ k) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    have hlen : cs.length ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    rw [List.getD_eq_default cs 0 hlen]
    norm_num
  have hvalue : (barrierFinitePowerDerivative cs).eval₂ (Rat.castHom ℝ) x =
      ∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) * x ^ k := by
    simp only [barrierFinitePowerDerivative, eval₂_finsetSum, eval₂_mul,
      eval₂_C, eval₂_X_pow, map_div₀, map_intCast, map_ofNat]
  rw [hvalue]
  simpa [barrierFiniteCoeff] using hs

private theorem barrierTailRow_power_hasSum (z r : ℂ) (hz : ‖z‖ < 1)
    {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ => (r * z ^ (k + 1)).re * x ^ k)
      (r * z / barrierTailLinearDen z x).re := by
  have hratio : ‖(x : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |x| * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg z)
      _ < 1 := by simpa only [one_mul] using hz
  have hc : HasSum
      (fun k : ℕ => (r * z ^ (k + 1)) * ((x ^ k : ℝ) : ℂ))
      (r * z / barrierTailLinearDen z x) := by
    convert (hasSum_geometric_of_norm_lt_one hratio).mul_left (r * z) using 1
    · rfl
    · funext k
      simp only [Complex.ofReal_pow, mul_pow, pow_succ]
      ring
    · simp only [barrierTailLinearDen, div_eq_mul_inv]
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
    Complex.hasSum_re hc

private theorem barrierTail_power_hasSum (tail : List (ℂ × ℂ))
    (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1) {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ =>
      (tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ (k + 1))).sum.re * x ^ k)
      (tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re := by
  revert htail
  induction tail with
  | nil =>
      intro _
      simp
  | cons zr tail ih =>
      intro htail
      have hr := barrierTailRow_power_hasSum zr.1 zr.2 (htail zr List.mem_cons_self) hx
      have ht := ih (fun w hw => htail w (List.mem_cons_of_mem _ hw))
      simpa only [List.map_cons, List.sum_cons, Complex.add_re, add_mul] using hr.add ht

theorem barrierTrial_power_hasSum (cs : List ℤ) (tail : List (ℂ × ℂ))
    (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1) {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ => barrierTrial cs tail (k + 1) * x ^ k)
      ((barrierFinitePowerDerivative cs).eval₂ (Rat.castHom ℝ) x +
        (tail.map (fun zr : ℂ × ℂ =>
          zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re) := by
  simpa [barrierTrial, add_mul] using
    (barrierFiniteCoeff_power_hasSum cs x).add (barrierTail_power_hasSum tail htail hx)

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierTrialUHasSum
namespace OAI

noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

private theorem barrierFiniteCoeff_U_hasSum (cs : List ℤ) (x : ℝ) :
    HasSum (fun k : ℕ => barrierFiniteCoeff cs (k + 1) *
      (Chebyshev.U ℝ (k : ℤ)).eval x)
      ((barrierFiniteUDerivative cs).eval₂ (Rat.castHom ℝ) x) := by
  have hs : HasSum
      (fun k : ℕ => ((cs.getD k 0 : ℝ) / 100000000) *
        (Chebyshev.U ℝ (k : ℤ)).eval x)
      (∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) *
        (Chebyshev.U ℝ (k : ℤ)).eval x) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    have hlen : cs.length ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    rw [List.getD_eq_default cs 0 hlen]
    norm_num
  have hvalue : (barrierFiniteUDerivative cs).eval₂ (Rat.castHom ℝ) x =
      ∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) *
        (Chebyshev.U ℝ (k : ℤ)).eval x := by
    simp only [barrierFiniteUDerivative, eval₂_finsetSum, eval₂_mul,
      eval₂_C, map_div₀, map_intCast, map_ofNat]
    simp only [eval₂_eq_eval_map, Chebyshev.map_U]
  rw [hvalue]
  simpa [barrierFiniteCoeff] using hs

private theorem barrierTailRow_U_hasSum (z r : ℂ) (hz : ‖z‖ < 1)
    {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ => (r * z ^ (k + 1)).re * (Chebyshev.U ℝ (k : ℤ)).eval x)
      (r * z / barrierTailQuadraticDen z x).re := by
  have hc : HasSum
      (fun k : ℕ => (r * z ^ (k + 1)) *
        (((Chebyshev.U ℝ (k : ℤ)).eval x : ℝ) : ℂ))
      (r * z / barrierTailQuadraticDen z x) := by
    convert (barrierChebyshevU_hasSum hx hz).mul_left (r * z) using 1
    · rfl
    · funext k
      rw [pow_succ]
      ring
    · simp only [barrierTailQuadraticDen, div_eq_mul_inv, one_mul]
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
    Complex.hasSum_re hc

private theorem barrierTail_U_hasSum (tail : List (ℂ × ℂ))
    (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1) {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ =>
      (tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ (k + 1))).sum.re *
        (Chebyshev.U ℝ (k : ℤ)).eval x)
      (tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re := by
  revert htail
  induction tail with
  | nil =>
      intro _
      simp
  | cons zr tail ih =>
      intro htail
      have hr := barrierTailRow_U_hasSum zr.1 zr.2 (htail zr List.mem_cons_self) hx
      have ht := ih (fun w hw => htail w (List.mem_cons_of_mem _ hw))
      simpa only [List.map_cons, List.sum_cons, Complex.add_re, add_mul] using hr.add ht

theorem barrierTrial_U_hasSum (cs : List ℤ) (tail : List (ℂ × ℂ))
    (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1) {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ => barrierTrial cs tail (k + 1) *
      (Chebyshev.U ℝ (k : ℤ)).eval x)
      ((barrierFiniteUDerivative cs).eval₂ (Rat.castHom ℝ) x +
        (tail.map (fun zr : ℂ × ℂ =>
          zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re) := by
  simpa [barrierTrial, add_mul] using
    (barrierFiniteCoeff_U_hasSum cs x).add (barrierTail_U_hasSum tail htail hx)

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoXExplicitGroup7
namespace OAI

noncomputable section

namespace InternalCatalan






def barrierExpandRealRows (rs : List (ℚ × ℚ)) : List (ℂ × ℂ) :=
  rs.map (fun ac : ℚ × ℚ => (barrierComplex ac.1 0, barrierComplex ac.2 0))

def barrierExpandPairRow (row : BarrierRationalPairRow) : List (ℂ × ℂ) :=
  barrierConjugatePair (barrierComplex row.a row.b) (barrierComplex row.c row.d)

def barrierExpandPairRows (rs : List BarrierRationalPairRow) : List (ℂ × ℂ) :=
  rs.flatMap barrierExpandPairRow

theorem barrierP2Tail_eq_grouped :
    barrierP2Tail = barrierExpandRealRows barrierP2RealRows ++
      barrierExpandPairRows barrierP2PairRows := by rfl

theorem barrierV2Tail_eq_grouped :
    barrierV2Tail = barrierExpandRealRows barrierV2RealRows ++
      barrierExpandPairRows barrierV2PairRows := by rfl

open Polynomial



def barrierGroupedLinearQ (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) : ℚ[X] :=
  (rs.map (fun ac : ℚ × ℚ => barrierRealLinearQ ac.1)).prod *
    (ps.map (fun row : BarrierRationalPairRow => barrierPairLinearQ row.a row.b)).prod

def barrierGroupedQuadraticQ (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) : ℚ[X] :=
  (rs.map (fun ac : ℚ × ℚ => barrierRealQuadraticQ ac.1)).prod *
    (ps.map (fun row : BarrierRationalPairRow => barrierPairQuadraticQ row.a row.b)).prod

private theorem barrierRealLinearQ_eval_complex (a : ℚ) (x : ℝ) :
    (barrierRealLinearQ a).eval₂ (Rat.castHom ℂ) (x : ℂ) =
      barrierTailLinearDen (barrierComplex a 0) x := by
  apply Complex.ext <;> simp [barrierRealLinearQ, barrierTailLinearDen, barrierComplex]
  ring

private theorem barrierRealQuadraticQ_eval_complex (a : ℚ) (x : ℝ) :
    (barrierRealQuadraticQ a).eval₂ (Rat.castHom ℂ) (x : ℂ) =
      barrierTailQuadraticDen (barrierComplex a 0) x := by
  apply Complex.ext <;>
    simp [barrierRealQuadraticQ, barrierTailQuadraticDen, barrierComplex, pow_two]
  ring

private theorem barrierPairLinearQ_eval_complex (row : BarrierRationalPairRow) (x : ℝ) :
    (barrierPairLinearQ row.a row.b).eval₂ (Rat.castHom ℂ) (x : ℂ) =
      ((barrierExpandPairRow row).map
        (fun zr : ℂ × ℂ => barrierTailLinearDen zr.1 x)).prod := by
  apply Complex.ext <;>
    simp [barrierPairLinearQ, barrierExpandPairRow, barrierConjugatePair,
      barrierTailLinearDen, barrierComplex, pow_two]
  <;> ring

private theorem barrierPairQuadraticQ_eval_complex (row : BarrierRationalPairRow) (x : ℝ) :
    (barrierPairQuadraticQ row.a row.b).eval₂ (Rat.castHom ℂ) (x : ℂ) =
      ((barrierExpandPairRow row).map
        (fun zr : ℂ × ℂ => barrierTailQuadraticDen zr.1 x)).prod := by
  apply Complex.ext <;>
    simp [barrierPairQuadraticQ, barrierExpandPairRow, barrierConjugatePair,
      barrierTailQuadraticDen, barrierComplex, pow_two]
  <;> ring

private theorem barrier_prod_map_flatMap {α β : Type*} (rs : List α)
    (g : α → List β) (f : β → ℂ) :
    ((rs.flatMap g).map f).prod = (rs.map (fun r => ((g r).map f).prod)).prod := by
  induction rs with
  | nil => simp
  | cons r rs ih => simp [List.flatMap_cons, List.map_append, List.prod_append, ih]

private theorem barrierGroupedLinearQ_eval_complex (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) (x : ℝ) :
    (barrierGroupedLinearQ rs ps).eval₂ (Rat.castHom ℂ) (x : ℂ) =
      ((barrierExpandRealRows rs ++ barrierExpandPairRows ps).map
        (fun zr : ℂ × ℂ => barrierTailLinearDen zr.1 x)).prod := by
  simp only [barrierGroupedLinearQ, eval₂_mul, eval₂_list_prod,
    barrierExpandRealRows, barrierExpandPairRows, List.map_append, List.prod_append,
    barrier_prod_map_flatMap, List.map_map, Function.comp_def,
    barrierRealLinearQ_eval_complex, barrierPairLinearQ_eval_complex]

private theorem barrierGroupedQuadraticQ_eval_complex (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) (x : ℝ) :
    (barrierGroupedQuadraticQ rs ps).eval₂ (Rat.castHom ℂ) (x : ℂ) =
      ((barrierExpandRealRows rs ++ barrierExpandPairRows ps).map
        (fun zr : ℂ × ℂ => barrierTailQuadraticDen zr.1 x)).prod := by
  simp only [barrierGroupedQuadraticQ, eval₂_mul, eval₂_list_prod,
    barrierExpandRealRows, barrierExpandPairRows, List.map_append, List.prod_append,
    barrier_prod_map_flatMap, List.map_map, Function.comp_def,
    barrierRealQuadraticQ_eval_complex, barrierPairQuadraticQ_eval_complex]

def barrierP2QuadraticQ : ℚ[X] :=
  barrierGroupedQuadraticQ barrierP2RealRows barrierP2PairRows

def barrierV2LinearQ : ℚ[X] :=
  barrierGroupedLinearQ barrierV2RealRows barrierV2PairRows


theorem barrierP2QuadraticQ_eval_complex (x : ℝ) :
    barrierP2QuadraticQ.eval₂ (Rat.castHom ℂ) (x : ℂ) =
      (barrierP2Tail.map (fun zr : ℂ × ℂ => barrierTailQuadraticDen zr.1 x)).prod := by
  rw [barrierP2Tail_eq_grouped]
  exact barrierGroupedQuadraticQ_eval_complex _ _ x

theorem barrierV2LinearQ_eval_complex (x : ℝ) :
    barrierV2LinearQ.eval₂ (Rat.castHom ℂ) (x : ℂ) =
      (barrierV2Tail.map (fun zr : ℂ × ℂ => barrierTailLinearDen zr.1 x)).prod := by
  rw [barrierV2Tail_eq_grouped]
  exact barrierGroupedLinearQ_eval_complex _ _ x


def barrierCase2QX : ℚ[X] :=
  X * (1 - X) * (1 + X ^ 2) * barrierP2QuadraticQ * barrierV2LinearQ


theorem barrierCase2QX_eval_complex (x : ℝ) :
    barrierCase2QX.eval₂ (Rat.castHom ℂ) (x : ℂ) = barrierCase2QXValue x := by
  simp only [barrierCase2QX, eval₂_mul, eval₂_sub, eval₂_add, eval₂_pow,
    eval₂_X, eval₂_one, barrierP2QuadraticQ_eval_complex,
    barrierV2LinearQ_eval_complex, barrierCase2QXValue]


private theorem barrier_ratPolynomial_eval_complex (p : ℚ[X]) (x : ℝ) :
    ((p.eval₂ (Rat.castHom ℝ) x : ℝ) : ℂ) = p.eval₂ (Rat.castHom ℂ) (x : ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp

theorem barrierCase2QX_eval_ne_zero {x : ℝ} (hx : |x| ≤ 1)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    barrierCase2QX.eval₂ (Rat.castHom ℝ) x ≠ 0 := by
  intro hzero
  apply barrierCase2QXValue_ne_zero hx hx0 hx1
  rw [← barrierCase2QX_eval_complex, ← barrier_ratPolynomial_eval_complex]
  simp only [hzero, Complex.ofReal_zero]


open Polynomial

def barrierGroupedLinearTailValue (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) (x : ℝ) : ℝ :=
  (rs.map (fun ac : ℚ × ℚ =>
    (ac.2 : ℝ) * (ac.1 : ℝ) / (1 - (ac.1 : ℝ) * x))).sum +
  (ps.map (fun row : BarrierRationalPairRow =>
    (barrierPairLinearA row.a row.b row.c row.d).eval₂ (Rat.castHom ℝ) x /
      (barrierPairLinearQ row.a row.b).eval₂ (Rat.castHom ℝ) x)).sum

def barrierGroupedQuadraticTailValue (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) (x : ℝ) : ℝ :=
  (rs.map (fun ac : ℚ × ℚ =>
    (ac.2 : ℝ) * (ac.1 : ℝ) /
      (1 - 2 * (ac.1 : ℝ) * x + (ac.1 : ℝ) ^ 2))).sum +
  (ps.map (fun row : BarrierRationalPairRow =>
    (barrierPairQuadraticA row.a row.b row.c row.d).eval₂ (Rat.castHom ℝ) x /
      (barrierPairQuadraticQ row.a row.b).eval₂ (Rat.castHom ℝ) x)).sum

private theorem barrierComplex_real (a : ℚ) :
    barrierComplex a 0 = ((a : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [barrierComplex]

private theorem barrier_realTailLinear_re (a c : ℚ) (x : ℝ) :
    (barrierComplex c 0 * barrierComplex a 0 /
      barrierTailLinearDen (barrierComplex a 0) x).re =
      (c : ℝ) * (a : ℝ) / (1 - (a : ℝ) * x) := by
  have hd : barrierTailLinearDen (barrierComplex a 0) x =
      ((1 - (a : ℝ) * x : ℝ) : ℂ) := by
    simp only [barrierTailLinearDen, barrierComplex_real, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_mul]
    ring
  rw [hd]
  simp only [barrierComplex_real, ← Complex.ofReal_mul, ← Complex.ofReal_div,
    Complex.ofReal_re]

private theorem barrier_realTailQuadratic_re (a c : ℚ) (x : ℝ) :
    (barrierComplex c 0 * barrierComplex a 0 /
      barrierTailQuadraticDen (barrierComplex a 0) x).re =
      (c : ℝ) * (a : ℝ) / (1 - 2 * (a : ℝ) * x + (a : ℝ) ^ 2) := by
  have hd : barrierTailQuadraticDen (barrierComplex a 0) x =
      ((1 - 2 * (a : ℝ) * x + (a : ℝ) ^ 2 : ℝ) : ℂ) := by
    simp only [barrierTailQuadraticDen, barrierComplex_real, Complex.ofReal_add,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.ofReal_pow]
    ring
  rw [hd]
  simp only [barrierComplex_real, ← Complex.ofReal_mul, ← Complex.ofReal_div,
    Complex.ofReal_re]

private theorem barrier_list_map_sum_re {α : Type*} (rs : List α)
    (f : α → ℂ) (g : α → ℝ) (h : ∀ a, (f a).re = g a) :
    (rs.map f).sum.re = (rs.map g).sum := by
  induction rs with
  | nil => simp
  | cons a rs ih =>
    simp only [List.map_cons, List.sum_cons, Complex.add_re, h a, ih]

private theorem barrier_list_flatMap_sum_re {α : Type*} (rs : List α)
    (expand : α → List (ℂ × ℂ)) (f : ℂ × ℂ → ℂ) (g : α → ℝ)
    (h : ∀ a, ((expand a).map f).sum.re = g a) :
    ((rs.flatMap expand).map f).sum.re = (rs.map g).sum := by
  induction rs with
  | nil => simp
  | cons a rs ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, Complex.add_re,
      List.map_cons, List.sum_cons, h a, ih]

private theorem barrier_grouped_tail_sum_re (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) (f : ℂ × ℂ → ℂ)
    (g : ℚ × ℚ → ℝ) (h : BarrierRationalPairRow → ℝ)
    (hreal : ∀ ac : ℚ × ℚ,
      (f (barrierComplex ac.1 0, barrierComplex ac.2 0)).re = g ac)
    (hpair : ∀ row : BarrierRationalPairRow,
      ((barrierExpandPairRow row).map f).sum.re = h row) :
    ((barrierExpandRealRows rs ++ barrierExpandPairRows ps).map f).sum.re =
      (rs.map g).sum + (ps.map h).sum := by
  have hr : ((barrierExpandRealRows rs).map f).sum.re = (rs.map g).sum := by
    simpa only [barrierExpandRealRows, List.map_map, Function.comp_def] using
      barrier_list_map_sum_re rs
        (fun ac : ℚ × ℚ => f (barrierComplex ac.1 0, barrierComplex ac.2 0)) g hreal
  have hp : ((barrierExpandPairRows ps).map f).sum.re = (ps.map h).sum := by
    simpa only [barrierExpandPairRows] using
      barrier_list_flatMap_sum_re ps barrierExpandPairRow f h hpair
  rw [List.map_append, List.sum_append, Complex.add_re, hr, hp]

theorem barrierP2Tail_quadratic_sum_re_eq_grouped (x : ℝ) :
    (barrierP2Tail.map (fun zr : ℂ × ℂ =>
      zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re =
      barrierGroupedQuadraticTailValue barrierP2RealRows barrierP2PairRows x := by
  rw [barrierP2Tail_eq_grouped]
  unfold barrierGroupedQuadraticTailValue
  apply barrier_grouped_tail_sum_re
  · intro ac
    exact barrier_realTailQuadratic_re ac.1 ac.2 x
  · intro row
    exact barrierConjugatePair_quadratic_eq_ratPolynomial row.a row.b row.c row.d x

theorem barrierV2Tail_linear_sum_re_eq_grouped (x : ℝ) :
    (barrierV2Tail.map (fun zr : ℂ × ℂ =>
      zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re =
      barrierGroupedLinearTailValue barrierV2RealRows barrierV2PairRows x := by
  rw [barrierV2Tail_eq_grouped]
  unfold barrierGroupedLinearTailValue
  apply barrier_grouped_tail_sum_re
  · intro ac
    exact barrier_realTailLinear_re ac.1 ac.2 x
  · intro row
    exact barrierConjugatePair_linear_eq_ratPolynomial row.a row.b row.c row.d x





private theorem barrierLinearFractions_product (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) :
    barrierFractionProduct (barrierLinearFractions rs ps) = barrierGroupedLinearQ rs ps := by
  simp [barrierFractionProduct, barrierLinearFractions, barrierGroupedLinearQ,
    List.map_append, List.prod_append, List.map_map, Function.comp_def]

private theorem barrierQuadraticFractions_product (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) :
    barrierFractionProduct (barrierQuadraticFractions rs ps) = barrierGroupedQuadraticQ rs ps := by
  simp [barrierFractionProduct, barrierQuadraticFractions, barrierGroupedQuadraticQ,
    List.map_append, List.prod_append, List.map_map, Function.comp_def]

private theorem barrierFractionProduct_append (fs gs : List (ℚ[X] × ℚ[X])) :
    barrierFractionProduct (fs ++ gs) = barrierFractionProduct fs * barrierFractionProduct gs := by
  simp [barrierFractionProduct, List.map_append, List.prod_append]

private theorem barrierScaleFractions_product (c : ℚ) (fs : List (ℚ[X] × ℚ[X])) :
    barrierFractionProduct (barrierScaleFractions c fs) = barrierFractionProduct fs := by
  simp [barrierFractionProduct, barrierScaleFractions, List.map_map, Function.comp_def]

private theorem barrierLinearFractions_sum (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) (x : ℝ) :
    barrierFractionSum (barrierLinearFractions rs ps) x =
      barrierGroupedLinearTailValue rs ps x := by
  simp [barrierFractionSum, barrierLinearFractions, barrierGroupedLinearTailValue,
    barrierRealLinearQ, List.map_append, List.sum_append, List.map_map, Function.comp_def]

private theorem barrierQuadraticFractions_sum (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) (x : ℝ) :
    barrierFractionSum (barrierQuadraticFractions rs ps) x =
      barrierGroupedQuadraticTailValue rs ps x := by
  simp [barrierFractionSum, barrierQuadraticFractions, barrierGroupedQuadraticTailValue,
    barrierRealQuadraticQ, eval₂_pow, List.map_append, List.sum_append, List.map_map, Function.comp_def]

private theorem barrierFractionSum_append (fs gs : List (ℚ[X] × ℚ[X])) (x : ℝ) :
    barrierFractionSum (fs ++ gs) x = barrierFractionSum fs x + barrierFractionSum gs x := by
  simp [barrierFractionSum, List.map_append, List.sum_append]

private theorem barrierScaleFractions_sum (c : ℚ) (fs : List (ℚ[X] × ℚ[X])) (x : ℝ) :
    barrierFractionSum (barrierScaleFractions c fs) x = (c : ℝ) * barrierFractionSum fs x := by
  simpa only [barrierFractionSum, barrierScaleFractions, List.map_map, Function.comp_def,
    eval₂_mul, eval₂_C, Rat.coe_castHom, mul_div_assoc] using
    List.sum_map_mul_left fs
      (fun aq : ℚ[X] × ℚ[X] =>
        aq.1.eval₂ (Rat.castHom ℝ) x / aq.2.eval₂ (Rat.castHom ℝ) x) (c : ℝ)



def barrierCase2XDerivativeFormula (x : ℝ) : ℝ :=
  (19 / 48) / x - (1 / 12) / (1 - x) - (65 / 24) * x / (1 + x ^ 2) -
    4 * ((barrierFiniteUDerivative barrierP2Finite).eval₂ (Rat.castHom ℝ) x +
      (barrierP2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re) -
    ((barrierFinitePowerDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x +
      (barrierV2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re)


theorem barrierCase2XFractions_product :
    barrierFractionProduct barrierCase2XFractions = barrierCase2QX := by
  simp only [barrierCase2XFractions, barrierFractionProduct_append,
    barrierScaleFractions_product, barrierLinearFractions_product,
    barrierQuadraticFractions_product]
  simp only [barrierFractionProduct, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, barrierCase2QX, barrierP2QuadraticQ, barrierV2LinearQ]
  ring


theorem barrierCase2XFractions_sum (x : ℝ) :
    barrierFractionSum barrierCase2XFractions x = barrierCase2XDerivativeFormula x := by
  simp only [barrierCase2XFractions, barrierFractionSum_append, barrierScaleFractions_sum,
    barrierLinearFractions_sum, barrierQuadraticFractions_sum]
  unfold barrierCase2XDerivativeFormula
  rw [barrierP2Tail_quadratic_sum_re_eq_grouped, barrierV2Tail_linear_sum_re_eq_grouped]
  norm_num [barrierFractionSum, eval₂_pow]
  ring



theorem barrierCase2AX_clears_denominator {x : ℝ} (hx : |x| ≤ 1)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    barrierCase2AX.eval₂ (Rat.castHom ℝ) x =
      barrierCase2QX.eval₂ (Rat.castHom ℝ) x * barrierCase2XDerivativeFormula x := by
  have hprod : (barrierFractionProduct barrierCase2XFractions).eval₂ (Rat.castHom ℝ) x ≠ 0 := by
    rw [barrierCase2XFractions_product]
    exact barrierCase2QX_eval_ne_zero hx hx0 hx1
  simpa only [barrierCase2AX, barrierCase2XFractions_product, barrierCase2XFractions_sum] using
    barrierFractionNumerator_eval barrierCase2XFractions x hprod

























end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction
namespace OAI

noncomputable section

namespace InternalCatalan

section



theorem barrierCase2X_eq (x : ℝ) :
    barrierCase2X x = realEnergyField 2 x -
      4 * barrierTrialT barrierP2 x - barrierTrialS barrierV2 x := by
  simp only [barrierCase2X, barrierLambda2, zero_mul, add_zero]

private theorem barrier_case2_p_tail_base_lt_one :
    ∀ zr ∈ barrierP2Tail, ‖zr.1‖ < 1 := by
  intro zr hzr
  exact lt_of_le_of_lt (barrierP2_tail_norm_bounds zr hzr).1 (by norm_num)

private theorem barrier_case2_v_tail_base_lt_one :
    ∀ zr ∈ barrierV2Tail, ‖zr.1‖ < 1 := by
  intro zr hzr
  exact lt_of_le_of_lt (barrierV2_tail_norm_bounds zr hzr).1 (by norm_num)

private theorem barrier_case2_pT_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (barrierTrialT barrierP2)
      ((barrierFiniteUDerivative barrierP2Finite).eval₂ (Rat.castHom ℝ) x +
        (barrierP2Tail.map (fun zr : ℂ × ℂ =>
          zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re) x := by
  have hg := barrierTrialT_hasDerivAt_series barrierP2 barrier_trials_abs_summable.1
    barrier_trials_weighted_abs_summable.1 hx
  have hs := barrierTrial_U_hasSum barrierP2Finite barrierP2Tail
    barrier_case2_p_tail_base_lt_one (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)
  apply hg.congr_deriv
  exact hs.tsum_eq


private theorem barrier_case2_vS_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (barrierTrialS barrierV2)
      ((barrierFinitePowerDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x +
        (barrierV2Tail.map (fun zr : ℂ × ℂ =>
          zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re) x := by
  have hg := barrierTrialS_hasDerivAt_series barrierV2 barrier_trials_abs_summable.2.1 hx
  have hs := barrierTrial_power_hasSum barrierV2Finite barrierV2Tail
    barrier_case2_v_tail_base_lt_one (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)
  apply hg.congr_deriv
  exact hs.tsum_eq

private theorem barrier_realEnergyField_two_hasDerivAt {x : ℝ}
    (h0 : x ≠ 0) (h1 : x ≠ 1) :
    HasDerivAt (realEnergyField 2)
      ((19 / 48 : ℝ) / x - (1 / 12 : ℝ) / (1 - x) -
        (65 / 24 : ℝ) * x / (1 + x ^ 2)) x := by
  have ho : 1 - x ≠ 0 := sub_ne_zero.mpr h1.symm
  have hd : 1 + x ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < 1 + x ^ 2)
  have hl0 : HasDerivAt (fun y : ℝ => Real.log |y|) (1 / x) x := by
    simpa only [Real.log_abs, one_div] using Real.hasDerivAt_log h0
  have hl1 : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1 / (1 - x)) x :=
    ((hasDerivAt_id x).const_sub (1 : ℝ)).log ho
  have hp : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add (1 : ℝ)
  have hh := ((hl0.const_mul (19 / 48 : ℝ)).add
    (hl1.const_mul (1 / 12 : ℝ))).sub
    ((hp.log hd).const_mul ((2 : ℝ) / 2 + 17 / 48))
  unfold realEnergyField
  apply hh.congr_deriv
  field_simp [h0, ho, hd]
  ring


theorem barrierCase2X_hasDerivAt {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (h0 : x ≠ 0) :
    HasDerivAt barrierCase2X (barrierCase2XDerivativeFormula x) x := by
  have hh := ((barrier_realEnergyField_two_hasDerivAt h0 (ne_of_lt hx.2)).sub
    ((barrier_case2_pT_hasDerivAt hx).const_mul (4 : ℝ))).sub
    (barrier_case2_vS_hasDerivAt hx)
  have hfun : barrierCase2X = (fun y : ℝ => realEnergyField 2 y -
      4 * barrierTrialT barrierP2 y - barrierTrialS barrierV2 y) :=
    funext barrierCase2X_eq
  rw [hfun]
  apply hh.congr_deriv
  unfold barrierCase2XDerivativeFormula
  rfl


end

section

open Set Filter
open scoped Topology

private theorem barrier2_atBot_add_finite {l : Filter ℝ} {f g : ℝ → ℝ} {c : ℝ}
    (hf : Tendsto f l atBot) (hg : Tendsto g l (𝓝 c)) :
    Tendsto (fun x => f x + g x) l atBot := by
  have hb : ∀ᶠ x in l, g x ≤ c + 1 :=
    ((tendsto_order.mp hg).2 (c + 1) (by linarith)).mono (fun _ hx => hx.le)
  exact tendsto_atBot_add_right_of_ge' l (c + 1) hf hb

private theorem barrier2_log_one_sub_tendsto :
    Tendsto (fun x : ℝ => Real.log (1 - x)) (𝓝[<] 1) atBot := by
  have hc : Continuous (fun x : ℝ => 1 - x) := continuous_const.sub continuous_id
  have ht : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (hc.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change x < 1 at hx
      change 0 < 1 - x
      exact sub_pos.mpr hx
  exact Real.tendsto_log_nhdsGT_zero.comp ht

private theorem barrier2_continuousOn_tendsto_one_left {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    Tendsto f (𝓝[<] 1) (𝓝 (f 1)) := by
  have ht : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝[Icc (-1) 1] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨nhdsWithin_le_nhds, ?_⟩
    have ha : ∀ᶠ x : ℝ in 𝓝[<] 1, -1 < x :=
      (eventually_gt_nhds (by norm_num : (-1 : ℝ) < 1)).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [ha, self_mem_nhdsWithin] with x hx hx1
    exact ⟨hx.le, le_of_lt hx1⟩
  exact (hf 1 (by norm_num)).tendsto.comp ht

private theorem barrier2_continuousOn_continuousAt_zero {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) : ContinuousAt f 0 :=
  (hf 0 (by norm_num)).continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))

private def barrierCase2XRegular (x : ℝ) : ℝ :=
  -(65 / 48 : ℝ) * Real.log (1 + x ^ 2) -
    4 * barrierTrialT barrierP2 x - barrierTrialS barrierV2 x

private theorem barrierCase2XRegular_continuousOn :
    ContinuousOn barrierCase2XRegular (Icc (-1 : ℝ) 1) := by
  have hl : Continuous (fun x : ℝ => Real.log (1 + x ^ 2)) := by
    apply Continuous.log (continuous_const.add (continuous_id.pow 2))
    intro x
    change 1 + x ^ 2 ≠ 0
    exact ne_of_gt (by positivity : (0 : ℝ) < 1 + x ^ 2)
  have ht := barrierTrialT_continuousOn barrierP2 barrier_trials_abs_summable.1
  have hs := barrierTrialS_continuousOn barrierV2 barrier_trials_abs_summable.2.1
  exact ((hl.continuousOn.const_mul (-(65 / 48 : ℝ))).sub (ht.const_mul 4)).sub hs


private theorem barrierCase2X_split (x : ℝ) :
    barrierCase2X x = (19 / 48 : ℝ) * Real.log |x| +
      (1 / 12 : ℝ) * Real.log (1 - x) + barrierCase2XRegular x := by
  rw [barrierCase2X_eq]
  unfold realEnergyField barrierCase2XRegular
  ring

private theorem barrierCase2X_zero_remainder :
    ContinuousAt (fun x : ℝ => (1 / 12 : ℝ) * Real.log (1 - x) +
      barrierCase2XRegular x) 0 := by
  have hl : ContinuousAt (fun x : ℝ => Real.log (1 - x)) 0 :=
    (continuousAt_const.sub continuousAt_id).log (by norm_num)
  exact (hl.const_mul (1 / 12 : ℝ)).add
    (barrier2_continuousOn_continuousAt_zero barrierCase2XRegular_continuousOn)

theorem barrierCase2X_tendsto_zero_left :
    Tendsto barrierCase2X (𝓝[<] 0) atBot := by
  have hl : Tendsto (fun x : ℝ => (19 / 48 : ℝ) * Real.log |x|)
      (𝓝[<] 0) atBot := by
    simpa only [Real.log_abs] using
      (Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 19 / 48)
        Real.tendsto_log_nhdsLT_zero)
  have hh := barrier2_atBot_add_finite hl
    (barrierCase2X_zero_remainder.tendsto.mono_left nhdsWithin_le_nhds)
  convert hh using 1
  funext x
  rw [barrierCase2X_split]
  ring

theorem barrierCase2X_tendsto_zero_right :
    Tendsto barrierCase2X (𝓝[>] 0) atBot := by
  have hl : Tendsto (fun x : ℝ => (19 / 48 : ℝ) * Real.log |x|)
      (𝓝[>] 0) atBot := by
    simpa only [Real.log_abs] using
      (Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 19 / 48)
        Real.tendsto_log_nhdsGT_zero)
  have hh := barrier2_atBot_add_finite hl
    (barrierCase2X_zero_remainder.tendsto.mono_left nhdsWithin_le_nhds)
  convert hh using 1
  funext x
  rw [barrierCase2X_split]
  ring

theorem barrierCase2X_tendsto_one_left :
    Tendsto barrierCase2X (𝓝[<] 1) atBot := by
  have hl := Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 1 / 12)
    barrier2_log_one_sub_tendsto
  have hc : ContinuousAt (fun x : ℝ => Real.log |x|) 1 := by
    simpa only [Real.log_abs] using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0))
  have hr := ((hc.tendsto.mono_left nhdsWithin_le_nhds).const_mul (19 / 48 : ℝ)).add
    (barrier2_continuousOn_tendsto_one_left barrierCase2XRegular_continuousOn)
  have hh := barrier2_atBot_add_finite hl hr
  convert hh using 1
  funext x
  rw [barrierCase2X_split]
  ring



private theorem barrierCase2X_continuousWithinAt {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) (h0 : x ≠ 0) (h1 : x ≠ 1) :
    ContinuousWithinAt barrierCase2X (Icc (-1 : ℝ) 1) x := by
  have hlog : ContinuousAt (fun y : ℝ => Real.log |y|) x := by
    simpa only [Real.log_abs] using Real.continuousAt_log h0
  have hlog1 : ContinuousAt (fun y : ℝ => Real.log (1 - y)) x :=
    (continuousAt_const.sub continuousAt_id).log (sub_ne_zero.mpr (Ne.symm h1))
  have hh := ((hlog.continuousWithinAt.const_mul (19 / 48 : ℝ)).add
    (hlog1.continuousWithinAt.const_mul (1 / 12 : ℝ))).add
    (barrierCase2XRegular_continuousOn x hx)
  convert hh using 1
  funext y
  exact barrierCase2X_split y

theorem barrierCase2X_continuousOn_negative :
    ContinuousOn barrierCase2X (Ico (-1 : ℝ) 0) := by
  intro x hx
  apply (barrierCase2X_continuousWithinAt
    ⟨hx.1, by linarith [hx.2]⟩ (ne_of_lt hx.2) (by linarith [hx.2])).mono
  intro y hy
  exact ⟨hy.1, by linarith [hy.2]⟩

theorem barrierCase2X_continuousOn_positive :
    ContinuousOn barrierCase2X (Ioo (0 : ℝ) 1) := by
  intro x hx
  apply (barrierCase2X_continuousWithinAt
    ⟨by linarith [hx.1], hx.2.le⟩ (ne_of_gt hx.1) (ne_of_lt hx.2)).mono
  intro y hy
  exact ⟨by linarith [hy.1], hy.2.le⟩


end

section
open scoped BigOperators











end
section

theorem barrierCase2X_deriv_eq_zero_iff {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (h0 : x ≠ 0) :
    deriv barrierCase2X x = 0 ↔ (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0 := by
  have ha : |x| ≤ 1 := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
  have h1 : x ≠ 1 := ne_of_lt hx.2
  rw [(barrierCase2X_hasDerivAt hx h0).deriv, Polynomial.eval_map,
    barrierCase2AX_clears_denominator ha h0 h1]
  simp [barrierCase2QX_eval_ne_zero ha h0 h1]


end

section

open scoped ComplexConjugate




end

open Set

theorem barrierCase2X_le_of_bracket_bounds (M : ℝ)
    (hneg : barrierCase2X (-1) ≤ M)
    (hbr : ∀ m ∈ barrierCase2XBrackets, ∀ x ∈
      Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ),
      barrierCase2X x ≤ M) :
    ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo (0 : ℝ) 1, barrierCase2X x ≤ M := by
  apply GlobalMaxReduction.le_on_two_components_of_stationary_cover
    (S := {x | ∃ m ∈ barrierCase2XBrackets,
      x ∈ Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)})
  · exact barrierCase2X_continuousOn_negative
  · exact barrierCase2X_continuousOn_positive
  · exact hneg
  · exact barrierCase2X_tendsto_zero_left
  · exact barrierCase2X_tendsto_zero_right
  · exact barrierCase2X_tendsto_one_left
  · intro x hx hd
    have h0 : x ≠ 0 := by rcases hx with hx | hx <;> linarith [hx.1, hx.2]
    have hdomain : x ∈ Ioo (-1 : ℝ) 1 := by
      rcases hx with hx | hx
      · exact ⟨hx.1, by linarith [hx.2]⟩
      · exact ⟨by linarith [hx.1], hx.2⟩
    exact barrierCase2AX_roots_exhausted hx
      ((barrierCase2X_deriv_eq_zero_iff hdomain h0).1 hd)
  · rintro x ⟨m, hm, hx⟩
    exact hbr m hm x hx


end InternalCatalan

end

end OAI

end

section
open OAI.InternalCatalan
open Set

theorem solution (M : ℝ)
    (hneg : barrierCase2X (-1) ≤ M)
    (hbr : ∀ m ∈ barrierCase2XBrackets, ∀ x ∈
      Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ),
      barrierCase2X x ≤ M) :
    ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo (0 : ℝ) 1, barrierCase2X x ≤ M := by
  first
  | exact @OAI.InternalCatalan.barrierCase2X_le_of_bracket_bounds
  | (apply OAI.InternalCatalan.barrierCase2X_le_of_bracket_bounds <;> assumption)

end
