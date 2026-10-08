-- Prove2me | solution 1 for OAI.InternalCatalan.barrierCase2Y_global_upper
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T19:06:02.584206+00:00
-- url     : https://prove2.me/submissions/a3c450c5-2180-4688-b1b9-d425f9eaaa39

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
import Theorems.Thm_OAI_InternalCatalan_barrierCase2Y_bracket_left_lt
import Theorems.Thm_OAI_InternalCatalan_barrierCase2Y_le_of_bracket_bounds

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

def barrierTailQuadraticDen (z : ℂ) (x : ℝ) : ℂ :=
  1 - 2 * (x : ℂ) * z + z ^ 2
































open Polynomial






def barrierPairLinearQ (a b : ℚ) : ℚ[X] :=
  (1 - C a * X) ^ 2 + (C b * X) ^ 2

def barrierPairLinearA (a b c d : ℚ) : ℚ[X] :=
  2 * (C (c * a - d * b) * (1 - C a * X) - C (c * b + d * a) * C b * X)









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


theorem barrierTrialT_summable (u : ℕ → ℝ) (hu : Summable (fun k => |u k|))
    {x : ℝ} (hx : |x| ≤ 1) :
    Summable (fun k : ℕ => u (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x /
      ((k + 1 : ℕ) : ℝ)) := by
  exact ((summable_nat_add_iff 1).mpr hu).of_norm_bounded
    (fun k => barrierTrialT_term_norm_le u k hx)





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
-- module Solutions.OAICatalan.Catalan.FirstBarrier.BarrierCaseOneDescartesX0
namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial
open scoped BigOperators

def barrierFiniteUDerivative (cs : List ℤ) : ℚ[X] :=
  ∑ k ∈ Finset.range cs.length,
    C ((cs.getD k 0 : ℚ) / 100000000) * Chebyshev.U ℚ (k : ℤ)

def barrierFinitePowerDerivative (cs : List ℤ) : ℚ[X] :=
  ∑ k ∈ Finset.range cs.length,
    C ((cs.getD k 0 : ℚ) / 100000000) * X ^ k











end

section

open Polynomial
























end

section



open Polynomial
open scoped BigOperators




end




open Polynomial



open Polynomial




















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
-- module Solutions.OAICatalan.Catalan.Estimates.RealEnergyChebyshev
namespace OAI

noncomputable section

namespace InternalCatalan

section





end

section

open Set
open scoped ComplexConjugate

def realEnergyCirclePoint (u : ℝ) : ℂ :=
  (u : ℂ) + Complex.I * (Real.sqrt (1 - u ^ 2) : ℂ)

theorem realEnergyCirclePoint_norm {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    ‖realEnergyCirclePoint u‖ = 1 := by
  have hn : ‖u‖ ≤ 1 := by simpa only [Real.norm_eq_abs] using abs_le.mpr hu
  have h := Complex.normSq_ofReal_add_I_mul_sqrt_one_sub hn
  change Complex.normSq (realEnergyCirclePoint u) = 1 at h
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (realEnergyCirclePoint u)]

theorem realEnergyCirclePoint_add_conj (u : ℝ) :
    realEnergyCirclePoint u + conj (realEnergyCirclePoint u) = 2 * (u : ℂ) := by
  apply Complex.ext <;> simp [realEnergyCirclePoint]
  ring

theorem realEnergyCirclePoint_mul_conj {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    realEnergyCirclePoint u * conj (realEnergyCirclePoint u) = 1 := by
  rw [Complex.mul_conj', realEnergyCirclePoint_norm hu]
  norm_num






end

open Polynomial Set
open scoped ComplexConjugate




end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FirstBarrier.BarrierCaseOneBracketHeight
namespace OAI

noncomputable section

namespace InternalCatalan

section








end

namespace Case1Height
open Polynomial
open scoped BigOperators

theorem abs_U_eval_le (k : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |(Chebyshev.U ℝ (k : ℤ)).eval x| ≤ (k : ℝ) + 1 := by
  have h := Chebyshev.abs_iterate_derivative_T_real_le ((k : ℤ) + 1) 1 hx
  simp only [Function.iterate_one] at h
  rw [Chebyshev.derivative_T_eval_one] at h
  rw [Chebyshev.T_derivative_eq_U, eval_mul, eval_intCast] at h
  have hi : (k : ℤ) + 1 - 1 = (k : ℤ) := by ring
  rw [hi, abs_mul] at h
  have hn : (((k : ℤ) + 1 : ℤ) : ℝ) = (k : ℝ) + 1 := by norm_num
  rw [hn] at h
  have hp : 0 < (k : ℝ) + 1 := by positivity
  rw [abs_of_pos hp] at h
  exact le_of_mul_le_mul_left (by simpa only [sq] using h) hp

theorem finiteU_abs_le_mass (cs : List ℤ) {x : ℝ} (hx : |x| ≤ 1) :
    |(barrierFiniteUDerivative cs).eval₂ (Rat.castHom ℝ) x| ≤
      ∑ k ∈ Finset.range cs.length,
        |(cs.getD k 0 : ℝ) / 100000000| * ((k : ℝ) + 1) := by
  have hd : (barrierFiniteUDerivative cs).eval₂ (Rat.castHom ℝ) x =
      ∑ k ∈ Finset.range cs.length,
        ((cs.getD k 0 : ℝ) / 100000000) * (Chebyshev.U ℝ (k : ℤ)).eval x := by
    simp only [barrierFiniteUDerivative, eval₂_finsetSum, eval₂_mul,
      eval₂_C, map_div₀, map_intCast, map_ofNat]
    simp only [eval₂_eq_eval_map, Chebyshev.map_U]
  rw [hd]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_U_eval_le k hx) (abs_nonneg _)

theorem finitePower_abs_le_mass (cs : List ℤ) {x : ℝ} (hx : |x| ≤ 1) :
    |(barrierFinitePowerDerivative cs).eval₂ (Rat.castHom ℝ) x| ≤
      ∑ k ∈ Finset.range cs.length, |(cs.getD k 0 : ℝ) / 100000000| := by
  have hd : (barrierFinitePowerDerivative cs).eval₂ (Rat.castHom ℝ) x =
      ∑ k ∈ Finset.range cs.length,
        ((cs.getD k 0 : ℝ) / 100000000) * x ^ k := by
    simp only [barrierFinitePowerDerivative, eval₂_finsetSum, eval₂_mul,
      eval₂_C, eval₂_X_pow, map_div₀, map_intCast, map_ofNat]
  rw [hd]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul, abs_pow]
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg x) hx)
    (abs_nonneg ((cs.getD k 0 : ℝ) / 100000000))).trans_eq (mul_one _)







end Case1Height

section

open Set Filter
open scoped Topology















end









open Set

namespace Case1Height




theorem abs_sub_le_on_Icc {f : ℝ → ℝ} {a b C x : ℝ}
    (hdiff : ∀ y ∈ Icc a b, DifferentiableAt ℝ f y)
    (hbound : ∀ y ∈ Icc a b, |deriv f y| ≤ C)
    (hx : x ∈ Icc a b) : |f x - f a| ≤ C * |x - a| := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hx.1.trans hx.2⟩
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => (hdiff y hy).hasDerivAt.hasDerivWithinAt)
      (fun y hy => by simpa only [Real.norm_eq_abs] using hbound y hy)
      (convex_Icc a b) ha hx

theorem actual_bracket_width (m : ℤ) :
    (barrierBracketRight m : ℝ) - (barrierBracketLeft m : ℝ) =
      (2 / 10000000000 : ℝ) := by
  norm_num [barrierBracketLeft, barrierBracketRight]
  ring


end Case1Height



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoXExplicitGroup7
namespace OAI

noncomputable section

namespace InternalCatalan

structure BarrierRationalPairRow where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ










open Polynomial


def barrierRealQuadraticQ (a : ℚ) : ℚ[X] := 1 - 2 * C a * X + C (a ^ 2)























open Polynomial

def barrierGroupedLinearTailValue (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) (x : ℝ) : ℝ :=
  (rs.map (fun ac : ℚ × ℚ =>
    (ac.2 : ℝ) * (ac.1 : ℝ) / (1 - (ac.1 : ℝ) * x))).sum +
  (ps.map (fun row : BarrierRationalPairRow =>
    (barrierPairLinearA row.a row.b row.c row.d).eval₂ (Rat.castHom ℝ) x /
      (barrierPairLinearQ row.a row.b).eval₂ (Rat.castHom ℝ) x)).sum
























def barrierCase2XDerivativeFormula (x : ℝ) : ℝ :=
  (19 / 48) / x - (1 / 12) / (1 - x) - (65 / 24) * x / (1 + x ^ 2) -
    4 * ((barrierFiniteUDerivative barrierP2Finite).eval₂ (Rat.castHom ℝ) x +
      (barrierP2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re) -
    ((barrierFinitePowerDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x +
      (barrierV2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re)

def barrierCase2YDerivativeFormula (x : ℝ) : ℝ :=
  (7 / 48) / x - (1 / 12) / (1 - x) +
    2 * ((barrierFiniteUDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x +
      (barrierV2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re)































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





private theorem barrier_case2_v_tail_base_lt_one :
    ∀ zr ∈ barrierV2Tail, ‖zr.1‖ < 1 := by
  intro zr hzr
  exact lt_of_le_of_lt (barrierV2_tail_norm_bounds zr hzr).1 (by norm_num)


private theorem barrier_case2_vT_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (barrierTrialT barrierV2)
      ((barrierFiniteUDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x +
        (barrierV2Tail.map (fun zr : ℂ × ℂ =>
          zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re) x := by
  have hg := barrierTrialT_hasDerivAt_series barrierV2 barrier_trials_abs_summable.2.1
    barrier_trials_weighted_abs_summable.2.1 hx
  have hs := barrierTrial_U_hasSum barrierV2Finite barrierV2Tail
    barrier_case2_v_tail_base_lt_one (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)
  apply hg.congr_deriv
  exact hs.tsum_eq



private theorem barrier_case2_column_hasDerivAt {x : ℝ}
    (h0 : x ≠ 0) (h1 : x ≠ 1) :
    HasDerivAt realEnergyColumnField
      ((7 / 48 : ℝ) / x - (1 / 12 : ℝ) / (1 - x)) x := by
  have ho : 1 - x ≠ 0 := sub_ne_zero.mpr h1.symm
  have hl0 : HasDerivAt Real.log (1 / x) x := by
    simpa only [one_div] using Real.hasDerivAt_log h0
  have hl1 : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1 / (1 - x)) x :=
    ((hasDerivAt_id x).const_sub (1 : ℝ)).log ho
  have hh := (hl0.const_mul (7 / 48 : ℝ)).add (hl1.const_mul (1 / 12 : ℝ))
  unfold realEnergyColumnField
  apply hh.congr_deriv
  field_simp [h0, ho]
  ring


theorem barrierCase2Y_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt barrierCase2Y (barrierCase2YDerivativeFormula x) x := by
  have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨lt_trans (by norm_num) hx.1, hx.2⟩
  have hh := (barrier_case2_column_hasDerivAt (ne_of_gt hx.1) (ne_of_lt hx.2)).add
    ((barrier_case2_vT_hasDerivAt hx').const_mul (2 : ℝ))
  unfold barrierCase2Y
  apply hh.congr_deriv
  unfold barrierCase2YDerivativeFormula
  rfl

end

section

open Set Filter
open scoped Topology



















end

section
open scoped BigOperators











end
section



end

section

open scoped ComplexConjugate




end

open Set



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoBracketHeight
namespace OAI

noncomputable section

namespace InternalCatalan

namespace Case2Height
open Polynomial Set
open scoped BigOperators ComplexConjugate

theorem linear_den_norm_lower {x : ℝ} {z : ℂ} (hx : |x| ≤ 1) :
    1 - ‖z‖ ≤ ‖barrierTailLinearDen z x‖ := by
  have hm : ‖(x : ℂ) * z‖ ≤ ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hx (norm_nonneg z)
  change 1 - ‖z‖ ≤ ‖(1 : ℂ) - (x : ℂ) * z‖
  exact (sub_le_sub_left hm 1).trans
    (by simpa only [norm_one] using norm_sub_norm_le (1 : ℂ) ((x : ℂ) * z))

theorem quadratic_den_norm_lower {x : ℝ} {z : ℂ} (hx : |x| ≤ 1)
    (hz : ‖z‖ ≤ 1) : (1 - ‖z‖) ^ 2 ≤ ‖barrierTailQuadraticDen z x‖ := by
  have hx' : x ∈ Icc (-1 : ℝ) 1 := abs_le.mp hx
  have hA : 1 - ‖z‖ ≤ ‖(1 : ℂ) - z * realEnergyCirclePoint x‖ := by
    simpa only [norm_one, norm_mul, realEnergyCirclePoint_norm hx', mul_one] using
      norm_sub_norm_le (1 : ℂ) (z * realEnergyCirclePoint x)
  have hB : 1 - ‖z‖ ≤ ‖(1 : ℂ) - z * conj (realEnergyCirclePoint x)‖ := by
    simpa only [norm_one, norm_mul, Complex.norm_conj,
      realEnergyCirclePoint_norm hx', mul_one] using
      norm_sub_norm_le (1 : ℂ) (z * conj (realEnergyCirclePoint x))
  have hfactor :
      ((1 : ℂ) - z * realEnergyCirclePoint x) *
        (1 - z * conj (realEnergyCirclePoint x)) = barrierTailQuadraticDen z x := by
    calc
      _ = 1 - z * (realEnergyCirclePoint x + conj (realEnergyCirclePoint x)) +
          z ^ 2 * (realEnergyCirclePoint x * conj (realEnergyCirclePoint x)) := by ring
      _ = _ := by
        rw [realEnergyCirclePoint_add_conj, realEnergyCirclePoint_mul_conj hx']
        unfold barrierTailQuadraticDen
        ring
  calc
    _ ≤ ‖(1 : ℂ) - z * realEnergyCirclePoint x‖ *
        ‖(1 : ℂ) - z * conj (realEnergyCirclePoint x)‖ := by
      simpa only [pow_two] using mul_le_mul hA hB (sub_nonneg.mpr hz) (norm_nonneg _)
    _ = _ := by rw [← norm_mul, hfactor]

private theorem quotient_norm_le {u d : ℂ} {D B : ℝ}
    (hu : ‖u‖ ≤ 1) (hD : 0 < D) (hd : D ≤ ‖d‖)
    (hB : 0 ≤ B) (hBD : 1 ≤ B * D) : ‖u / d‖ ≤ B := by
  rw [norm_div]
  apply (div_le_iff₀ (hD.trans_le hd)).mpr
  exact hu.trans (hBD.trans (mul_le_mul_of_nonneg_left hd hB))

private theorem numerator_norm_le {z r : ℂ} (hz : ‖z‖ ≤ 1) (hr : ‖r‖ ≤ 1) :
    ‖r * z‖ ≤ 1 := by
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul hr hz (norm_nonneg z) (by norm_num : (0 : ℝ) ≤ 1)

private theorem norm_map_sum_le {α : Type*} (tail : List α) (f : α → ℂ) (B : ℝ)
    (hb : ∀ a ∈ tail, ‖f a‖ ≤ B) : ‖(tail.map f).sum‖ ≤ (tail.length : ℝ) * B := by
  revert hb
  induction tail with
  | nil => intro _; simp
  | cons a tail ih =>
      intro hb
      have ha := hb a List.mem_cons_self
      have ht := ih (fun b h => hb b (List.mem_cons_of_mem _ h))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      exact (norm_add_le _ _).trans ((add_le_add ha ht).trans_eq (by ring))

theorem actual_finite_bounds {x : ℝ} (hx : |x| ≤ 1) :
    |(barrierFiniteUDerivative barrierP2Finite).eval₂ (Rat.castHom ℝ) x| ≤ 55 ∧
    |(barrierFiniteUDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x| ≤ 55 ∧
    |(barrierFinitePowerDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x| ≤ 10 := by
  refine ⟨(Case1Height.finiteU_abs_le_mass barrierP2Finite hx).trans ?_,
    (Case1Height.finiteU_abs_le_mass barrierV2Finite hx).trans ?_,
    (Case1Height.finitePower_abs_le_mass barrierV2Finite hx).trans ?_⟩
  all_goals norm_num [barrierP2Finite, barrierV2Finite, Finset.sum_range_succ]

theorem actual_tail_bounds {x : ℝ} (hx : |x| ≤ 1) :
    |(barrierP2Tail.map (fun zr : ℂ × ℂ =>
      zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re| ≤ 2800 ∧
    |(barrierV2Tail.map (fun zr : ℂ × ℂ =>
      zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re| ≤ 832 ∧
    |(barrierV2Tail.map (fun zr : ℂ × ℂ =>
      zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re| ≤ 52000 := by
  have hp : ∀ zr ∈ barrierP2Tail,
      ‖zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x‖ ≤ 280 := by
    intro zr hzr
    obtain ⟨hz, hr⟩ := barrierP2_tail_norm_bounds zr hzr
    have hz1 : ‖zr.1‖ ≤ 1 := hz.trans (by norm_num)
    have hgap : (3 / 50 : ℝ) ≤ 1 - ‖zr.1‖ := by linarith
    have hd : (3 / 50 : ℝ) ^ 2 ≤ ‖barrierTailQuadraticDen zr.1 x‖ := by
      apply le_trans _ (quadratic_den_norm_lower hx hz1)
      nlinarith only [hgap, sq_nonneg (1 - ‖zr.1‖ - 3 / 50)]
    exact quotient_norm_le (numerator_norm_le hz1 hr.le) (by norm_num) hd
      (by norm_num) (by norm_num)
  have hvl : ∀ zr ∈ barrierV2Tail,
      ‖zr.2 * zr.1 / barrierTailLinearDen zr.1 x‖ ≤ 64 := by
    intro zr hzr
    obtain ⟨hz, hr⟩ := barrierV2_tail_norm_bounds zr hzr
    have hz1 : ‖zr.1‖ ≤ 1 := hz.trans (by norm_num)
    have hgap : (2 / 125 : ℝ) ≤ 1 - ‖zr.1‖ := by linarith
    have hd := hgap.trans (linear_den_norm_lower hx (z := zr.1))
    exact quotient_norm_le (numerator_norm_le hz1 hr.le) (by norm_num) hd
      (by norm_num) (by norm_num)
  have hvq : ∀ zr ∈ barrierV2Tail,
      ‖zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x‖ ≤ 4000 := by
    intro zr hzr
    obtain ⟨hz, hr⟩ := barrierV2_tail_norm_bounds zr hzr
    have hz1 : ‖zr.1‖ ≤ 1 := hz.trans (by norm_num)
    have hgap : (2 / 125 : ℝ) ≤ 1 - ‖zr.1‖ := by linarith
    have hd : (2 / 125 : ℝ) ^ 2 ≤ ‖barrierTailQuadraticDen zr.1 x‖ := by
      apply le_trans _ (quadratic_den_norm_lower hx hz1)
      nlinarith only [hgap, sq_nonneg (1 - ‖zr.1‖ - 2 / 125)]
    exact quotient_norm_le (numerator_norm_le hz1 hr.le) (by norm_num) hd
      (by norm_num) (by norm_num)
  constructor
  · exact (Complex.abs_re_le_norm _).trans
      ((norm_map_sum_le barrierP2Tail _ 280 hp).trans_eq (by rw [barrier_tail_lengths.1]; norm_num))
  constructor
  · exact (Complex.abs_re_le_norm _).trans
      ((norm_map_sum_le barrierV2Tail _ 64 hvl).trans_eq (by rw [barrier_tail_lengths.2]; norm_num))
  · exact (Complex.abs_re_le_norm _).trans
      ((norm_map_sum_le barrierV2Tail _ 4000 hvq).trans_eq (by rw [barrier_tail_lengths.2]; norm_num))

private theorem abs_div_le_const {a b B : ℝ} (hb : 0 < |b|)
    (h : |a| ≤ B * |b|) : |a / b| ≤ B := by
  rw [abs_div]
  exact (div_le_iff₀ hb).mpr h

private theorem abs_sub_le_pair (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa only [Real.norm_eq_abs] using norm_sub_le a b



theorem Y_formula_abs_le {x : ℝ} (hx : |x| ≤ 1)
    (hxmargin : (7 / 10000 : ℝ) ≤ |x|)
    (hgap : (7 / 10000 : ℝ) ≤ 1 - x) :
    |barrierCase2YDerivativeFormula x| ≤ 120000 := by
  have hxpos : 0 < |x| := lt_of_lt_of_le (by norm_num) hxmargin
  have hgpos : 0 < 1 - x := lt_of_lt_of_le (by norm_num) hgap
  obtain ⟨_, hvu, _⟩ := actual_finite_bounds hx
  obtain ⟨_, _, hvt⟩ := actual_tail_bounds hx
  have hA : |(7 / 48 : ℝ) / x| ≤ 209 := by
    apply abs_div_le_const hxpos
    norm_num
    linarith
  have hB : |(1 / 12 : ℝ) / (1 - x)| ≤ 120 := by
    apply abs_div_le_const (abs_pos.mpr hgpos.ne')
    rw [abs_of_pos hgpos]
    norm_num
    linarith
  have hC : |2 * ((barrierFiniteUDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x +
      (barrierV2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re)| ≤ 104110 := by
    rw [abs_mul]
    norm_num
    have hh := abs_add_le ((barrierFiniteUDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x)
      ((barrierV2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re)
    linarith
  unfold barrierCase2YDerivativeFormula
  have hab := abs_sub_le_pair ((7 / 48 : ℝ) / x) ((1 / 12 : ℝ) / (1 - x))
  have habc := abs_add_le (((7 / 48 : ℝ) / x) - ((1 / 12 : ℝ) / (1 - x)))
    (2 * ((barrierFiniteUDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x +
      (barrierV2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re))
  linarith

end Case2Height

open Set

namespace Case2Height


theorem Y_closed_bracket_margins (m : ℤ) (hm : m ∈ barrierCase2YBrackets)
    {x : ℝ} (hx : x ∈ Icc (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    x ∈ Ioo (0 : ℝ) 1 ∧ |x| ≤ 1 ∧
      (7 / 10000 : ℝ) ≤ |x| ∧ (7 / 10000 : ℝ) ≤ 1 - x := by
  have he : (7 / 10000 : ℝ) ≤ (barrierBracketLeft m : ℝ) ∧
      (barrierBracketRight m : ℝ) ≤ 1 - (7 / 10000 : ℝ) := by
    simp only [barrierCase2YBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    <;> norm_num [barrierBracketLeft, barrierBracketRight]
  have hdomain : x ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2, he.1, he.2]
  refine ⟨hdomain, ?_, ?_, ?_⟩
  · rw [abs_of_pos hdomain.1]
    exact hdomain.2.le
  · rw [abs_of_pos hdomain.1]
    exact he.1.trans hx.1
  · linarith [hx.2, he.2]

private theorem height_of_abs_variation {f : ℝ → ℝ} {m : ℤ} {x : ℝ}
    (hx : x ∈ Icc (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ))
    (hvar : |f x - f (barrierBracketLeft m : ℝ)| ≤
      120000 * |x - (barrierBracketLeft m : ℝ)|) :
    f x ≤ f (barrierBracketLeft m : ℝ) + (24 / 1000000 : ℝ) := by
  have hdist : |x - (barrierBracketLeft m : ℝ)| ≤
      (barrierBracketRight m : ℝ) - (barrierBracketLeft m : ℝ) := by
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
    exact sub_le_sub_right hx.2 _
  have he : |f x - f (barrierBracketLeft m : ℝ)| ≤ (24 / 1000000 : ℝ) := by
    calc
      _ ≤ 120000 * |x - (barrierBracketLeft m : ℝ)| := hvar
      _ ≤ 120000 * ((barrierBracketRight m : ℝ) - (barrierBracketLeft m : ℝ)) :=
        mul_le_mul_of_nonneg_left hdist (by norm_num)
      _ = (24 / 1000000 : ℝ) := by rw [Case1Height.actual_bracket_width]; norm_num
  have hs := (le_abs_self (f x - f (barrierBracketLeft m : ℝ))).trans he
  linarith

end Case2Height


theorem barrierCase2Y_bracket_height (m : ℤ) (hm : m ∈ barrierCase2YBrackets)
    {x : ℝ} (hx : x ∈ Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    barrierCase2Y x ≤ barrierCase2Y (barrierBracketLeft m : ℝ) +
      (24 / 1000000 : ℝ) := by
  have hxcc : x ∈ Icc (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) :=
    ⟨hx.1.le, hx.2.le⟩
  apply Case2Height.height_of_abs_variation hxcc
  apply Case1Height.abs_sub_le_on_Icc
  · intro y hy
    obtain ⟨hyD, _, _, _⟩ := Case2Height.Y_closed_bracket_margins m hm hy
    exact (barrierCase2Y_hasDerivAt hyD).differentiableAt
  · intro y hy
    obtain ⟨hyD, hyabs, hy0, hy1⟩ := Case2Height.Y_closed_bracket_margins m hm hy
    rw [(barrierCase2Y_hasDerivAt hyD).deriv]
    exact Case2Height.Y_formula_abs_le hyabs hy0 hy1
  · exact hxcc

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoGlobalBounds
namespace OAI


noncomputable section
namespace InternalCatalan













































































end InternalCatalan




namespace InternalCatalan










theorem barrierCase2Y_global_upper {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    barrierCase2Y x ≤ (-160890 / 100000 : ℝ) + 24 / 1000000 := by
  apply barrierCase2Y_le_of_bracket_bounds
    ((-160890 / 100000 : ℝ) + 24 / 1000000) _ x hx
  intro m hm y hy
  have hp := barrierCase2Y_bracket_left_lt m hm
  have hh := barrierCase2Y_bracket_height m hm hy
  linarith

end InternalCatalan

end

end OAI

end

section
open OAI.InternalCatalan

theorem solution {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    barrierCase2Y x ≤ (-160890 / 100000 : ℝ) + 24 / 1000000 := by
  first
  | exact @OAI.InternalCatalan.barrierCase2Y_global_upper
  | (apply OAI.InternalCatalan.barrierCase2Y_global_upper <;> assumption)

end
