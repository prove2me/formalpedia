-- Prove2me | solution 1 for OAI.InternalCatalan.barrierCase2X_table_left_lt_A1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T20:57:24.038345+00:00
-- url     : https://prove2.me/submissions/b76e3577-08a2-4f93-98ec-06ab5f9bc0af

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
-- module Solutions.OAICatalan.Catalan.Analysis.RealEnergyLogSeries
namespace OAI

noncomputable section
open Set

namespace InternalCatalan


theorem energy_hasSum_re_power_div {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => (z ^ k).re / (k : ℝ))
      (-Real.log ‖1 - z‖) := by
  simpa only [Complex.div_natCast_re, Complex.neg_re, Complex.log_re] using
    Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hz)




theorem energy_hasSum_real_power_div {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => u ^ k / (k : ℝ)) (-Real.log (1 - u)) := by
  have huNorm : ‖(u : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_lt.mpr hu
  have hnorm : ‖(1 : ℂ) - (u : ℂ)‖ = 1 - u := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hu.2)]
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re, hnorm] using
    energy_hasSum_re_power_div huNorm






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
-- module Solutions.OAICatalan.Catalan.Energy.BarrierAtanArgument
namespace OAI

noncomputable section

namespace InternalCatalan

section

open scoped BigOperators

def barrierAtanJ (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 24, (-1 : ℝ) ^ j * t ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ)

def barrierAtanJ0 : ℝ := (1 / 2 : ℝ) ^ 49 / 49

def barrierArgApprox (k : ℤ) (t : ℝ) : ℝ :=
  (k : ℝ) * (barrierAtanJ (1 / 2) + barrierAtanJ (1 / 3)) + barrierAtanJ t

end

section

theorem barrier_atan_half_add_third :
    Real.arctan (1 / 2 : ℝ) + Real.arctan (1 / 3 : ℝ) = Real.pi / 4 := by
  simpa only [one_div] using Real.arctan_inv_2_add_arctan_inv_3

open Filter
open scoped BigOperators Topology

private theorem barrierAtanJ_neg (t : ℝ) : barrierAtanJ (-t) = -barrierAtanJ t := by
  unfold barrierAtanJ
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [(odd_two_mul_add_one j).neg_pow t]
  ring

private theorem barrierAtanJ_remainder_nonneg (t : ℝ)
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    |Real.arctan t - barrierAtanJ t| ≤ t ^ 49 / 49 := by
  let f : ℕ → ℝ := fun j => t ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ)
  have ht1 : t ≤ 1 := by linarith
  have hf : Antitone f := by
    intro i j hij
    dsimp only [f]
    exact div_le_div₀ (pow_nonneg ht0 _)
      (pow_le_pow_of_le_one ht0 ht1 (by omega)) (by positivity)
      (by exact_mod_cast (show 2 * i + 1 ≤ 2 * j + 1 by omega))
  have hnorm : ‖t‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg ht0]
    linarith
  have hseries := Real.hasSum_arctan hnorm
  have hconv : Tendsto
      (fun n => ∑ j ∈ Finset.range n, (-1 : ℝ) ^ j * f j)
      atTop (𝓝 (Real.arctan t)) := by
    simpa only [f, mul_div_assoc] using hseries.tendsto_sum_nat
  have hpartial : (∑ j ∈ Finset.range 24, (-1 : ℝ) ^ j * f j) =
      barrierAtanJ t := by
    simp only [barrierAtanJ, f, mul_div_assoc]
  have hlast : (-1 : ℝ) ^ 24 * f 24 = t ^ 49 / 49 := by
    norm_num [f]
  have hlo : barrierAtanJ t ≤ Real.arctan t := by
    have h := Antitone.alternating_series_le_tendsto hconv hf 12
    change (∑ j ∈ Finset.range 24, (-1 : ℝ) ^ j * f j) ≤ Real.arctan t at h
    rwa [hpartial] at h
  have hhi : Real.arctan t ≤ barrierAtanJ t + t ^ 49 / 49 := by
    have h := Antitone.tendsto_le_alternating_series hconv hf 12
    change Real.arctan t ≤
      ∑ j ∈ Finset.range (24 + 1), (-1 : ℝ) ^ j * f j at h
    rwa [Finset.sum_range_succ, hpartial, hlast] at h
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith

theorem barrierAtanJ_remainder (t : ℝ) (ht : |t| ≤ 1 / 2) :
    |Real.arctan t - barrierAtanJ t| ≤ |t| ^ 49 / 49 := by
  by_cases ht0 : 0 ≤ t
  · have ht' : t ≤ 1 / 2 := by simpa only [abs_of_nonneg ht0] using ht
    simpa only [abs_of_nonneg ht0] using barrierAtanJ_remainder_nonneg t ht0 ht'
  · have htneg : t < 0 := lt_of_not_ge ht0
    have hnt0 : 0 ≤ -t := by linarith
    have hnt : -t ≤ 1 / 2 := by simpa only [abs_of_neg htneg] using ht
    have h := barrierAtanJ_remainder_nonneg (-t) hnt0 hnt
    have heq : Real.arctan (-t) - barrierAtanJ (-t) =
        -(Real.arctan t - barrierAtanJ t) := by
      rw [Real.arctan_neg, barrierAtanJ_neg]
      ring
    rw [heq, abs_neg] at h
    simpa only [abs_of_neg htneg] using h

end

theorem barrierAtanJ_remainder_uniform (t : ℝ) (ht : |t| ≤ 1 / 2) :
    |Real.arctan t - barrierAtanJ t| ≤ barrierAtanJ0 := by
  exact (barrierAtanJ_remainder t ht).trans
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg t) ht 49) (by norm_num))

theorem barrierAtanJ_octant_error :
    |Real.pi / 4 - (barrierAtanJ (1 / 2) + barrierAtanJ (1 / 3))| ≤
      2 * barrierAtanJ0 := by
  have hhalf := barrierAtanJ_remainder_uniform (1 / 2) (by norm_num)
  have hthird := barrierAtanJ_remainder_uniform (1 / 3) (by norm_num)
  rw [← barrier_atan_half_add_third]
  calc
    _ = |(Real.arctan (1 / 2) - barrierAtanJ (1 / 2)) +
          (Real.arctan (1 / 3) - barrierAtanJ (1 / 3))| := by congr 1; ring
    _ ≤ |Real.arctan (1 / 2) - barrierAtanJ (1 / 2)| +
          |Real.arctan (1 / 3) - barrierAtanJ (1 / 3)| := by
      simpa only [Real.norm_eq_abs] using norm_add_le
        (Real.arctan (1 / 2) - barrierAtanJ (1 / 2))
        (Real.arctan (1 / 3) - barrierAtanJ (1 / 3))
    _ ≤ 2 * barrierAtanJ0 := by linarith

theorem barrierArgApprox_error_general (k : ℤ) (t : ℝ) (ht : |t| ≤ 1 / 2) :
    |((k : ℝ) * (Real.pi / 4) + Real.arctan t) - barrierArgApprox k t| ≤
      (2 * |(k : ℝ)| + 1) * barrierAtanJ0 := by
  have hangle := barrierAtanJ_octant_error
  have htaylor := barrierAtanJ_remainder_uniform t ht
  unfold barrierArgApprox
  calc
    _ = |(k : ℝ) * (Real.pi / 4 - (barrierAtanJ (1 / 2) + barrierAtanJ (1 / 3))) +
          (Real.arctan t - barrierAtanJ t)| := by congr 1; ring
    _ ≤ |(k : ℝ) * (Real.pi / 4 - (barrierAtanJ (1 / 2) + barrierAtanJ (1 / 3)))| +
          |Real.arctan t - barrierAtanJ t| := by
      simpa only [Real.norm_eq_abs] using norm_add_le
        ((k : ℝ) * (Real.pi / 4 - (barrierAtanJ (1 / 2) + barrierAtanJ (1 / 3))))
        (Real.arctan t - barrierAtanJ t)
    _ = |(k : ℝ)| * |Real.pi / 4 - (barrierAtanJ (1 / 2) + barrierAtanJ (1 / 3))| +
          |Real.arctan t - barrierAtanJ t| := by rw [abs_mul]
    _ ≤ |(k : ℝ)| * (2 * barrierAtanJ0) + barrierAtanJ0 :=
      add_le_add (mul_le_mul_of_nonneg_left hangle (abs_nonneg _)) htaylor
    _ = (2 * |(k : ℝ)| + 1) * barrierAtanJ0 := by ring

theorem barrierArgApprox_error (k : ℤ) (t : ℝ) (hk : |k| ≤ 4) (ht : |t| ≤ 1 / 2) :
    |((k : ℝ) * (Real.pi / 4) + Real.arctan t) - barrierArgApprox k t| ≤
      9 * barrierAtanJ0 := by
  have hkR : |(k : ℝ)| ≤ 4 := by exact_mod_cast hk
  have hj0 : 0 ≤ barrierAtanJ0 := by unfold barrierAtanJ0; positivity
  exact (barrierArgApprox_error_general k t ht).trans
    (mul_le_mul_of_nonneg_right (by linarith) hj0)

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierTailPairRational
namespace OAI

noncomputable section

namespace InternalCatalan




















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



































open Polynomial
















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









open Polynomial Filter
open scoped BigOperators










end

section

open scoped BigOperators





end
section

open Polynomial
open scoped BigOperators

theorem barrierTrialT_nil_eq_sum (cs : List ℤ) (x : ℝ) :
    barrierTrialT (barrierTrial cs []) x =
      ∑ k ∈ Finset.range cs.length,
        ((cs.getD k 0 : ℝ) / 100000000) *
          (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ) := by
  unfold barrierTrialT
  have heq (k : ℕ) : barrierTrial cs [] (k + 1) =
      (cs.getD k 0 : ℝ) / 100000000 := by
    simp [barrierTrial, barrierFiniteCoeff]
  simp_rw [heq]
  apply tsum_eq_sum
  intro k hk
  have hlen : cs.length ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
  rw [List.getD_eq_default cs 0 hlen]
  norm_num

theorem barrierTrialS_nil_eq_sum (cs : List ℤ) (x : ℝ) :
    barrierTrialS (barrierTrial cs []) x =
      ∑ k ∈ Finset.range cs.length,
        ((cs.getD k 0 : ℝ) / 100000000) * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  unfold barrierTrialS
  have heq (k : ℕ) : barrierTrial cs [] (k + 1) =
      (cs.getD k 0 : ℝ) / 100000000 := by
    simp [barrierTrial, barrierFiniteCoeff]
  simp_rw [heq]
  apply tsum_eq_sum
  intro k hk
  have hlen : cs.length ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
  rw [List.getD_eq_default cs 0 hlen]
  norm_num

end

section

open Polynomial Set Filter
open scoped BigOperators



end

open Polynomial







open Polynomial
open scoped BigOperators

def barrierFiniteTRat (cs : List ℤ) (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℚ) / 100000000) *
    (Chebyshev.T ℚ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℚ)

def barrierFiniteSRat (cs : List ℤ) (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range cs.length,
    ((cs.getD k 0 : ℚ) / 100000000) * x ^ (k + 1) / ((k + 1 : ℕ) : ℚ)

theorem barrierTrialT_nil_eval_rat (cs : List ℤ) (x : ℚ) :
    barrierTrialT (barrierTrial cs []) (x : ℝ) = ((barrierFiniteTRat cs x : ℚ) : ℝ) := by
  have heval (n : ℤ) : (Chebyshev.T ℝ n).eval (x : ℝ) =
      (((Chebyshev.T ℚ n).eval x : ℚ) : ℝ) := by
    rw [← Chebyshev.map_T (Rat.castHom ℝ)]
    change ((Chebyshev.T ℚ n).map (Rat.castHom ℝ)).eval ((Rat.castHom ℝ) x) =
      (Rat.castHom ℝ) ((Chebyshev.T ℚ n).eval x)
    exact Polynomial.eval_map_apply (Rat.castHom ℝ) x
  rw [barrierTrialT_nil_eq_sum]
  unfold barrierFiniteTRat
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [heval]

theorem barrierTrialS_nil_eval_rat (cs : List ℤ) (x : ℚ) :
    barrierTrialS (barrierTrial cs []) (x : ℝ) = ((barrierFiniteSRat cs x : ℚ) : ℝ) := by
  rw [barrierTrialS_nil_eq_sum]
  unfold barrierFiniteSRat
  push_cast
  rfl

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

theorem realEnergyCirclePoint_quadratic {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    realEnergyCirclePoint u ^ 2 + 1 = 2 * (u : ℂ) * realEnergyCirclePoint u := by
  calc
    _ = realEnergyCirclePoint u *
        (realEnergyCirclePoint u + conj (realEnergyCirclePoint u)) := by
      rw [mul_add, realEnergyCirclePoint_mul_conj hu, pow_two]
    _ = _ := by rw [realEnergyCirclePoint_add_conj]; ring





end

open Polynomial Set
open scoped ComplexConjugate

theorem realEnergyCirclePoint_pow_re (k : ℕ) {u : ℝ}
    (hu : u ∈ Icc (-1 : ℝ) 1) :
    (realEnergyCirclePoint u ^ k).re = (Chebyshev.T ℝ (k : ℤ)).eval u := by
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one => simp [realEnergyCirclePoint]
  | more k ih0 ih1 =>
    have hp : realEnergyCirclePoint u ^ (k + 2) + realEnergyCirclePoint u ^ k =
        2 * (u : ℂ) * realEnergyCirclePoint u ^ (k + 1) := by
      calc
        _ = realEnergyCirclePoint u ^ k * (realEnergyCirclePoint u ^ 2 + 1) := by
          rw [pow_add]
          ring
        _ = _ := by
          rw [realEnergyCirclePoint_quadratic hu, pow_succ]
          ring
    have hr := congrArg Complex.re hp
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, mul_zero, sub_zero, add_zero] at hr
    have hi1 : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := by omega
    rw [Nat.cast_add, Nat.cast_ofNat, Chebyshev.T_add_two]
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X]
    rw [hi1, ← ih1, ← ih0]
    linarith



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierChebyshevLogFormula
namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial Set
open scoped ComplexConjugate

theorem barrier_log_mul_of_re_pos {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    Complex.log (a * b) = Complex.log a + Complex.log b := by
  have ha0 : a ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp only [Complex.zero_re] at hr
    linarith
  have hb0 : b ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp only [Complex.zero_re] at hr
    linarith
  have hargA := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha))
  have hargB := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb))
  exact Complex.log_mul ha0 hb0
    ⟨by linarith [hargA.1, hargB.1], by linarith [hargA.2, hargB.2]⟩

theorem barrier_chebyshev_quadratic_log {x : ℝ} {z : ℂ}
    (hx : |x| ≤ 1) (hz : ‖z‖ < 1) :
    Complex.log (1 - 2 * (x : ℂ) * z + z ^ 2) =
      Complex.log (1 - z * realEnergyCirclePoint x) +
        Complex.log (1 - z * conj (realEnergyCirclePoint x)) := by
  have hx' : x ∈ Icc (-1 : ℝ) 1 := abs_le.mp hx
  have hnormA : ‖z * realEnergyCirclePoint x‖ < 1 := by
    simpa only [Complex.norm_mul, realEnergyCirclePoint_norm hx', mul_one] using hz
  have hnormB : ‖z * conj (realEnergyCirclePoint x)‖ < 1 := by
    simpa only [Complex.norm_mul, Complex.norm_conj,
      realEnergyCirclePoint_norm hx', mul_one] using hz
  have hreA : 0 < (1 - z * realEnergyCirclePoint x).re := by
    have hh := (Complex.re_le_norm (z * realEnergyCirclePoint x)).trans_lt hnormA
    simpa only [Complex.sub_re, Complex.one_re] using sub_pos.mpr hh
  have hreB : 0 < (1 - z * conj (realEnergyCirclePoint x)).re := by
    have hh := (Complex.re_le_norm (z * conj (realEnergyCirclePoint x))).trans_lt hnormB
    simpa only [Complex.sub_re, Complex.one_re] using sub_pos.mpr hh
  have hfactor :
      (1 - z * realEnergyCirclePoint x) * (1 - z * conj (realEnergyCirclePoint x)) =
        1 - 2 * (x : ℂ) * z + z ^ 2 := by
    calc
      _ = 1 - z * (realEnergyCirclePoint x + conj (realEnergyCirclePoint x)) +
          z ^ 2 * (realEnergyCirclePoint x * conj (realEnergyCirclePoint x)) := by ring
      _ = _ := by
        rw [realEnergyCirclePoint_add_conj, realEnergyCirclePoint_mul_conj hx']
        ring
  rw [← hfactor]
  exact barrier_log_mul_of_re_pos hreA hreB

private theorem circle_power_add_conj (k : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    realEnergyCirclePoint x ^ k + conj (realEnergyCirclePoint x) ^ k =
      2 * Complex.ofReal ((Chebyshev.T ℝ (k : ℤ)).eval x) := by
  rw [← map_pow]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.conj_re, Complex.mul_re,
      Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    rw [realEnergyCirclePoint_pow_re k (abs_le.mp hx)]
    ring
  · simp only [Complex.add_im, Complex.conj_im, Complex.mul_im,
      Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_mul, add_zero]
    ring

theorem barrier_hasSum_chebyshev_log {x : ℝ} {z : ℂ}
    (hx : |x| ≤ 1) (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => z ^ (k + 1) *
      Complex.ofReal ((Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x) / ((k + 1 : ℕ) : ℂ))
      (-(1 / 2 : ℂ) * Complex.log (1 - 2 * (x : ℂ) * z + z ^ 2)) := by
  have hx' : x ∈ Icc (-1 : ℝ) 1 := abs_le.mp hx
  have hnormA : ‖z * realEnergyCirclePoint x‖ < 1 := by
    simpa only [Complex.norm_mul, realEnergyCirclePoint_norm hx', mul_one] using hz
  have hnormB : ‖z * conj (realEnergyCirclePoint x)‖ < 1 := by
    simpa only [Complex.norm_mul, Complex.norm_conj,
      realEnergyCirclePoint_norm hx', mul_one] using hz
  have hA := Complex.hasSum_taylorSeries_neg_log' hnormA
  have hB := Complex.hasSum_taylorSeries_neg_log' hnormB
  convert (hA.add hB).mul_left (1 / 2 : ℂ) using 1
  · rfl
  · funext k
    calc
      _ = (1 / 2 : ℂ) * (z ^ (k + 1) *
          (realEnergyCirclePoint x ^ (k + 1) +
            conj (realEnergyCirclePoint x) ^ (k + 1)) / ((k + 1 : ℕ) : ℂ)) := by
        rw [circle_power_add_conj (k + 1) hx]
        ring
      _ = _ := by
        simp only [mul_pow, Nat.cast_add, Nat.cast_one]
        ring
  · rw [barrier_chebyshev_quadratic_log hx hz]
    ring


end

open Polynomial
open scoped BigOperators

private theorem barrierFiniteCoeff_T_hasSum (cs : List ℤ) (x : ℝ) :
    HasSum (fun k : ℕ => barrierFiniteCoeff cs (k + 1) *
      (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ))
      (∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) *
        (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ)) := by
  have hs : HasSum
      (fun k : ℕ => ((cs.getD k 0 : ℝ) / 100000000) *
        (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ))
      (∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) *
        (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    have hlen : cs.length ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    rw [List.getD_eq_default cs 0 hlen]
    norm_num
  simpa [barrierFiniteCoeff] using hs

theorem barrierTailRow_T_hasSum (z r : ℂ) (hz : ‖z‖ < 1)
    {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ => (r * z ^ (k + 1)).re *
      (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ))
      (-(r * Complex.log (1 - 2 * (x : ℂ) * z + z ^ 2)).re / 2) := by
  have hc : HasSum (fun k : ℕ => (r * z ^ (k + 1)) *
      (((Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x : ℝ) : ℂ) / ((k + 1 : ℕ) : ℂ))
      (-(r * Complex.log (1 - 2 * (x : ℂ) * z + z ^ 2)) / 2) := by
    convert (barrier_hasSum_chebyshev_log hx hz).mul_left r using 1
    · rfl
    · funext k
      ring
    · ring
  simpa only [Complex.div_natCast_re, Complex.div_ofNat_re, Complex.neg_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
    Complex.hasSum_re hc

theorem barrierTail_T_hasSum (tail : List (ℂ × ℂ))
    (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1) {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ =>
      (tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ (k + 1))).sum.re *
        (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ))
      (-(tail.map (fun zr : ℂ × ℂ =>
        zr.2 * Complex.log (1 - 2 * (x : ℂ) * zr.1 + zr.1 ^ 2))).sum.re / 2) := by
  revert htail
  induction tail with
  | nil =>
      intro _
      simp
  | cons zr tail ih =>
      intro htail
      have hr := barrierTailRow_T_hasSum zr.1 zr.2 (htail zr List.mem_cons_self) hx
      have ht := ih (fun w hw => htail w (List.mem_cons_of_mem _ hw))
      simpa only [List.map_cons, List.sum_cons, Complex.add_re, add_mul, add_div,
        neg_add] using hr.add ht

theorem barrierTrialT_eq_finite_log (cs : List ℤ) (tail : List (ℂ × ℂ))
    (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1) {x : ℝ} (hx : |x| ≤ 1) :
    barrierTrialT (barrierTrial cs tail) x =
      (∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) *
        (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ)) -
      (tail.map (fun zr : ℂ × ℂ =>
        zr.2 * Complex.log (1 - 2 * (x : ℂ) * zr.1 + zr.1 ^ 2))).sum.re / 2 := by
  have hh := (barrierFiniteCoeff_T_hasSum cs x).add (barrierTail_T_hasSum tail htail hx)
  have hs : HasSum (fun k : ℕ => barrierTrial cs tail (k + 1) *
      (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ))
      ((∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) *
        (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ)) -
        (tail.map (fun zr : ℂ × ℂ =>
          zr.2 * Complex.log (1 - 2 * (x : ℂ) * zr.1 + zr.1 ^ 2))).sum.re / 2) := by
    simpa [barrierTrial, add_mul, add_div, sub_eq_add_neg, neg_div] using hh
  exact hs.tsum_eq

theorem barrierP2_T_eq_finite_log {x : ℝ} (hx : |x| ≤ 1) :
    barrierTrialT barrierP2 x =
      (∑ k ∈ Finset.range barrierP2Finite.length,
        ((barrierP2Finite.getD k 0 : ℝ) / 100000000) *
          (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ)) -
      (barrierP2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * Complex.log (1 - 2 * (x : ℂ) * zr.1 + zr.1 ^ 2))).sum.re / 2 := by
  apply barrierTrialT_eq_finite_log barrierP2Finite barrierP2Tail _ hx
  intro zr hzr
  exact lt_of_le_of_lt (barrierP2_tail_norm_bounds zr hzr).1 (by norm_num)


end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierComplexOctantRange
namespace OAI

noncomputable section

namespace InternalCatalan

section

theorem barrierComplex_norm_sq (z : ℂ) :
    z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring


theorem barrierComplexLog_re (z : ℂ) :
    (Complex.log z).re = Real.log (z.re ^ 2 + z.im ^ 2) / 2 := by
  rw [Complex.log_re, barrierComplex_norm_sq, Real.log_pow]
  norm_num


theorem barrierComplexArg_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    Complex.arg z = Real.arctan (z.im / z.re) := by
  have hb := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  rw [← Complex.tan_arg z]
  exact (Real.arctan_tan hb.1 hb.2).symm

theorem barrierComplexArg_one_add_I :
    Complex.arg (1 + Complex.I) = Real.pi / 4 := by
  rw [barrierComplexArg_of_re_pos (by norm_num)]
  norm_num [Real.arctan_one]

theorem barrierComplexArg_one_sub_I :
    Complex.arg (1 - Complex.I) = -(Real.pi / 4) := by
  rw [barrierComplexArg_of_re_pos (by norm_num)]
  norm_num [Real.arctan_neg, Real.arctan_one]

end

section

open scoped ComplexConjugate

theorem barrierComplexLog_conj {z : ℂ} (hz : z.im ≠ 0 ∨ 0 < z.re) :
    Complex.log (conj z) = conj (Complex.log z) := by
  apply Complex.log_conj z
  intro harg
  have h := Complex.arg_eq_pi_iff.mp harg
  rcases hz with him | hre
  · exact him h.2
  · exact (not_lt_of_ge hre.le) h.1

theorem barrierComplexLog_conj_weighted_re (c z : ℂ)
    (hz : z.im ≠ 0 ∨ 0 < z.re) :
    (conj c * Complex.log (conj z)).re = (c * Complex.log z).re := by
  rw [barrierComplexLog_conj hz, ← map_mul, Complex.conj_re]



theorem barrierComplexLog_linear_conj (x : ℝ) (z : ℂ) :
    1 - (x : ℂ) * conj z = conj (1 - (x : ℂ) * z) := by
  simp

theorem barrierComplexLog_quadratic_conj (x : ℝ) (z : ℂ) :
    1 - 2 * (x : ℂ) * conj z + (conj z) ^ 2 =
      conj (1 - 2 * (x : ℂ) * z + z ^ 2) := by
  simp [map_ofNat]

end

def barrierOctantMultiplier (k : ℤ) : ℂ :=
  if 0 ≤ k then (1 - Complex.I) ^ k.toNat
  else (1 + Complex.I) ^ (-k).toNat

def barrierOctantRotate (k : ℤ) (z : ℂ) : ℂ :=
  barrierOctantMultiplier k * z

/-- Port note (prove2.me): newer Lean simplifies `Int.toNat` of a numeral; Lean 4.33.1 needs
this lemma in the `norm_num` calls that unfold `barrierOctantMultiplier`. -/
theorem portInt_toNat_ofNat (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n : ℤ)).toNat = OfNat.ofNat n := Int.toNat_natCast n



theorem barrierOctantMultiplier_ne_zero (k : ℤ) :
    barrierOctantMultiplier k ≠ 0 := by
  have hm : (1 - Complex.I : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hp : (1 + Complex.I : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  unfold barrierOctantMultiplier
  split <;> exact pow_ne_zero _ (by assumption)

private theorem arg_pow_angle_of_arg (u : ℂ) (a : ℝ)
    (ha : Complex.arg u = a) (m : ℕ) :
    (Complex.arg (u ^ m) : Real.Angle) = (((m : ℝ) * a : ℝ) : Real.Angle) := by
  rw [Complex.arg_pow_coe_angle, ha, ← Real.Angle.coe_nsmul]
  simp only [nsmul_eq_mul]

theorem barrierOctantMultiplier_arg (k : ℤ) :
    (Complex.arg (barrierOctantMultiplier k) : Real.Angle) =
      ((-((k : ℝ) * (Real.pi / 4)) : ℝ) : Real.Angle) := by
  unfold barrierOctantMultiplier
  split_ifs with hk
  · rw [arg_pow_angle_of_arg _ _ barrierComplexArg_one_sub_I]
    have hc : (k.toNat : ℝ) = (k : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hk
    rw [hc]
    congr 1
    ring
  · rw [arg_pow_angle_of_arg _ _ barrierComplexArg_one_add_I]
    have hneg : 0 ≤ -k := neg_nonneg.mpr (le_of_not_ge hk)
    have hc : ((-k).toNat : ℝ) = -(k : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hneg
    rw [hc]
    congr 1
    ring

theorem barrierComplexArg_octant (k : ℤ) (z : ℂ)
    (hre : 0 < (barrierOctantRotate k z).re)
    (hrange : (k : ℝ) * (Real.pi / 4) +
        Real.arctan ((barrierOctantRotate k z).im / (barrierOctantRotate k z).re)
      ∈ Set.Ioc (-Real.pi) Real.pi) :
    Complex.arg z = (k : ℝ) * (Real.pi / 4) +
      Real.arctan ((barrierOctantRotate k z).im / (barrierOctantRotate k z).re) := by
  have hz : z ≠ 0 := by
    intro hz
    simp [barrierOctantRotate, hz] at hre
  have hpos := barrierComplexArg_of_re_pos hre
  have hmod : (Complex.arg z : Real.Angle) =
      (((k : ℝ) * (Real.pi / 4) +
        Real.arctan ((barrierOctantRotate k z).im / (barrierOctantRotate k z).re)
        : ℝ) : Real.Angle) := by
    calc
      (Complex.arg z : Real.Angle) =
          (((k : ℝ) * (Real.pi / 4) : ℝ) : Real.Angle) +
            (Complex.arg (barrierOctantRotate k z) : Real.Angle) := by
        rw [barrierOctantRotate,
          Complex.arg_mul_coe_angle (barrierOctantMultiplier_ne_zero k) hz,
          barrierOctantMultiplier_arg, Real.Angle.coe_neg]
        abel
      _ = _ := by rw [hpos, Real.Angle.coe_add]
  calc
    Complex.arg z = (((k : ℝ) * (Real.pi / 4) +
        Real.arctan ((barrierOctantRotate k z).im / (barrierOctantRotate k z).re)
        : ℝ) : Real.Angle).toReal :=
      Complex.arg_coe_angle_eq_iff_eq_toReal.mp hmod
    _ = _ := Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr hrange

theorem barrierComplexArg_octant_of_eq (k : ℤ) (z : ℂ) (r s t : ℝ)
    (hrot : barrierOctantRotate k z = ⟨r, s⟩) (hr : 0 < r)
    (ht : t = s / r)
    (hrange : (k : ℝ) * (Real.pi / 4) + Real.arctan t
      ∈ Set.Ioc (-Real.pi) Real.pi) :
    Complex.arg z = (k : ℝ) * (Real.pi / 4) + Real.arctan t := by
  have hre : 0 < (barrierOctantRotate k z).re := by simpa only [hrot] using hr
  have hratio : (barrierOctantRotate k z).im / (barrierOctantRotate k z).re = t := by
    simpa only [hrot] using ht.symm
  simpa only [hratio] using barrierComplexArg_octant k z hre (by simpa only [hratio] using hrange)

theorem barrierOctant_principal_range (k : ℤ) (t : ℝ)
    (hk : |k| ≤ 4) (ht : |t| ≤ 1 / 2)
    (hpos : k = 4 → t ≤ 0) (hneg : k = -4 → 0 < t) :
    (k : ℝ) * (Real.pi / 4) + Real.arctan t ∈ Set.Ioc (-Real.pi) Real.pi := by
  have htlo : -(Real.pi / 4) < Real.arctan t := by
    have h : Real.arctan (-1) < Real.arctan t :=
      Real.arctan_lt_arctan_iff.mpr (by have := (abs_le.mp ht).1; linarith)
    simpa only [Real.arctan_neg, Real.arctan_one] using h
  have hthi : Real.arctan t < Real.pi / 4 := by
    have h : Real.arctan t < Real.arctan 1 :=
      Real.arctan_lt_arctan_iff.mpr (by have := (abs_le.mp ht).2; linarith)
    simpa only [Real.arctan_one] using h
  have hpi : 0 ≤ Real.pi / 4 := by positivity
  have hkbound := abs_le.mp hk
  constructor
  · by_cases he : k = -4
    · have hp := Real.arctan_pos.mpr (hneg he)
      rw [he]
      norm_num
      linarith
    · have hlo : (-3 : ℤ) ≤ k := by omega
      have hloR : (-3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hlo
      have hm := mul_le_mul_of_nonneg_right hloR hpi
      linarith
  · by_cases he : k = 4
    · have hp := Real.arctan_le_zero.mpr (hpos he)
      rw [he]
      norm_num
      linarith
    · have hhi : k ≤ (3 : ℤ) := by omega
      have hhiR : (k : ℝ) ≤ (3 : ℝ) := by exact_mod_cast hhi
      have hm := mul_le_mul_of_nonneg_right hhiR hpi
      linarith

theorem barrierComplexArg_octant_rational (k : ℤ) (z : ℂ) (r s : ℝ)
    (hrot : barrierOctantRotate k z = ⟨r, s⟩)
    (hr : 0 < r) (hs : |s| ≤ r / 2) (hk : |k| ≤ 4)
    (hpos : k = 4 → s ≤ 0) (hneg : k = -4 → 0 < s) :
    Complex.arg z = (k : ℝ) * (Real.pi / 4) + Real.arctan (s / r) := by
  have ht : |s / r| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hr, div_le_iff₀ hr]
    linarith
  exact barrierComplexArg_octant_of_eq k z r s (s / r) hrot hr rfl
    (barrierOctant_principal_range k (s / r) hk ht
      (fun he => div_nonpos_of_nonpos_of_nonneg (hpos he) hr.le)
      (fun he => div_pos (hneg he) hr))

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.FirstBarrier.BarrierCaseOnePointLogInputs
namespace OAI

noncomputable section
namespace InternalCatalan.Case1PointData

def FixedLogNormalization (s : ℝ) (m : ℤ) (y : ℚ) : Prop :=
  s = (2 : ℝ) ^ m * (y : ℝ) ∧
    (y : ℝ) ∈ Set.Icc (1 : ℝ) 2 ∧ |(m : ℝ)| ≤ 100








































end InternalCatalan.Case1PointData

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierLogRatConstants
namespace OAI

noncomputable section

namespace InternalCatalan

section

open scoped BigOperators

def barrierLogH (y : ℝ) : ℝ :=
  2 * ∑ j ∈ Finset.range 18,
    ((y - 1) / (y + 1)) ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ)

theorem barrier_hasSum_odd_log {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun k : ℕ => 2 * q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ))
      (Real.log (1 + q) - Real.log (1 - q)) := by
  let f : ℕ → ℝ := fun k => q ^ k / (k : ℝ) - (-q) ^ k / (k : ℝ)
  have hq : q ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hq1⟩
  have hnq : -q ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hbase : HasSum f (Real.log (1 + q) - Real.log (1 - q)) := by
    convert (energy_hasSum_real_power_div hq).sub
      (energy_hasSum_real_power_div hnq) using 1
    all_goals first
      | rfl
      | (simp only [sub_neg_eq_add]
         ring)
  have heven (k : ℕ) : f (2 * k) = 0 := by
    simp [f, pow_mul]
  have hodd (k : ℕ) : f (2 * k + 1) =
      2 * q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ) := by
    simp only [f, pow_add, pow_mul, pow_one, neg_sq]
    ring
  have hi : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro i j hij
    change 2 * i + 1 = 2 * j + 1 at hij
    omega
  have hs : Summable
      (fun k : ℕ => 2 * q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)) := by
    have hcomp := hbase.summable.comp_injective hi
    change Summable (fun k : ℕ => f (2 * k + 1)) at hcomp
    simpa only [hodd] using hcomp
  have he : HasSum (fun k => f (2 * k)) 0 := by
    simpa only [heven] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  have ho : HasSum (fun k => f (2 * k + 1))
      (∑' k : ℕ, 2 * q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)) := by
    simpa only [hodd] using hs.hasSum
  have heq : (∑' k : ℕ, 2 * q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)) =
      Real.log (1 + q) - Real.log (1 - q) := by
    simpa only [zero_add] using (he.even_add_odd ho).unique hbase
  rw [← heq]
  exact hs.hasSum

theorem barrier_hasSum_scaled_log {y : ℝ} (hy : 1 ≤ y) :
    HasSum (fun k : ℕ => 2 * ((y - 1) / (y + 1)) ^ (2 * k + 1) /
      ((2 * k + 1 : ℕ) : ℝ)) (Real.log y) := by
  let q := (y - 1) / (y + 1)
  have hd : 0 < y + 1 := by linarith
  have hq0 : 0 ≤ q := div_nonneg (sub_nonneg.mpr hy) hd.le
  have hq1 : q < 1 := (div_lt_one hd).2 (by linarith)
  have hp : 1 + q ≠ 0 := ne_of_gt (by linarith)
  have hn : 1 - q ≠ 0 := ne_of_gt (by linarith)
  have heq : (1 + q) / (1 - q) = y := by
    apply (div_eq_iff hn).2
    dsimp [q]
    field_simp [ne_of_gt hd]
    ring
  have hlog : Real.log (1 + q) - Real.log (1 - q) = Real.log y := by
    rw [← Real.log_div hp hn, heq]
  simpa only [hlog] using barrier_hasSum_odd_log hq0 hq1

private theorem barrier_odd_log_shift_le_geometric {q : ℝ} (hq0 : 0 ≤ q)
    (m k : ℕ) :
    2 * q ^ (2 * (k + m) + 1) / ((2 * (k + m) + 1 : ℕ) : ℝ) ≤
      (2 * q ^ (2 * m + 1) / ((2 * m + 1 : ℕ) : ℝ)) * (q ^ 2) ^ k := by
  have hden0 : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  have hden : ((2 * m + 1 : ℕ) : ℝ) ≤ ((2 * (k + m) + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.le_add_left m k)) 1
  have hnum : 0 ≤ 2 * q ^ (2 * (k + m) + 1) :=
    mul_nonneg (by norm_num) (pow_nonneg hq0 _)
  have hexp : 2 * (k + m) + 1 = (2 * m + 1) + 2 * k := by ring
  calc
    _ ≤ 2 * q ^ (2 * (k + m) + 1) / ((2 * m + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left hnum hden0 hden
    _ = (2 * q ^ (2 * m + 1) / ((2 * m + 1 : ℕ) : ℝ)) * (q ^ 2) ^ k := by
      rw [hexp, pow_add, pow_mul]
      ring

theorem barrier_odd_log_remainder_bounds {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (m : ℕ) :
    0 ≤ (Real.log (1 + q) - Real.log (1 - q)) -
        ∑ k ∈ Finset.range m, 2 * q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ) ∧
      (Real.log (1 + q) - Real.log (1 - q)) -
          (∑ k ∈ Finset.range m, 2 * q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)) ≤
        2 * q ^ (2 * m + 1) / (((2 * m + 1 : ℕ) : ℝ) * (1 - q ^ 2)) := by
  have hseries := barrier_hasSum_odd_log hq0 hq1
  have htail : HasSum
      (fun k : ℕ => 2 * q ^ (2 * (k + m) + 1) / ((2 * (k + m) + 1 : ℕ) : ℝ))
      ((Real.log (1 + q) - Real.log (1 - q)) -
        ∑ k ∈ Finset.range m, 2 * q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)) := by
    exact (hasSum_nat_add_iff'
      (f := fun k : ℕ => 2 * q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)) m).2 hseries
  have hq2 : q ^ 2 < 1 := by
    simpa only [pow_two, one_mul] using mul_self_lt_mul_self hq0 hq1
  have hq2abs : |q ^ 2| < 1 := by
    simpa only [abs_of_nonneg (sq_nonneg q)] using hq2
  have hgeom := (hasSum_geometric_of_abs_lt_one hq2abs).mul_left
    (2 * q ^ (2 * m + 1) / ((2 * m + 1 : ℕ) : ℝ))
  have hupper := hasSum_le (fun k => barrier_odd_log_shift_le_geometric hq0 m k)
    htail hgeom
  constructor
  · exact hasSum_le (fun k => by positivity) hasSum_zero htail
  · calc
      _ ≤ (2 * q ^ (2 * m + 1) / ((2 * m + 1 : ℕ) : ℝ)) * (1 - q ^ 2)⁻¹ := hupper
      _ = 2 * q ^ (2 * m + 1) / (((2 * m + 1 : ℕ) : ℝ) * (1 - q ^ 2)) := by
        rw [← div_eq_mul_inv, div_div]

theorem barrier_odd_log_remainder_bounds_eighteen {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 ≤ (Real.log (1 + q) - Real.log (1 - q)) -
        ∑ k ∈ Finset.range 18, 2 * q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ) ∧
      (Real.log (1 + q) - Real.log (1 - q)) -
          (∑ k ∈ Finset.range 18, 2 * q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)) ≤
        2 * q ^ 37 / (37 * (1 - q ^ 2)) := by
  simpa only [Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat] using
    barrier_odd_log_remainder_bounds hq0 hq1 18

def barrierLogHError : ℝ := 2 * (1 / 3 : ℝ) ^ 37 / (37 * (1 - 1 / 9))

theorem barrier_log_parameter_bounds {y : ℝ} (hy : y ∈ Set.Icc (1 : ℝ) 2) :
    0 ≤ (y - 1) / (y + 1) ∧ (y - 1) / (y + 1) ≤ 1 / 3 := by
  have hd : 0 < y + 1 := by linarith [hy.1]
  constructor
  · exact div_nonneg (sub_nonneg.mpr hy.1) hd.le
  · apply (div_le_iff₀ hd).2
    linarith [hy.2]

theorem barrier_logH_remainder {y : ℝ} (hy : y ∈ Set.Icc (1 : ℝ) 2) :
    0 ≤ Real.log y - barrierLogH y ∧
      Real.log y - barrierLogH y ≤
        2 * ((y - 1) / (y + 1)) ^ 37 /
          (37 * (1 - ((y - 1) / (y + 1)) ^ 2)) := by
  let q := (y - 1) / (y + 1)
  obtain ⟨hq0, hqthird⟩ := barrier_log_parameter_bounds hy
  have hq1 : q < 1 := lt_of_le_of_lt hqthird (by norm_num)
  have hlog : Real.log (1 + q) - Real.log (1 - q) = Real.log y :=
    (barrier_hasSum_odd_log hq0 hq1).unique (barrier_hasSum_scaled_log hy.1)
  have hsum : (∑ k ∈ Finset.range 18,
      2 * q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)) = barrierLogH y := by
    simp only [barrierLogH, Finset.mul_sum, mul_div_assoc, q]
  have h := barrier_odd_log_remainder_bounds_eighteen hq0 hq1
  rw [hlog, hsum] at h
  exact h

theorem barrier_logH_remainder_uniform {y : ℝ} (hy : y ∈ Set.Icc (1 : ℝ) 2) :
    0 ≤ Real.log y - barrierLogH y ∧
      Real.log y - barrierLogH y ≤ barrierLogHError := by
  obtain ⟨hlo, hhi⟩ := barrier_logH_remainder hy
  obtain ⟨hq0, hqthird⟩ := barrier_log_parameter_bounds hy
  let q := (y - 1) / (y + 1)
  have hpow : q ^ 37 ≤ (1 / 3 : ℝ) ^ 37 := pow_le_pow_left₀ hq0 hqthird 37
  have hsq : q ^ 2 ≤ (1 / 9 : ℝ) := by
    have h := pow_le_pow_left₀ hq0 hqthird 2
    norm_num at h
    exact h
  have hd : (0 : ℝ) < 37 * (1 - q ^ 2) := by linarith
  refine ⟨hlo, hhi.trans ?_⟩
  calc
    2 * q ^ 37 / (37 * (1 - q ^ 2)) ≤
        2 * (1 / 3 : ℝ) ^ 37 / (37 * (1 - q ^ 2)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) hd.le
    _ ≤ 2 * (1 / 3 : ℝ) ^ 37 / (37 * (1 - 1 / 9)) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    _ = barrierLogHError := rfl

theorem barrier_logH_error_101_lt :
    101 * barrierLogHError < (1 / 1000000000000000 : ℝ) := by
  norm_num [barrierLogHError]

end

section

def barrierScaledLogApprox (m : ℤ) (y : ℝ) : ℝ :=
  (m : ℝ) * barrierLogH 2 + barrierLogH y

theorem barrier_scaled_log_abs_error (m : ℤ) {y : ℝ}
    (hy : y ∈ Set.Icc (1 : ℝ) 2) :
    |Real.log ((2 : ℝ) ^ m * y) - barrierScaledLogApprox m y| ≤
      (|(m : ℝ)| + 1) * barrierLogHError := by
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num) hy.1
  have h2 := barrier_logH_remainder_uniform (y := 2) ⟨by norm_num, le_rfl⟩
  have he := barrier_logH_remainder_uniform hy
  rw [Real.log_mul (zpow_ne_zero m (by norm_num)) (ne_of_gt hypos), Real.log_zpow]
  unfold barrierScaledLogApprox
  calc
    |(m : ℝ) * Real.log 2 + Real.log y - ((m : ℝ) * barrierLogH 2 + barrierLogH y)| =
        |(m : ℝ) * (Real.log 2 - barrierLogH 2) + (Real.log y - barrierLogH y)| := by
      congr 1
      ring
    _ ≤ |(m : ℝ) * (Real.log 2 - barrierLogH 2)| + |Real.log y - barrierLogH y| := by
      simpa only [Real.norm_eq_abs] using norm_add_le
        ((m : ℝ) * (Real.log 2 - barrierLogH 2)) (Real.log y - barrierLogH y)
    _ = |(m : ℝ)| * (Real.log 2 - barrierLogH 2) + (Real.log y - barrierLogH y) := by
      rw [abs_mul, abs_of_nonneg h2.1, abs_of_nonneg he.1]
    _ ≤ |(m : ℝ)| * barrierLogHError + barrierLogHError :=
      add_le_add (mul_le_mul_of_nonneg_left h2.2 (abs_nonneg _)) he.2
    _ = (|(m : ℝ)| + 1) * barrierLogHError := by ring

theorem barrier_scaled_log_abs_error_lt (m : ℤ) {y : ℝ}
    (hy : y ∈ Set.Icc (1 : ℝ) 2) (hm : |(m : ℝ)| ≤ 100) :
    |Real.log ((2 : ℝ) ^ m * y) - barrierScaledLogApprox m y| <
      (1 / 1000000000000000 : ℝ) := by
  have he : 0 ≤ barrierLogHError := by unfold barrierLogHError; positivity
  calc
    _ ≤ (|(m : ℝ)| + 1) * barrierLogHError := barrier_scaled_log_abs_error m hy
    _ ≤ 101 * barrierLogHError := mul_le_mul_of_nonneg_right (by linarith) he
    _ < (1 / 1000000000000000 : ℝ) := barrier_logH_error_101_lt




def barrierWeightedComplexLogApprox (c : ℂ) (m k : ℤ) (y t : ℝ) : ℝ :=
  c.re * (barrierScaledLogApprox m y / 2) - c.im * barrierArgApprox k t

theorem barrierComplexLog_re_error (z : ℂ) (m : ℤ) (y : ℝ)
    (hnorm : z.re ^ 2 + z.im ^ 2 = (2 : ℝ) ^ m * y)
    (hy : y ∈ Set.Icc (1 : ℝ) 2) :
    |(Complex.log z).re - barrierScaledLogApprox m y / 2| ≤
      (|(m : ℝ)| + 1) * barrierLogHError / 2 := by
  rw [barrierComplexLog_re, hnorm, ← sub_div, abs_div]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right (barrier_scaled_log_abs_error m hy) (by norm_num)

theorem barrierComplexArg_octant_error (k : ℤ) (z : ℂ) (r s : ℝ)
    (hrot : barrierOctantRotate k z = ⟨r, s⟩)
    (hr : 0 < r) (hs : |s| ≤ r / 2) (hk : |k| ≤ 4)
    (hpos : k = 4 → s ≤ 0) (hneg : k = -4 → 0 < s) :
    |Complex.arg z - barrierArgApprox k (s / r)| ≤ 9 * barrierAtanJ0 := by
  rw [barrierComplexArg_octant_rational k z r s hrot hr hs hk hpos hneg]
  apply barrierArgApprox_error k (s / r) hk
  rw [abs_div, abs_of_pos hr, div_le_iff₀ hr]
  linarith

theorem barrierComplexLog_weighted_error (c z : ℂ) (m k : ℤ) (y r s : ℝ)
    (hnorm : z.re ^ 2 + z.im ^ 2 = (2 : ℝ) ^ m * y)
    (hy : y ∈ Set.Icc (1 : ℝ) 2)
    (hrot : barrierOctantRotate k z = ⟨r, s⟩)
    (hr : 0 < r) (hs : |s| ≤ r / 2) (hk : |k| ≤ 4)
    (hpos : k = 4 → s ≤ 0) (hneg : k = -4 → 0 < s) :
    |(c * Complex.log z).re - barrierWeightedComplexLogApprox c m k y (s / r)| ≤
      |c.re| * ((|(m : ℝ)| + 1) * barrierLogHError / 2) +
        |c.im| * (9 * barrierAtanJ0) := by
  have hl := barrierComplexLog_re_error z m y hnorm hy
  have ha := barrierComplexArg_octant_error k z r s hrot hr hs hk hpos hneg
  rw [Complex.mul_re, Complex.log_im, barrierWeightedComplexLogApprox]
  calc
    _ = |c.re * ((Complex.log z).re - barrierScaledLogApprox m y / 2) -
        c.im * (Complex.arg z - barrierArgApprox k (s / r))| := by congr 1; ring
    _ ≤ |c.re * ((Complex.log z).re - barrierScaledLogApprox m y / 2)| +
        |c.im * (Complex.arg z - barrierArgApprox k (s / r))| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le
        (c.re * ((Complex.log z).re - barrierScaledLogApprox m y / 2))
        (c.im * (Complex.arg z - barrierArgApprox k (s / r)))
    _ = |c.re| * |(Complex.log z).re - barrierScaledLogApprox m y / 2| +
        |c.im| * |Complex.arg z - barrierArgApprox k (s / r)| := by rw [abs_mul, abs_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hl (abs_nonneg _))
      (mul_le_mul_of_nonneg_left ha (abs_nonneg _))

open scoped BigOperators

def barrierLogHRat (y : ℚ) : ℚ :=
  2 * ∑ j ∈ Finset.range 18,
    ((y - 1) / (y + 1)) ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℚ)

def barrierScaledLogRat (m : ℤ) (y : ℚ) : ℚ :=
  (m : ℚ) * barrierLogHRat 2 + barrierLogHRat y

theorem barrierLogHRat_cast (y : ℚ) :
    ((barrierLogHRat y : ℚ) : ℝ) = barrierLogH (y : ℝ) := by
  unfold barrierLogHRat barrierLogH
  push_cast
  rfl

theorem barrierScaledLogRat_cast (m : ℤ) (y : ℚ) :
    ((barrierScaledLogRat m y : ℚ) : ℝ) = barrierScaledLogApprox m (y : ℝ) := by
  unfold barrierScaledLogRat barrierScaledLogApprox
  push_cast
  rw [barrierLogHRat_cast, barrierLogHRat_cast]
  norm_num

theorem barrier_fixed_log_abs_error {s : ℝ} {m : ℤ} {y : ℚ}
    (h : Case1PointData.FixedLogNormalization s m y) :
    |Real.log s - ((barrierScaledLogRat m y : ℚ) : ℝ)| <
      (1 / 1000000000000000 : ℝ) := by
  rcases h with ⟨hs, hy, hm⟩
  rw [hs, barrierScaledLogRat_cast]
  exact barrier_scaled_log_abs_error_lt m hy hm

end

section




open scoped BigOperators

def barrierAtanJRat (t : ℚ) : ℚ :=
  ∑ j ∈ Finset.range 24, (-1 : ℚ) ^ j * t ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℚ)

def barrierArgApproxRat (k : ℤ) (t : ℚ) : ℚ :=
  (k : ℚ) * (barrierAtanJRat (1 / 2) + barrierAtanJRat (1 / 3)) + barrierAtanJRat t

def barrierWeightedComplexLogRat (c d : ℚ) (m k : ℤ) (y t : ℚ) : ℚ :=
  c * (barrierScaledLogRat m y / 2) - d * barrierArgApproxRat k t

theorem barrierAtanJRat_cast (t : ℚ) :
    ((barrierAtanJRat t : ℚ) : ℝ) = barrierAtanJ (t : ℝ) := by
  unfold barrierAtanJRat barrierAtanJ
  push_cast
  rfl

theorem barrierArgApproxRat_cast (k : ℤ) (t : ℚ) :
    ((barrierArgApproxRat k t : ℚ) : ℝ) = barrierArgApprox k (t : ℝ) := by
  unfold barrierArgApproxRat barrierArgApprox
  push_cast
  rw [barrierAtanJRat_cast, barrierAtanJRat_cast, barrierAtanJRat_cast]
  norm_num

theorem barrierWeightedComplexLogRat_cast (c d : ℚ) (m k : ℤ) (y t : ℚ) :
    ((barrierWeightedComplexLogRat c d m k y t : ℚ) : ℝ) =
      barrierWeightedComplexLogApprox (barrierComplex c d) m k (y : ℝ) (t : ℝ) := by
  unfold barrierWeightedComplexLogRat barrierWeightedComplexLogApprox barrierComplex
  push_cast
  rw [barrierScaledLogRat_cast, barrierArgApproxRat_cast]

theorem barrier_weighted_log_error_allowance :
    101 * barrierLogHError / 2 + 9 * barrierAtanJ0 < (1 / 1000000000000 : ℝ) := by
  norm_num [barrierLogHError, barrierAtanJ0]

theorem barrierWeightedComplexLogRat_error
    (c d : ℚ) (z : ℂ) (m k : ℤ) (y r s : ℚ)
    (hc : |(c : ℝ)| ≤ 1) (hd : |(d : ℝ)| ≤ 1)
    (hm : |(m : ℝ)| ≤ 100)
    (hnorm : z.re ^ 2 + z.im ^ 2 = (2 : ℝ) ^ m * (y : ℝ))
    (hy : (y : ℝ) ∈ Set.Icc (1 : ℝ) 2)
    (hrot : barrierOctantRotate k z = ⟨(r : ℝ), (s : ℝ)⟩)
    (hr : (0 : ℝ) < (r : ℝ)) (hs : |(s : ℝ)| ≤ (r : ℝ) / 2)
    (hk : |k| ≤ 4) (hpos : k = 4 → (s : ℝ) ≤ 0)
    (hneg : k = -4 → (0 : ℝ) < (s : ℝ)) :
    |(barrierComplex c d * Complex.log z).re -
      ((barrierWeightedComplexLogRat c d m k y (s / r) : ℚ) : ℝ)| <
        (1 / 1000000000000 : ℝ) := by
  rw [barrierWeightedComplexLogRat_cast]
  push_cast
  have h := barrierComplexLog_weighted_error (barrierComplex c d) z m k
    (y : ℝ) (r : ℝ) (s : ℝ) hnorm hy hrot hr hs hk hpos hneg
  change _ ≤ |(c : ℝ)| * ((|(m : ℝ)| + 1) * barrierLogHError / 2) +
    |(d : ℝ)| * (9 * barrierAtanJ0) at h
  have he : 0 ≤ barrierLogHError := by unfold barrierLogHError; positivity
  have hj : 0 ≤ barrierAtanJ0 := by unfold barrierAtanJ0; positivity
  have hreal : 0 ≤ (|(m : ℝ)| + 1) * barrierLogHError / 2 := by positivity
  have hang : 0 ≤ 9 * barrierAtanJ0 := by positivity
  have h1 := mul_le_mul_of_nonneg_right hc hreal
  have h2 := mul_le_mul_of_nonneg_right hd hang
  have hm' := mul_le_mul_of_nonneg_right (show |(m : ℝ)| + 1 ≤ 101 by linarith) he
  have hall : |(c : ℝ)| * ((|(m : ℝ)| + 1) * barrierLogHError / 2) +
      |(d : ℝ)| * (9 * barrierAtanJ0) ≤ 101 * barrierLogHError / 2 + 9 * barrierAtanJ0 := by
    nlinarith
  exact h.trans_lt (hall.trans_lt barrier_weighted_log_error_allowance)

end

theorem barrierLogHRat_two_eq :
    barrierLogHRat 2 = (5796068539909855793494541848 / 8361959339180483840538659925 : ℚ) := by
  norm_num [barrierLogHRat, Finset.sum_range_succ]

theorem barrierAtanJRat_half_eq :
    barrierAtanJRat (1 / 2) = (82070093885243869609160349250891 / 177009634670845858814825909452800 : ℚ) := by
  norm_num [barrierAtanJRat, Finset.sum_range_succ]

theorem barrierAtanJRat_third_eq :
    barrierAtanJRat (1 / 3) = (112400876852048123008581938124204001832 / 349341672659511491372281601118448876275 : ℚ) := by
  norm_num [barrierAtanJRat, Finset.sum_range_succ]

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierPowerLogFormula
namespace OAI

noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

private theorem barrierFiniteCoeff_S_hasSum (cs : List ℤ) (x : ℝ) :
    HasSum (fun k : ℕ => barrierFiniteCoeff cs (k + 1) * x ^ (k + 1) /
      ((k + 1 : ℕ) : ℝ))
      (∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) *
        x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
  have hs : HasSum
      (fun k : ℕ => ((cs.getD k 0 : ℝ) / 100000000) * x ^ (k + 1) /
        ((k + 1 : ℕ) : ℝ))
      (∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) *
        x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    have hlen : cs.length ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    rw [List.getD_eq_default cs 0 hlen]
    norm_num
  simpa [barrierFiniteCoeff] using hs

theorem barrierTailRow_S_hasSum (z r : ℂ) (hz : ‖z‖ < 1)
    {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ => (r * z ^ (k + 1)).re * x ^ (k + 1) /
      ((k + 1 : ℕ) : ℝ)) (-(r * Complex.log (1 - (x : ℂ) * z)).re) := by
  have hxz : ‖(x : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact lt_of_le_of_lt (by nlinarith [norm_nonneg z]) hz
  have hc : HasSum (fun k : ℕ =>
      (r * z ^ (k + 1)) * (x : ℂ) ^ (k + 1) / ((k + 1 : ℕ) : ℂ))
      (-(r * Complex.log (1 - (x : ℂ) * z))) := by
    convert (Complex.hasSum_taylorSeries_neg_log' hxz).mul_left r using 1
    · rfl
    · funext k
      push_cast
      rw [mul_pow]
      ring
    · ring
  simpa only [Complex.div_natCast_re, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.neg_re] using
    Complex.hasSum_re hc

theorem barrierTail_S_hasSum (tail : List (ℂ × ℂ))
    (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1) {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ =>
      (tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ (k + 1))).sum.re *
        x ^ (k + 1) / ((k + 1 : ℕ) : ℝ))
      (-(tail.map (fun zr : ℂ × ℂ =>
        zr.2 * Complex.log (1 - (x : ℂ) * zr.1))).sum.re) := by
  revert htail
  induction tail with
  | nil =>
      intro _
      simp
  | cons zr tail ih =>
      intro htail
      have hr := barrierTailRow_S_hasSum zr.1 zr.2 (htail zr List.mem_cons_self) hx
      have ht := ih (fun w hw => htail w (List.mem_cons_of_mem _ hw))
      simpa only [List.map_cons, List.sum_cons, Complex.add_re, add_mul, add_div,
        neg_add] using hr.add ht

theorem barrierTrialS_eq_finite_log (cs : List ℤ) (tail : List (ℂ × ℂ))
    (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1) {x : ℝ} (hx : |x| ≤ 1) :
    barrierTrialS (barrierTrial cs tail) x =
      (∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) *
        x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) -
      (tail.map (fun zr : ℂ × ℂ =>
        zr.2 * Complex.log (1 - (x : ℂ) * zr.1))).sum.re := by
  have hh := (barrierFiniteCoeff_S_hasSum cs x).add (barrierTail_S_hasSum tail htail hx)
  have hs : HasSum (fun k : ℕ => barrierTrial cs tail (k + 1) * x ^ (k + 1) /
      ((k + 1 : ℕ) : ℝ))
      ((∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) *
        x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) -
        (tail.map (fun zr : ℂ × ℂ =>
          zr.2 * Complex.log (1 - (x : ℂ) * zr.1))).sum.re) := by
    simpa [barrierTrial, add_mul, add_div, sub_eq_add_neg] using hh
  exact hs.tsum_eq

theorem barrierV2_S_eq_finite_log {x : ℝ} (hx : |x| ≤ 1) :
    barrierTrialS barrierV2 x =
      (∑ k ∈ Finset.range barrierV2Finite.length,
        ((barrierV2Finite.getD k 0 : ℝ) / 100000000) * x ^ (k + 1) /
          ((k + 1 : ℕ) : ℝ)) -
      (barrierV2Tail.map (fun zr : ℂ × ℂ =>
        zr.2 * Complex.log (1 - (x : ℂ) * zr.1))).sum.re := by
  apply barrierTrialS_eq_finite_log barrierV2Finite barrierV2Tail _ hx
  intro zr hzr
  exact lt_of_le_of_lt (barrierV2_tail_norm_bounds zr hzr).1 (by norm_num)

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
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction
namespace OAI

noncomputable section

namespace InternalCatalan

section













end

section

open Set Filter
open scoped Topology



















end

section
open scoped BigOperators

def barrierCase2XPLogTerm (x : ℝ) (zr : ℂ × ℂ) : ℝ :=
  (2 * zr.2 * Complex.log (1 - 2 * (x : ℂ) * zr.1 + zr.1 ^ 2)).re

def barrierCase2XVLogTerm (x : ℝ) (zr : ℂ × ℂ) : ℝ :=
  (zr.2 * Complex.log (1 - (x : ℂ) * zr.1)).re


def barrierCase2XRat (x : ℚ) : ℚ :=
  -4 * barrierFiniteTRat barrierP2Finite x - barrierFiniteSRat barrierV2Finite x


private theorem barrierFiniteT_sum_cast (cs : List ℤ) (x : ℚ) :
    (∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) *
      (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (x : ℝ) /
        ((k + 1 : ℕ) : ℝ)) = ((barrierFiniteTRat cs x : ℚ) : ℝ) := by
  rw [← barrierTrialT_nil_eq_sum cs (x : ℝ), barrierTrialT_nil_eval_rat]

private theorem barrierFiniteS_sum_cast (cs : List ℤ) (x : ℚ) :
    (∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) *
      (x : ℝ) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) =
      ((barrierFiniteSRat cs x : ℚ) : ℝ) := by
  rw [← barrierTrialS_nil_eq_sum cs (x : ℝ), barrierTrialS_nil_eval_rat]

private theorem barrierList_scaled_re_sum {α : Type*} (l : List α)
    (f : α → ℂ) (a : ℝ) :
    a * (l.map f).sum.re = (l.map (fun z => ((a : ℂ) * f z).re)).sum := by
  induction l with
  | nil => simp
  | cons z l ih =>
      simp only [List.map_cons, List.sum_cons, Complex.add_re]
      rw [← ih]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      ring

theorem barrierCase2X_eval_rat (x : ℚ) (hx : |(x : ℝ)| ≤ 1) :
    barrierCase2X (x : ℝ) =
      (19 / 48 : ℝ) * Real.log |(x : ℝ)| +
        (1 / 12 : ℝ) * Real.log (1 - (x : ℝ)) -
        (65 / 48 : ℝ) * Real.log (1 + (x : ℝ) ^ 2) +
        ((barrierCase2XRat x : ℚ) : ℝ) +
        (barrierP2Tail.map (barrierCase2XPLogTerm (x : ℝ))).sum +
        (barrierV2Tail.map (barrierCase2XVLogTerm (x : ℝ))).sum := by
  have hp : 2 * (barrierP2Tail.map (fun zr : ℂ × ℂ =>
      zr.2 * Complex.log (1 - 2 * (x : ℂ) * zr.1 + zr.1 ^ 2))).sum.re =
      (barrierP2Tail.map (barrierCase2XPLogTerm (x : ℝ))).sum := by
    unfold barrierCase2XPLogTerm
    simpa [barrierCase2XPLogTerm, mul_assoc] using barrierList_scaled_re_sum
      barrierP2Tail (fun zr : ℂ × ℂ =>
        zr.2 * Complex.log (1 - 2 * (x : ℂ) * zr.1 + zr.1 ^ 2)) 2
  have hv : (barrierV2Tail.map (fun zr : ℂ × ℂ =>
      zr.2 * Complex.log (1 - (x : ℂ) * zr.1))).sum.re =
      (barrierV2Tail.map (barrierCase2XVLogTerm (x : ℝ))).sum := by
    unfold barrierCase2XVLogTerm
    simpa [barrierCase2XVLogTerm] using barrierList_scaled_re_sum
      barrierV2Tail (fun zr : ℂ × ℂ => zr.2 * Complex.log (1 - (x : ℂ) * zr.1)) 1
  unfold barrierCase2X
  rw [barrierP2_T_eq_finite_log hx, barrierV2_S_eq_finite_log hx,
    barrierFiniteT_sum_cast, barrierFiniteS_sum_cast, ← hp, ← hv]
  unfold realEnergyField barrierLambda2 barrierCase2XRat
  push_cast
  ring


end
section



end

section

open scoped ComplexConjugate

theorem barrierCase2XPLogTerm_conj (x : ℝ) (z r : ℂ)
    (hz : (1 - 2 * (x : ℂ) * z + z ^ 2).im ≠ 0 ∨
      0 < (1 - 2 * (x : ℂ) * z + z ^ 2).re) :
    barrierCase2XPLogTerm x (star z, star r) = barrierCase2XPLogTerm x (z, r) := by
  have h := barrierComplexLog_conj_weighted_re (2 * r)
    (1 - 2 * (x : ℂ) * z + z ^ 2) hz
  rw [← barrierComplexLog_quadratic_conj x z] at h
  simpa only [barrierCase2XPLogTerm, Complex.star_def, map_mul, map_ofNat] using h

theorem barrierCase2XVLogTerm_conj (x : ℝ) (z r : ℂ)
    (hz : (1 - (x : ℂ) * z).im ≠ 0 ∨ 0 < (1 - (x : ℂ) * z).re) :
    barrierCase2XVLogTerm x (star z, star r) = barrierCase2XVLogTerm x (z, r) := by
  have h := barrierComplexLog_conj_weighted_re r (1 - (x : ℂ) * z) hz
  rw [← barrierComplexLog_linear_conj x z] at h
  simpa only [barrierCase2XVLogTerm, Complex.star_def] using h


end

open Set



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoPointData
namespace OAI

noncomputable section
namespace InternalCatalan.Case2PointData

def X0 : ℚ := (-2400277287 / 2500000000)

def X1 : ℚ := (-2235579393 / 2500000000)

def X2 : ℚ := (-7608305633 / 10000000000)







































end InternalCatalan.Case2PointData

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoLogApprox
namespace OAI

noncomputable section

namespace InternalCatalan

namespace Case2PointData
open InternalCatalan.Case1PointData

theorem X0_normalizations :
    FixedLogNormalization |(X0 : ℝ)| (-1) (2400277287 / 1250000000) ∧
    FixedLogNormalization (1 - (X0 : ℝ)) (0) (4900277287 / 2500000000) ∧
    FixedLogNormalization (1 + (X0 : ℝ) ^ 2) (0) (12011331054488080369 / 6250000000000000000) := by
  norm_num [FixedLogNormalization, X0, Set.mem_Icc]

theorem X1_normalizations :
    FixedLogNormalization |(X1 : ℝ)| (-1) (2235579393 / 1250000000) ∧
    FixedLogNormalization (1 - (X1 : ℝ)) (0) (4735579393 / 2500000000) ∧
    FixedLogNormalization (1 + (X1 : ℝ) ^ 2) (0) (11247815222406248449 / 6250000000000000000) := by
  norm_num [FixedLogNormalization, X1, Set.mem_Icc]

theorem X2_normalizations :
    FixedLogNormalization |(X2 : ℝ)| (-1) (7608305633 / 5000000000) ∧
    FixedLogNormalization (1 - (X2 : ℝ)) (0) (17608305633 / 10000000000) ∧
    FixedLogNormalization (1 + (X2 : ℝ) ^ 2) (0) (157886314605139530689 / 100000000000000000000) := by
  norm_num [FixedLogNormalization, X2, Set.mem_Icc]



































end Case2PointData

def barrierCase2XApproxRat (x : ℚ) (m0 m1 m2 : ℤ) (y0 y1 y2 : ℚ) : ℚ :=
  (19 / 48 : ℚ) * barrierScaledLogRat m0 y0 +
    (1 / 12 : ℚ) * barrierScaledLogRat m1 y1 -
    (65 / 48 : ℚ) * barrierScaledLogRat m2 y2 + barrierCase2XRat x


theorem barrierCase2X_realLog_approx_error (x : ℚ) (hx : |(x : ℝ)| ≤ 1)
    (m0 m1 m2 : ℤ) (y0 y1 y2 : ℚ)
    (h0 : Case1PointData.FixedLogNormalization |(x : ℝ)| m0 y0)
    (h1 : Case1PointData.FixedLogNormalization (1 - (x : ℝ)) m1 y1)
    (h2 : Case1PointData.FixedLogNormalization (1 + (x : ℝ) ^ 2) m2 y2) :
    |barrierCase2X (x : ℝ) -
      (((barrierCase2XApproxRat x m0 m1 m2 y0 y1 y2 : ℚ) : ℝ) +
        (barrierP2Tail.map (barrierCase2XPLogTerm (x : ℝ))).sum +
        (barrierV2Tail.map (barrierCase2XVLogTerm (x : ℝ))).sum)| <
      (2 / 1000000000000000 : ℝ) := by
  have he0 := abs_lt.mp (barrier_fixed_log_abs_error h0)
  have he1 := abs_lt.mp (barrier_fixed_log_abs_error h1)
  have he2 := abs_lt.mp (barrier_fixed_log_abs_error h2)
  rw [barrierCase2X_eval_rat x hx]
  unfold barrierCase2XApproxRat
  push_cast
  apply abs_lt.mpr
  constructor <;> linarith [he0.1, he0.2, he1.1, he1.2, he2.1, he2.2]


end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoLogsX0Group0
namespace OAI

noncomputable section
namespace InternalCatalan

def barrierCase2X0XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X0 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X0XP0_arg_eq :
    barrierCase2X0XP0LogArg = barrierComplex (83867213879 / 25000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XP0LogArg, Case2PointData.X0, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X0XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X0XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (3) (0) (7033709563825930226641 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X0XP0LogArg (3) (0) (7033709563825930226641 / 5000000000000000000000) (83867213879 / 25000000000) (0 / 1)
  have hratio : ((0 / 1) / (83867213879 / 25000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X0XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (3) (0) (7033709563825930226641 / 5000000000000000000000) (0 / 1) <
      (-226057576541 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X0 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (-226057576541 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X0XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (3) (0) (7033709563825930226641 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-226057576541 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XP0_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X0XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X0 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X0XP1_arg_eq :
    barrierCase2X0XP1LogArg = barrierComplex (230538032489 / 62500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XP1LogArg, Case2PointData.X0, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X0XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X0XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (53147784423899219535121 / 31250000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X0XP1LogArg (3) (0) (53147784423899219535121 / 31250000000000000000000) (230538032489 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (230538032489 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X0XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (53147784423899219535121 / 31250000000000000000000) (0 / 1) <
      (-55904062121 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X0 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (-55904062121 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X0XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (53147784423899219535121 / 31250000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-55904062121 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XP1_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X0XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X0 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X0XP2_arg_eq :
    barrierCase2X0XP2LogArg = barrierComplex (51 / 100) (16801941009 / 12500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XP2LogArg, Case2PointData.X0, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X0XP2_arg_regular :
    (barrierCase2X0XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X0XP2LogArg).re := by
  rw [barrierCase2X0XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X0XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X0XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (1) (1) (322945846669915938081 / 312500000000000000000) (3475647003 / 7725647003) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X0XP2LogArg (1) (1) (322945846669915938081 / 312500000000000000000) (23176941009 / 12500000000) (10426941009 / 12500000000)
  have hratio : ((10426941009 / 12500000000) / (23176941009 / 12500000000) : ℚ) = (3475647003 / 7725647003) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X0XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (1) (1) (322945846669915938081 / 312500000000000000000) (3475647003 / 7725647003) <
      (-626091082313 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X0 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (-626091082313 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X0XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (1) (1) (322945846669915938081 / 312500000000000000000) (3475647003 / 7725647003) : ℚ) : ℝ) <
      (-626091082313 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XP2_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X0XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X0 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X0XP4_arg_eq :
    barrierCase2X0XP4LogArg = barrierComplex (111 / 400) (40804713879 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XP4LogArg, Case2PointData.X0, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X0XP4_arg_regular :
    (barrierCase2X0XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X0XP4LogArg).re := by
  rw [barrierCase2X0XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X0XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X0XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (1) (2) (1713153580997055226641 / 1250000000000000000000) (-2312500000 / 13601571293) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X0XP4LogArg (1) (2) (1713153580997055226641 / 1250000000000000000000) (40804713879 / 12500000000) (-111 / 200)
  have hratio : ((-111 / 200) / (40804713879 / 12500000000) : ℚ) = (-2312500000 / 13601571293) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X0XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (1) (2) (1713153580997055226641 / 1250000000000000000000) (-2312500000 / 13601571293) <
      (77970853175 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X0 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (77970853175 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X0XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (1) (2) (1713153580997055226641 / 1250000000000000000000) (-2312500000 / 13601571293) : ℚ) : ℝ) <
      (77970853175 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XP4_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X0XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X0 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X0XP6_arg_eq :
    barrierCase2X0XP6LogArg = barrierComplex (105851377601 / 312500000000) (60496377601 / 31250000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XP6LogArg, Case2PointData.X0, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X0XP6_arg_regular :
    (barrierCase2X0XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X0XP6LogArg).re := by
  rw [barrierCase2X0XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X0XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X0XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (1) (2) (377185684424306936035301 / 195312500000000000000000) (-105851377601 / 604963776010) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X0XP6LogArg (1) (2) (377185684424306936035301 / 195312500000000000000000) (60496377601 / 15625000000) (-105851377601 / 156250000000)
  have hratio : ((-105851377601 / 156250000000) / (60496377601 / 15625000000) : ℚ) = (-105851377601 / 604963776010) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X0XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (1) (2) (377185684424306936035301 / 195312500000000000000000) (-105851377601 / 604963776010) <
      (102983412248 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X0 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (102983412248 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X0XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (1) (2) (377185684424306936035301 / 195312500000000000000000) (-105851377601 / 604963776010) : ℚ) : ℝ) <
      (102983412248 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XP6_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X0XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X0 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X0XP8_arg_eq :
    barrierCase2X0XP8LogArg = barrierComplex (-4561377601 / 312500000000) (49916377601 / 31250000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XP8LogArg, Case2PointData.X0, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X0XP8_arg_regular :
    (barrierCase2X0XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X0XP8LogArg).re := by
  rw [barrierCase2X0XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X0XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X0XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (2) (249185281446180356035301 / 195312500000000000000000) (4561377601 / 499163776010) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X0XP8LogArg (1) (2) (249185281446180356035301 / 195312500000000000000000) (49916377601 / 15625000000) (4561377601 / 156250000000)
  have hratio : ((4561377601 / 156250000000) / (49916377601 / 15625000000) : ℚ) = (4561377601 / 499163776010) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X0XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (2) (249185281446180356035301 / 195312500000000000000000) (4561377601 / 499163776010) <
      (-153498075605 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X0 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (-153498075605 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X0XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (2) (249185281446180356035301 / 195312500000000000000000) (4561377601 / 499163776010) : ℚ) : ℝ) <
      (-153498075605 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XP8_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoLogsX1Group0
namespace OAI

noncomputable section
namespace InternalCatalan

def barrierCase2X1XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X1 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X1XP0_arg_eq :
    barrierCase2X1XP0LogArg = barrierComplex (81067349681 / 25000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XP0LogArg, Case2PointData.X1, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X1XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X1XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (3) (0) (6571915184301530801761 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X1XP0LogArg (3) (0) (6571915184301530801761 / 5000000000000000000000) (81067349681 / 25000000000) (0 / 1)
  have hratio : ((0 / 1) / (81067349681 / 25000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X1XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (3) (0) (6571915184301530801761 / 5000000000000000000000) (0 / 1) <
      (-219715931992 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X1 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (-219715931992 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X1XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (3) (0) (6571915184301530801761 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-219715931992 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XP0_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X1XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X1 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X1XP1_arg_eq :
    barrierCase2X1XP1LogArg = barrierComplex (222797231471 / 62500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XP1LogArg, Case2PointData.X1, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X1XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X1XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (49638606351142352823841 / 31250000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X1XP1LogArg (3) (0) (49638606351142352823841 / 31250000000000000000000) (222797231471 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (222797231471 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X1XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (49638606351142352823841 / 31250000000000000000000) (0 / 1) <
      (-54441250138 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X1 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (-54441250138 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X1XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (49638606351142352823841 / 31250000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-54441250138 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XP1_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X1XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X1 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X1XP2_arg_eq :
    barrierCase2X1XP2LogArg = barrierComplex (51 / 100) (15649055751 / 12500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XP2LogArg, Case2PointData.X1, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X1XP2_arg_regular :
    (barrierCase2X1XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X1XP2LogArg).re := by
  rw [barrierCase2X1XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X1XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X1XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (1) (285533570897906174001 / 156250000000000000000) (3091351917 / 7341351917) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X1XP2LogArg (0) (1) (285533570897906174001 / 156250000000000000000) (22024055751 / 12500000000) (9274055751 / 12500000000)
  have hratio : ((9274055751 / 12500000000) / (22024055751 / 12500000000) : ℚ) = (3091351917 / 7341351917) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X1XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (1) (285533570897906174001 / 156250000000000000000) (3091351917 / 7341351917) <
      (-577565314512 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X1 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (-577565314512 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X1XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (1) (285533570897906174001 / 156250000000000000000) (3091351917 / 7341351917) : ℚ) : ℝ) <
      (-577565314512 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XP2_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X1XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X1 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X1XP4_arg_eq :
    barrierCase2X1XP4LogArg = barrierComplex (111 / 400) (38004849681 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XP4LogArg, Case2PointData.X1, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X1XP4_arg_regular :
    (barrierCase2X1XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X1XP4LogArg).re := by
  rw [barrierCase2X1XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X1XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X1XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (1) (2) (1492497505525405801761 / 1250000000000000000000) (-2312500000 / 12668283227) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X1XP4LogArg (1) (2) (1492497505525405801761 / 1250000000000000000000) (38004849681 / 12500000000) (-111 / 200)
  have hratio : ((-111 / 200) / (38004849681 / 12500000000) : ℚ) = (-2312500000 / 12668283227) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X1XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (1) (2) (1492497505525405801761 / 1250000000000000000000) (-2312500000 / 12668283227) <
      (78090797977 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X1 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (78090797977 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X1XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (1) (2) (1492497505525405801761 / 1250000000000000000000) (-2312500000 / 12668283227) : ℚ) : ℝ) <
      (78090797977 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XP4_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X1XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X1 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X1XP6_arg_eq :
    barrierCase2X1XP6LogArg = barrierComplex (102063326039 / 312500000000) (56708326039 / 31250000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XP6LogArg, Case2PointData.X1, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X1XP6_arg_regular :
    (barrierCase2X1XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X1XP6LogArg).re := by
  rw [barrierCase2X1XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X1XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X1XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (1) (2) (332000346736695758381621 / 195312500000000000000000) (-102063326039 / 567083260390) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X1XP6LogArg (1) (2) (332000346736695758381621 / 195312500000000000000000) (56708326039 / 15625000000) (-102063326039 / 156250000000)
  have hratio : ((-102063326039 / 156250000000) / (56708326039 / 15625000000) : ℚ) = (-102063326039 / 567083260390) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X1XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (1) (2) (332000346736695758381621 / 195312500000000000000000) (-102063326039 / 567083260390) <
      (104608101086 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X1 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (104608101086 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X1XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (1) (2) (332000346736695758381621 / 195312500000000000000000) (-102063326039 / 567083260390) : ℚ) : ℝ) <
      (104608101086 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XP6_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X1XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X1 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X1XP8_arg_eq :
    barrierCase2X1XP8LogArg = barrierComplex (-773326039 / 312500000000) (46128326039 / 31250000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XP8LogArg, Case2PointData.X1, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X1XP8_arg_regular :
    (barrierCase2X1XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X1XP8LogArg).re := by
  rw [barrierCase2X1XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X1XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X1XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (2) (212782844349191138381621 / 195312500000000000000000) (773326039 / 461283260390) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X1XP8LogArg (1) (2) (212782844349191138381621 / 195312500000000000000000) (46128326039 / 15625000000) (773326039 / 156250000000)
  have hratio : ((773326039 / 156250000000) / (46128326039 / 15625000000) : ℚ) = (773326039 / 461283260390) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X1XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (2) (212782844349191138381621 / 195312500000000000000000) (773326039 / 461283260390) <
      (-151157166207 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X1 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (-151157166207 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X1XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (2) (212782844349191138381621 / 195312500000000000000000) (773326039 / 461283260390) : ℚ) : ℝ) <
      (-151157166207 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XP8_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoLogsX2Group0
namespace OAI

noncomputable section
namespace InternalCatalan

def barrierCase2X2XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X2 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X2XP0_arg_eq :
    barrierCase2X2XP0LogArg = barrierComplex (301591195761 / 100000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XP0LogArg, Case2PointData.X2, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X2XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X2XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (3) (0) (90957249360549824369121 / 80000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X2XP0LogArg (3) (0) (90957249360549824369121 / 80000000000000000000000) (301591195761 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (301591195761 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X2XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (3) (0) (90957249360549824369121 / 80000000000000000000000) (0 / 1) <
      (-206174764969 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X2 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (-206174764969 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X2XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (3) (0) (90957249360549824369121 / 80000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-206174764969 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XP0_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X2XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X2 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X2XP1_arg_eq :
    barrierCase2X2XP1LogArg = barrierComplex (828490364751 / 250000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XP1LogArg, Case2PointData.X2, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X2XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X2XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (686396284485245023292001 / 500000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X2XP1LogArg (3) (0) (686396284485245023292001 / 500000000000000000000000) (828490364751 / 250000000000) (0 / 1)
  have hratio : ((0 / 1) / (828490364751 / 250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X2XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (686396284485245023292001 / 500000000000000000000000) (0 / 1) <
      (-51316735570 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X2 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (-51316735570 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X2XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (686396284485245023292001 / 500000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-51316735570 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XP1_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X2XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X2 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X2XP2_arg_eq :
    barrierCase2X2XP2LogArg = barrierComplex (51 / 100) (53258139431 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XP2LogArg, Case2PointData.X2, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X2XP2_arg_regular :
    (barrierCase2X2XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X2XP2LogArg).re := by
  rw [barrierCase2X2XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X2XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X2XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (1) (3486679415651837003761 / 2500000000000000000000) (27758139431 / 78758139431) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X2XP2LogArg (0) (1) (3486679415651837003761 / 2500000000000000000000) (78758139431 / 50000000000) (27758139431 / 50000000000)
  have hratio : ((27758139431 / 50000000000) / (78758139431 / 50000000000) : ℚ) = (27758139431 / 78758139431) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X2XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (1) (3486679415651837003761 / 2500000000000000000000) (27758139431 / 78758139431) <
      (-468961268538 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X2 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (-468961268538 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X2XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (1) (3486679415651837003761 / 2500000000000000000000) (27758139431 / 78758139431) : ℚ) : ℝ) <
      (-468961268538 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XP2_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X2XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X2 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X2XP4_arg_eq :
    barrierCase2X2XP4LogArg = barrierComplex (111 / 400) (129341195761 / 100000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XP4LogArg, Case2PointData.X2, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X2XP4_arg_regular :
    (barrierCase2X2XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X2XP4LogArg).re := by
  rw [barrierCase2X2XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X2XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X2XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (0) (2) (17499207420885324369121 / 10000000000000000000000) (-27750000000 / 129341195761) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X2XP4LogArg (0) (2) (17499207420885324369121 / 10000000000000000000000) (129341195761 / 50000000000) (-111 / 200)
  have hratio : ((-111 / 200) / (129341195761 / 50000000000) : ℚ) = (-27750000000 / 129341195761) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X2XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (0) (2) (17499207420885324369121 / 10000000000000000000000) (-27750000000 / 129341195761) <
      (78157067239 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X2 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (78157067239 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X2XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (0) (2) (17499207420885324369121 / 10000000000000000000000) (-27750000000 / 129341195761) : ℚ) : ℝ) <
      (78157067239 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XP4_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X2XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X2 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X2XP6_arg_eq :
    barrierCase2X2XP6LogArg = barrierComplex (377571029559 / 1250000000000) (196151029559 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XP6LogArg, Case2PointData.X2, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X2XP6_arg_regular :
    (barrierCase2X2XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X2XP6LogArg).re := by
  rw [barrierCase2X2XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X2XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X2XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (1) (2) (3990082522067812425182581 / 3125000000000000000000000) (-377571029559 / 1961510295590) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X2XP6LogArg (1) (2) (3990082522067812425182581 / 3125000000000000000000000) (196151029559 / 62500000000) (-377571029559 / 625000000000)
  have hratio : ((-377571029559 / 625000000000) / (196151029559 / 62500000000) : ℚ) = (-377571029559 / 1961510295590) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X2XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (1) (2) (3990082522067812425182581 / 3125000000000000000000000) (-377571029559 / 1961510295590) <
      (108144189988 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X2 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (108144189988 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X2XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (1) (2) (3990082522067812425182581 / 3125000000000000000000000) (-377571029559 / 1961510295590) : ℚ) : ℝ) <
      (108144189988 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XP6_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X2XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X2 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X2XP8_arg_eq :
    barrierCase2X2XP8LogArg = barrierComplex (27588970441 / 1250000000000) (153831029559 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XP8LogArg, Case2PointData.X2, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X2XP8_arg_regular :
    (barrierCase2X2XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X2XP8LogArg).re := by
  rw [barrierCase2X2XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X2XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X2XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (0) (2) (2367159716808187545182581 / 1562500000000000000000000) (-27588970441 / 1538310295590) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X2XP8LogArg (0) (2) (2367159716808187545182581 / 1562500000000000000000000) (153831029559 / 62500000000) (-27588970441 / 625000000000)
  have hratio : ((-27588970441 / 625000000000) / (153831029559 / 62500000000) : ℚ) = (-27588970441 / 1538310295590) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X2XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (0) (2) (2367159716808187545182581 / 1562500000000000000000000) (-27588970441 / 1538310295590) <
      (-145548528877 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X2 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (-145548528877 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X2XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (0) (2) (2367159716808187545182581 / 1562500000000000000000000) (-27588970441 / 1538310295590) : ℚ) : ℝ) <
      (-145548528877 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XP8_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoTailSums
namespace OAI

noncomputable section
namespace InternalCatalan

theorem barrierP2Tail_getD_pair (i : ℕ) (hi : i ∈ [2, 4, 6, 8]) :
    barrierP2Tail.getD (i + 1) (0, 0) =
      (star (barrierP2Tail.getD i (0, 0)).1, star (barrierP2Tail.getD i (0, 0)).2) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> rfl

theorem barrierV2Tail_getD_pair (i : ℕ) (hi : i ∈ [5, 7, 9, 11]) :
    barrierV2Tail.getD (i + 1) (0, 0) =
      (star (barrierV2Tail.getD i (0, 0)).1, star (barrierV2Tail.getD i (0, 0)).2) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> rfl

theorem barrierP2Tail_paired_sum (f : ℂ × ℂ → ℝ)
    (hp : ∀ i ∈ [2, 4, 6, 8],
      f (barrierP2Tail.getD (i + 1) (0, 0)) = f (barrierP2Tail.getD i (0, 0))) :
    (barrierP2Tail.map f).sum =
      f (barrierP2Tail.getD 0 (0, 0)) + f (barrierP2Tail.getD 1 (0, 0)) +
      2 * f (barrierP2Tail.getD 2 (0, 0)) + 2 * f (barrierP2Tail.getD 4 (0, 0)) +
      2 * f (barrierP2Tail.getD 6 (0, 0)) + 2 * f (barrierP2Tail.getD 8 (0, 0)) := by
  have h2 := hp 2 (by simp)
  have h4 := hp 4 (by simp)
  have h6 := hp 6 (by simp)
  have h8 := hp 8 (by simp)
  norm_num [barrierP2Tail, barrierConjugatePair] at h2 h4 h6 h8 ⊢
  linarith

theorem barrierV2Tail_paired_sum (f : ℂ × ℂ → ℝ)
    (hp : ∀ i ∈ [5, 7, 9, 11],
      f (barrierV2Tail.getD (i + 1) (0, 0)) = f (barrierV2Tail.getD i (0, 0))) :
    (barrierV2Tail.map f).sum =
      f (barrierV2Tail.getD 0 (0, 0)) + f (barrierV2Tail.getD 1 (0, 0)) +
      f (barrierV2Tail.getD 2 (0, 0)) + f (barrierV2Tail.getD 3 (0, 0)) +
      f (barrierV2Tail.getD 4 (0, 0)) + 2 * f (barrierV2Tail.getD 5 (0, 0)) +
      2 * f (barrierV2Tail.getD 7 (0, 0)) + 2 * f (barrierV2Tail.getD 9 (0, 0)) +
      2 * f (barrierV2Tail.getD 11 (0, 0)) := by
  have h5 := hp 5 (by simp)
  have h7 := hp 7 (by simp)
  have h9 := hp 9 (by simp)
  have h11 := hp 11 (by simp)
  norm_num [barrierV2Tail, barrierConjugatePair] at h5 h7 h9 h11 ⊢
  linarith

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoPointX0
namespace OAI

noncomputable section

namespace InternalCatalan

section
open Polynomial

private theorem barrier_T_3 :
    Chebyshev.T ℚ 3 = 2 * X * Chebyshev.T ℚ 2 - Chebyshev.T ℚ 1 := by
  simpa only [Int.reduceAdd] using Chebyshev.T_add_two ℚ 1

private theorem barrier_T_4 :
    Chebyshev.T ℚ 4 = 2 * X * Chebyshev.T ℚ 3 - Chebyshev.T ℚ 2 := by
  simpa only [Int.reduceAdd] using Chebyshev.T_add_two ℚ 2

private theorem barrier_T_5 :
    Chebyshev.T ℚ 5 = 2 * X * Chebyshev.T ℚ 4 - Chebyshev.T ℚ 3 := by
  simpa only [Int.reduceAdd] using Chebyshev.T_add_two ℚ 3

private theorem barrier_T_6 :
    Chebyshev.T ℚ 6 = 2 * X * Chebyshev.T ℚ 5 - Chebyshev.T ℚ 4 := by
  simpa only [Int.reduceAdd] using Chebyshev.T_add_two ℚ 4

private theorem barrier_T_7 :
    Chebyshev.T ℚ 7 = 2 * X * Chebyshev.T ℚ 6 - Chebyshev.T ℚ 5 := by
  simpa only [Int.reduceAdd] using Chebyshev.T_add_two ℚ 5

private theorem barrier_T_8 :
    Chebyshev.T ℚ 8 = 2 * X * Chebyshev.T ℚ 7 - Chebyshev.T ℚ 6 := by
  simpa only [Int.reduceAdd] using Chebyshev.T_add_two ℚ 6

private theorem barrier_T_9 :
    Chebyshev.T ℚ 9 = 2 * X * Chebyshev.T ℚ 8 - Chebyshev.T ℚ 7 := by
  simpa only [Int.reduceAdd] using Chebyshev.T_add_two ℚ 7

private theorem barrier_T_10 :
    Chebyshev.T ℚ 10 = 2 * X * Chebyshev.T ℚ 9 - Chebyshev.T ℚ 8 := by
  simpa only [Int.reduceAdd] using Chebyshev.T_add_two ℚ 8

def barrierCase2TPExplicit (x : ℚ) : ℚ :=
  (1191279397 / 4000000000 : ℚ) +
    (29086173 / 50000000 : ℚ) * x ^ 1 +
    (-49273657 / 50000000 : ℚ) * x ^ 2 +
    (-10371061 / 25000000 : ℚ) * x ^ 3 +
    (51185159 / 50000000 : ℚ) * x ^ 4 +
    (4435791 / 7812500 : ℚ) * x ^ 5 +
    (-1619803 / 1562500 : ℚ) * x ^ 6 +
    (-1319413 / 2734375 : ℚ) * x ^ 7 +
    (4083239 / 6250000 : ℚ) * x ^ 8 +
    (671564 / 3515625 : ℚ) * x ^ 9 +
    (-346453 / 1953125 : ℚ) * x ^ 10

theorem barrierCase2TP_eq_explicit (x : ℚ) :
    barrierFiniteTRat barrierP2Finite x = barrierCase2TPExplicit x := by
  norm_num [barrierFiniteTRat, barrierP2Finite, barrierCase2TPExplicit,
    Finset.sum_range_succ, Chebyshev.T_two, barrier_T_3, barrier_T_4,
    barrier_T_5, barrier_T_6, barrier_T_7, barrier_T_8, barrier_T_9, barrier_T_10]
  ring



def barrierCase2SVExplicit (x : ℚ) : ℚ :=
  (-11955079 / 50000000 : ℚ) * x ^ 1 +
    (1322027 / 12500000 : ℚ) * x ^ 2 +
    (-288511 / 30000000 : ℚ) * x ^ 3 +
    (-11558199 / 400000000 : ℚ) * x ^ 4 +
    (6485289 / 500000000 : ℚ) * x ^ 5 +
    (485607 / 200000000 : ℚ) * x ^ 6 +
    (-17073 / 6250000 : ℚ) * x ^ 7 +
    (-565881 / 200000000 : ℚ) * x ^ 8 +
    (30469 / 10000000 : ℚ) * x ^ 9 +
    (-581227 / 500000000 : ℚ) * x ^ 10

theorem barrierCase2SV_eq_explicit (x : ℚ) :
    barrierFiniteSRat barrierV2Finite x = barrierCase2SVExplicit x := by
  norm_num [barrierFiniteSRat, barrierV2Finite, barrierCase2SVExplicit,
    Finset.sum_range_succ, Chebyshev.T_two, barrier_T_3, barrier_T_4,
    barrier_T_5, barrier_T_6, barrier_T_7, barrier_T_8, barrier_T_9, barrier_T_10]
  ring

end

def barrierCase2X0XV0LogArg : ℂ :=
  1 - ((Case2PointData.X0 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1

private theorem barrierCase2X0XV0_arg_eq :
    barrierCase2X0XV0LogArg = barrierComplex (724722713 / 3125000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XV0LogArg, Case2PointData.X0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X0XV0_weight_eq :
    (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XV0_error :
    |((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X0XV0LogArg).re -
      ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-5) (0) (525223010738080369 / 305175781250000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (15199211 / 100000000) (0 / 1)
    barrierCase2X0XV0LogArg (-5) (0) (525223010738080369 / 305175781250000000) (724722713 / 3125000000) (0 / 1)
  have hratio : ((0 / 1) / (724722713 / 3125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X0XV0_approx_upper :
    barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-5) (0) (525223010738080369 / 305175781250000000) (0 / 1) <
      (-222121337235 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XV0_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-222121337235 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X0XV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XV0_error).2
  have ha : ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-5) (0) (525223010738080369 / 305175781250000000) (0 / 1) : ℚ) : ℝ) <
      (-222121337235 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XV0_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X0XV1LogArg : ℂ :=
  1 - ((Case2PointData.X0 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1

private theorem barrierCase2X0XV1_arg_eq :
    barrierCase2X0XV1LogArg = barrierComplex (611668139 / 7812500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XV1LogArg, Case2PointData.X0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X0XV1_weight_eq :
    (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XV1_error :
    |((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X0XV1LogArg).re -
      ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-8) (0) (374137912267723321 / 238418579101562500) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2225831 / 50000000) (0 / 1)
    barrierCase2X0XV1LogArg (-8) (0) (374137912267723321 / 238418579101562500) (611668139 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (611668139 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X0XV1_approx_upper :
    barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-8) (0) (374137912267723321 / 238418579101562500) (0 / 1) <
      (-113396759439 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XV1_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-113396759439 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X0XV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XV1_error).2
  have ha : ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-8) (0) (374137912267723321 / 238418579101562500) (0 / 1) : ℚ) : ℝ) <
      (-113396759439 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XV1_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X0XV2LogArg : ℂ :=
  1 - ((Case2PointData.X0 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1

private theorem barrierCase2X0XV2_arg_eq :
    barrierCase2X0XV2LogArg = barrierComplex (57653050157 / 31250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XV2LogArg, Case2PointData.X0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X0XV2_weight_eq :
    (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XV2_error :
    |((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X0XV2LogArg).re -
      ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (3323874192405557724649 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (1272699 / 50000000) (0 / 1)
    barrierCase2X0XV2LogArg (1) (0) (3323874192405557724649 / 1953125000000000000000) (57653050157 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (57653050157 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X0XV2_approx_upper :
    barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (3323874192405557724649 / 1953125000000000000000) (0 / 1) <
      (15588622581 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XV2_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (15588622581 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X0XV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XV2_error).2
  have ha : ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (3323874192405557724649 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ) <
      (15588622581 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XV2_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X0XV3LogArg : ℂ :=
  1 - ((Case2PointData.X0 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1

private theorem barrierCase2X0XV3_arg_eq :
    barrierCase2X0XV3LogArg = barrierComplex (95605268453 / 50000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XV3LogArg, Case2PointData.X0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X0XV3_weight_eq :
    (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XV3_error :
    |((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X0XV3LogArg).re -
      ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (9140367355970197013209 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2466317 / 50000000) (0 / 1)
    barrierCase2X0XV3LogArg (1) (0) (9140367355970197013209 / 5000000000000000000000) (95605268453 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (95605268453 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X0XV3_approx_upper :
    barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (9140367355970197013209 / 5000000000000000000000) (0 / 1) <
      (-31973576393 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XV3_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (-31973576393 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X0XV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XV3_error).2
  have ha : ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (9140367355970197013209 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-31973576393 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XV3_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X0XV4LogArg : ℂ :=
  1 - ((Case2PointData.X0 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1

private theorem barrierCase2X0XV4_arg_eq :
    barrierCase2X0XV4LogArg = barrierComplex (607734106301 / 312500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XV4LogArg, Case2PointData.X0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X0XV4_weight_eq :
    (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XV4_error :
    |((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X0XV4LogArg).re -
      ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (369340743961475167902601 / 195312500000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (11618157 / 100000000) (0 / 1)
    barrierCase2X0XV4LogArg (1) (0) (369340743961475167902601 / 195312500000000000000000) (607734106301 / 312500000000) (0 / 1)
  have hratio : ((0 / 1) / (607734106301 / 312500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X0XV4_approx_upper :
    barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (369340743961475167902601 / 195312500000000000000000) (0 / 1) <
      (77276195268 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XV4_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (77276195268 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X0XV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XV4_error).2
  have ha : ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (369340743961475167902601 / 195312500000000000000000) (0 / 1) : ℚ) : ℝ) <
      (77276195268 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XV4_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X0XV5LogArg : ℂ :=
  1 - ((Case2PointData.X0 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1

private theorem barrierCase2X0XV5_arg_eq :
    barrierCase2X0XV5LogArg = barrierComplex (1 / 1) (93610814193 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XV5LogArg, Case2PointData.X0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X0XV5_arg_regular :
    (barrierCase2X0XV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2X0XV5LogArg).re := by
  rw [barrierCase2X0XV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X0XV5_weight_eq :
    (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XV5_error :
    |((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X0XV5LogArg).re -
      ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (1) (24387984533876370241249 / 15625000000000000000000) (-31389185807 / 218610814193) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X0XV5LogArg (0) (1) (24387984533876370241249 / 15625000000000000000000) (218610814193 / 125000000000) (-31389185807 / 125000000000)
  have hratio : ((-31389185807 / 125000000000) / (218610814193 / 125000000000) : ℚ) = (-31389185807 / 218610814193) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X0XV5_approx_upper :
    barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (1) (24387984533876370241249 / 15625000000000000000000) (-31389185807 / 218610814193) <
      (-93251437795 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XV5_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-93251437795 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X0XV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XV5_error).2
  have ha : ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (1) (24387984533876370241249 / 15625000000000000000000) (-31389185807 / 218610814193) : ℚ) : ℝ) <
      (-93251437795 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XV5_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X0XV7LogArg : ℂ :=
  1 - ((Case2PointData.X0 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1

private theorem barrierCase2X0XV7_arg_eq :
    barrierCase2X0XV7LogArg = barrierComplex (1 / 1) (21602495583 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XV7LogArg, Case2PointData.X0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X0XV7_arg_regular :
    (barrierCase2X0XV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2X0XV7LogArg).re := by
  rw [barrierCase2X0XV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X0XV7_weight_eq :
    (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XV7_error :
    |((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X0XV7LogArg).re -
      ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (1091667815413534509889 / 625000000000000000000) (-3397504417 / 46602495583) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X0XV7LogArg (0) (1) (1091667815413534509889 / 625000000000000000000) (46602495583 / 25000000000) (-3397504417 / 25000000000)
  have hratio : ((-3397504417 / 25000000000) / (46602495583 / 25000000000) : ℚ) = (-3397504417 / 46602495583) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X0XV7_approx_upper :
    barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (1091667815413534509889 / 625000000000000000000) (-3397504417 / 46602495583) <
      (-151264226370 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XV7_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-151264226370 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X0XV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XV7_error).2
  have ha : ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (1091667815413534509889 / 625000000000000000000) (-3397504417 / 46602495583) : ℚ) : ℝ) <
      (-151264226370 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XV7_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X0XV9LogArg : ℂ :=
  1 - ((Case2PointData.X0 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1

private theorem barrierCase2X0XV9_arg_eq :
    barrierCase2X0XV9LogArg = barrierComplex (1 / 1) (458452961817 / 500000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XV9LogArg, Case2PointData.X0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X0XV9_arg_regular :
    (barrierCase2X0XV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2X0XV9LogArg).re := by
  rw [barrierCase2X0XV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X0XV9_weight_eq :
    (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XV9_error :
    |((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X0XV9LogArg).re -
      ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (460179118198779659941489 / 250000000000000000000000) (-41547038183 / 958452961817) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X0XV9LogArg (0) (1) (460179118198779659941489 / 250000000000000000000000) (958452961817 / 500000000000) (-41547038183 / 500000000000)
  have hratio : ((-41547038183 / 500000000000) / (958452961817 / 500000000000) : ℚ) = (-41547038183 / 958452961817) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X0XV9_approx_upper :
    barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (460179118198779659941489 / 250000000000000000000000) (-41547038183 / 958452961817) <
      (33988820931 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XV9_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (33988820931 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X0XV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XV9_error).2
  have ha : ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (460179118198779659941489 / 250000000000000000000000) (-41547038183 / 958452961817) : ℚ) : ℝ) <
      (33988820931 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XV9_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X0XV11LogArg : ℂ :=
  1 - ((Case2PointData.X0 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1

private theorem barrierCase2X0XV11_arg_eq :
    barrierCase2X0XV11LogArg = barrierComplex (1 / 1) (295234106301 / 312500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XV11LogArg, Case2PointData.X0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X0XV11_arg_regular :
    (barrierCase2X0XV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2X0XV11LogArg).re := by
  rw [barrierCase2X0XV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X0XV11_weight_eq :
    (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XV11_error :
    |((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X0XV11LogArg).re -
      ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (184819427523350167902601 / 97656250000000000000000) (-17265893699 / 607734106301) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X0XV11LogArg (0) (1) (184819427523350167902601 / 97656250000000000000000) (607734106301 / 312500000000) (-17265893699 / 312500000000)
  have hratio : ((-17265893699 / 312500000000) / (607734106301 / 312500000000) : ℚ) = (-17265893699 / 607734106301) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X0XV11_approx_upper :
    barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (184819427523350167902601 / 97656250000000000000000) (-17265893699 / 607734106301) <
      (-78916320257 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XV11_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-78916320257 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X0XV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XV11_error).2
  have ha : ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (184819427523350167902601 / 97656250000000000000000) (-17265893699 / 607734106301) : ℚ) : ℝ) <
      (-78916320257 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XV11_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

open Case2PointData

private theorem barrierCase2X0_XP_tail_upper :
    (barrierP2Tail.map (barrierCase2XPLogTerm (X0 : ℝ))).sum <
      (-1479231423652 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [2, 4, 6, 8],
      barrierCase2XPLogTerm (X0 : ℝ) (barrierP2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XPLogTerm (X0 : ℝ) (barrierP2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierP2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X0XP2_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X0XP4_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X0XP6_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X0XP8_arg_regular
  rw [barrierP2Tail_paired_sum _ hp]
  linarith only [barrierCase2X0XP0_log_upper,
    barrierCase2X0XP1_log_upper,
    barrierCase2X0XP2_log_upper,
    barrierCase2X0XP4_log_upper,
    barrierCase2X0XP6_log_upper,
    barrierCase2X0XP8_log_upper]

private theorem barrierCase2X0_XV_tail_upper :
    (barrierV2Tail.map (barrierCase2XVLogTerm (X0 : ℝ))).sum <
      (-853513182200 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2XVLogTerm (X0 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XVLogTerm (X0 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X0XV5_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X0XV7_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X0XV9_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X0XV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2X0XV0_log_upper,
    barrierCase2X0XV1_log_upper,
    barrierCase2X0XV2_log_upper,
    barrierCase2X0XV3_log_upper,
    barrierCase2X0XV4_log_upper,
    barrierCase2X0XV5_log_upper,
    barrierCase2X0XV7_log_upper,
    barrierCase2X0XV9_log_upper,
    barrierCase2X0XV11_log_upper]

private theorem barrierCase2X0_approx_upper :
    barrierCase2XApproxRat X0 (-1) (0) (0) (2400277287 / 1250000000) (4900277287 / 2500000000) (12011331054488080369 / 6250000000000000000) + (-1479231423652 / 1000000000000) + (-853513182200 / 1000000000000) <
      (-98399 / 100000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase2XApproxRat barrierCase2XRat
  rw [barrierCase2TP_eq_explicit, barrierCase2SV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2X0_lt : barrierCase2X (X0 : ℝ) < (-98399 / 100000 : ℝ) := by
  have hx : |(X0 : ℝ)| ≤ 1 := by norm_num [X0]
  have he := (abs_lt.mp (barrierCase2X_realLog_approx_error X0 hx
    (-1) (0) (0) (2400277287 / 1250000000) (4900277287 / 2500000000) (12011331054488080369 / 6250000000000000000)
    X0_normalizations.1 X0_normalizations.2.1 X0_normalizations.2.2)).2
  have ha : ((barrierCase2XApproxRat X0 (-1) (0) (0) (2400277287 / 1250000000) (4900277287 / 2500000000) (12011331054488080369 / 6250000000000000000) : ℚ) : ℝ) +
      (-1479231423652 / 1000000000000) + (-853513182200 / 1000000000000) < (-98399 / 100000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith only [he, ha, barrierCase2X0_XP_tail_upper, barrierCase2X0_XV_tail_upper]

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoPointX1
namespace OAI

noncomputable section

namespace InternalCatalan

def barrierCase2X1XV0LogArg : ℂ :=
  1 - ((Case2PointData.X1 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1

private theorem barrierCase2X1XV0_arg_eq :
    barrierCase2X1XV0LogArg = barrierComplex (889420607 / 3125000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XV0LogArg, Case2PointData.X1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X1XV0_weight_eq :
    (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XV0_error :
    |((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X1XV0LogArg).re -
      ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-4) (0) (791069016156248449 / 610351562500000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (15199211 / 100000000) (0 / 1)
    barrierCase2X1XV0LogArg (-4) (0) (791069016156248449 / 610351562500000000) (889420607 / 3125000000) (0 / 1)
  have hratio : ((0 / 1) / (889420607 / 3125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X1XV0_approx_upper :
    barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-4) (0) (791069016156248449 / 610351562500000000) (0 / 1) <
      (-190996221123 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XV0_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-190996221123 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X1XV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XV0_error).2
  have ha : ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-4) (0) (791069016156248449 / 610351562500000000) (0 / 1) : ℚ) : ℝ) <
      (-190996221123 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XV0_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X1XV1LogArg : ℂ :=
  1 - ((Case2PointData.X1 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1

private theorem barrierCase2X1XV1_arg_eq :
    barrierCase2X1XV1LogArg = barrierComplex (1105761821 / 7812500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XV1LogArg, Case2PointData.X1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X1XV1_weight_eq :
    (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XV1_error :
    |((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X1XV1LogArg).re -
      ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-6) (0) (1222709204781236041 / 953674316406250000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2225831 / 50000000) (0 / 1)
    barrierCase2X1XV1LogArg (-6) (0) (1222709204781236041 / 953674316406250000) (1105761821 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (1105761821 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X1XV1_approx_upper :
    barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-6) (0) (1222709204781236041 / 953674316406250000) (0 / 1) <
      (-87038471930 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XV1_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-87038471930 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X1XV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XV1_error).2
  have ha : ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-6) (0) (1222709204781236041 / 953674316406250000) (0 / 1) : ℚ) : ℝ) <
      (-87038471930 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XV1_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X1XV2LogArg : ℂ :=
  1 - ((Case2PointData.X1 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1

private theorem barrierCase2X1XV2_arg_eq :
    barrierCase2X1XV2LogArg = barrierComplex (55841373323 / 31250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XV2LogArg, Case2PointData.X1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X1XV2_weight_eq :
    (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XV2_error :
    |((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X1XV2LogArg).re -
      ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (3118258974598656062329 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (1272699 / 50000000) (0 / 1)
    barrierCase2X1XV2LogArg (1) (0) (3118258974598656062329 / 1953125000000000000000) (55841373323 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (55841373323 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X1XV2_approx_upper :
    barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (3118258974598656062329 / 1953125000000000000000) (0 / 1) <
      (14775925325 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XV2_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (14775925325 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X1XV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XV2_error).2
  have ha : ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (3118258974598656062329 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ) <
      (14775925325 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XV2_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X1XV3LogArg : ℂ :=
  1 - ((Case2PointData.X1 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1

private theorem barrierCase2X1XV3_arg_eq :
    barrierCase2X1XV3LogArg = barrierComplex (92476008467 / 50000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XV3LogArg, Case2PointData.X1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X1XV3_weight_eq :
    (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XV3_error :
    |((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X1XV3LogArg).re -
      ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (8551812141988655690089 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2466317 / 50000000) (0 / 1)
    barrierCase2X1XV3LogArg (1) (0) (8551812141988655690089 / 5000000000000000000000) (92476008467 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (92476008467 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X1XV3_approx_upper :
    barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (8551812141988655690089 / 5000000000000000000000) (0 / 1) <
      (-30332060666 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XV3_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (-30332060666 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X1XV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XV3_error).2
  have ha : ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (8551812141988655690089 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-30332060666 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XV3_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X1XV4LogArg : ℂ :=
  1 - ((Case2PointData.X1 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1

private theorem barrierCase2X1XV4_arg_eq :
    barrierCase2X1XV4LogArg = barrierComplex (587476265339 / 312500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XV4LogArg, Case2PointData.X1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X1XV4_weight_eq :
    (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XV4_error :
    |((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X1XV4LogArg).re -
      ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (345128362336659132784921 / 195312500000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (11618157 / 100000000) (0 / 1)
    barrierCase2X1XV4LogArg (1) (0) (345128362336659132784921 / 195312500000000000000000) (587476265339 / 312500000000) (0 / 1)
  have hratio : ((0 / 1) / (587476265339 / 312500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X1XV4_approx_upper :
    barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (345128362336659132784921 / 195312500000000000000000) (0 / 1) <
      (73337452368 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XV4_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (73337452368 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X1XV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XV4_error).2
  have ha : ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (345128362336659132784921 / 195312500000000000000000) (0 / 1) : ℚ) : ℝ) <
      (73337452368 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XV4_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X1XV5LogArg : ℂ :=
  1 - ((Case2PointData.X1 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1

private theorem barrierCase2X1XV5_arg_eq :
    barrierCase2X1XV5LogArg = barrierComplex (1 / 1) (87187596327 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XV5LogArg, Case2PointData.X1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X1XV5_arg_regular :
    (barrierCase2X1XV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2X1XV5LogArg).re := by
  rw [barrierCase2X1XV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X1XV5_weight_eq :
    (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XV5_error :
    |((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X1XV5LogArg).re -
      ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (1) (23226676953279903890929 / 15625000000000000000000) (-37812403673 / 212187596327) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X1XV5LogArg (0) (1) (23226676953279903890929 / 15625000000000000000000) (212187596327 / 125000000000) (-37812403673 / 125000000000)
  have hratio : ((-37812403673 / 125000000000) / (212187596327 / 125000000000) : ℚ) = (-37812403673 / 212187596327) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X1XV5_approx_upper :
    barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (1) (23226676953279903890929 / 15625000000000000000000) (-37812403673 / 212187596327) <
      (-90087374639 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XV5_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-90087374639 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X1XV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XV5_error).2
  have ha : ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (1) (23226676953279903890929 / 15625000000000000000000) (-37812403673 / 212187596327) : ℚ) : ℝ) <
      (-90087374639 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XV5_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X1XV7LogArg : ℂ :=
  1 - ((Case2PointData.X1 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1

private theorem barrierCase2X1XV7_arg_eq :
    barrierCase2X1XV7LogArg = barrierComplex (1 / 1) (20120214537 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XV7LogArg, Case2PointData.X1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X1XV7_arg_regular :
    (barrierCase2X1XV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2X1XV7LogArg).re := by
  rw [barrierCase2X1XV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X1XV7_weight_eq :
    (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XV7_error :
    |((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X1XV7LogArg).re -
      ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (1029823033014906124369 / 625000000000000000000) (-4879785463 / 45120214537) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X1XV7LogArg (0) (1) (1029823033014906124369 / 625000000000000000000) (45120214537 / 25000000000) (-4879785463 / 25000000000)
  have hratio : ((-4879785463 / 25000000000) / (45120214537 / 25000000000) : ℚ) = (-4879785463 / 45120214537) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X1XV7_approx_upper :
    barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (1029823033014906124369 / 625000000000000000000) (-4879785463 / 45120214537) <
      (-141418196713 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XV7_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-141418196713 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X1XV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XV7_error).2
  have ha : ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (1029823033014906124369 / 625000000000000000000) (-4879785463 / 45120214537) : ℚ) : ℝ) <
      (-141418196713 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XV7_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X1XV9LogArg : ℂ :=
  1 - ((Case2PointData.X1 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1

private theorem barrierCase2X1XV9_arg_eq :
    barrierCase2X1XV9LogArg = barrierComplex (1 / 1) (426995664063 / 500000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XV9LogArg, Case2PointData.X1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X1XV9_arg_regular :
    (barrierCase2X1XV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2X1XV9LogArg).re := by
  rw [barrierCase2X1XV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X1XV9_weight_eq :
    (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XV9_error :
    |((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X1XV9LogArg).re -
      ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (432325297128602349667969 / 250000000000000000000000) (-73004335937 / 926995664063) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X1XV9LogArg (0) (1) (432325297128602349667969 / 250000000000000000000000) (926995664063 / 500000000000) (-73004335937 / 500000000000)
  have hratio : ((-73004335937 / 500000000000) / (926995664063 / 500000000000) : ℚ) = (-73004335937 / 926995664063) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X1XV9_approx_upper :
    barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (432325297128602349667969 / 250000000000000000000000) (-73004335937 / 926995664063) <
      (32932879939 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XV9_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (32932879939 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X1XV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XV9_error).2
  have ha : ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (432325297128602349667969 / 250000000000000000000000) (-73004335937 / 926995664063) : ℚ) : ℝ) <
      (32932879939 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XV9_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X1XV11LogArg : ℂ :=
  1 - ((Case2PointData.X1 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1

private theorem barrierCase2X1XV11_arg_eq :
    barrierCase2X1XV11LogArg = barrierComplex (1 / 1) (274976265339 / 312500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XV11LogArg, Case2PointData.X1, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X1XV11_arg_regular :
    (barrierCase2X1XV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2X1XV11LogArg).re := by
  rw [barrierCase2X1XV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X1XV11_weight_eq :
    (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XV11_error :
    |((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X1XV11LogArg).re -
      ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (173268196499784132784921 / 97656250000000000000000) (-37523734661 / 587476265339) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X1XV11LogArg (0) (1) (173268196499784132784921 / 97656250000000000000000) (587476265339 / 312500000000) (-37523734661 / 312500000000)
  have hratio : ((-37523734661 / 312500000000) / (587476265339 / 312500000000) : ℚ) = (-37523734661 / 587476265339) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X1XV11_approx_upper :
    barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (173268196499784132784921 / 97656250000000000000000) (-37523734661 / 587476265339) <
      (-75406010027 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XV11_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-75406010027 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X1XV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XV11_error).2
  have ha : ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (173268196499784132784921 / 97656250000000000000000) (-37523734661 / 587476265339) : ℚ) : ℝ) <
      (-75406010027 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XV11_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

open Case2PointData

private theorem barrierCase2X1_XP_tail_upper :
    (barrierP2Tail.map (barrierCase2XPLogTerm (X1 : ℝ))).sum <
      (-1366204345442 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [2, 4, 6, 8],
      barrierCase2XPLogTerm (X1 : ℝ) (barrierP2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XPLogTerm (X1 : ℝ) (barrierP2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierP2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X1XP2_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X1XP4_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X1XP6_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X1XP8_arg_regular
  rw [barrierP2Tail_paired_sum _ hp]
  linarith only [barrierCase2X1XP0_log_upper,
    barrierCase2X1XP1_log_upper,
    barrierCase2X1XP2_log_upper,
    barrierCase2X1XP4_log_upper,
    barrierCase2X1XP6_log_upper,
    barrierCase2X1XP8_log_upper]

private theorem barrierCase2X1_XV_tail_upper :
    (barrierV2Tail.map (barrierCase2XVLogTerm (X1 : ℝ))).sum <
      (-768210778906 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2XVLogTerm (X1 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XVLogTerm (X1 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X1XV5_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X1XV7_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X1XV9_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X1XV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2X1XV0_log_upper,
    barrierCase2X1XV1_log_upper,
    barrierCase2X1XV2_log_upper,
    barrierCase2X1XV3_log_upper,
    barrierCase2X1XV4_log_upper,
    barrierCase2X1XV5_log_upper,
    barrierCase2X1XV7_log_upper,
    barrierCase2X1XV9_log_upper,
    barrierCase2X1XV11_log_upper]

private theorem barrierCase2X1_approx_upper :
    barrierCase2XApproxRat X1 (-1) (0) (0) (2235579393 / 1250000000) (4735579393 / 2500000000) (11247815222406248449 / 6250000000000000000) + (-1366204345442 / 1000000000000) + (-768210778906 / 1000000000000) <
      (-98399 / 100000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase2XApproxRat barrierCase2XRat
  rw [barrierCase2TP_eq_explicit, barrierCase2SV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2X1_lt : barrierCase2X (X1 : ℝ) < (-98399 / 100000 : ℝ) := by
  have hx : |(X1 : ℝ)| ≤ 1 := by norm_num [X1]
  have he := (abs_lt.mp (barrierCase2X_realLog_approx_error X1 hx
    (-1) (0) (0) (2235579393 / 1250000000) (4735579393 / 2500000000) (11247815222406248449 / 6250000000000000000)
    X1_normalizations.1 X1_normalizations.2.1 X1_normalizations.2.2)).2
  have ha : ((barrierCase2XApproxRat X1 (-1) (0) (0) (2235579393 / 1250000000) (4735579393 / 2500000000) (11247815222406248449 / 6250000000000000000) : ℚ) : ℝ) +
      (-1366204345442 / 1000000000000) + (-768210778906 / 1000000000000) < (-98399 / 100000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith only [he, ha, barrierCase2X1_XP_tail_upper, barrierCase2X1_XV_tail_upper]

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoPointX2
namespace OAI

noncomputable section

namespace InternalCatalan

def barrierCase2X2XV0LogArg : ℂ :=
  1 - ((Case2PointData.X2 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1

private theorem barrierCase2X2XV0_arg_eq :
    barrierCase2X2XV0LogArg = barrierComplex (4891694367 / 12500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XV0LogArg, Case2PointData.X2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X2XV0_weight_eq :
    (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XV0_error :
    |((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X2XV0LogArg).re -
      ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-3) (0) (23928673780139530689 / 19531250000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (15199211 / 100000000) (0 / 1)
    barrierCase2X2XV0LogArg (-3) (0) (23928673780139530689 / 19531250000000000000) (4891694367 / 12500000000) (0 / 1)
  have hratio : ((0 / 1) / (4891694367 / 12500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X2XV0_approx_upper :
    barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-3) (0) (23928673780139530689 / 19531250000000000000) (0 / 1) <
      (-142597463167 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XV0_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-142597463167 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X2XV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XV0_error).2
  have ha : ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-3) (0) (23928673780139530689 / 19531250000000000000) (0 / 1) : ℚ) : ℝ) <
      (-142597463167 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XV0_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X2XV1LogArg : ℂ :=
  1 - ((Case2PointData.X2 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1

private theorem barrierCase2X2XV1_arg_eq :
    barrierCase2X2XV1LogArg = barrierComplex (8425083101 / 31250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XV1LogArg, Case2PointData.X2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X2XV1_weight_eq :
    (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XV1_error :
    |((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X2XV1LogArg).re -
      ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-4) (0) (70982025258755776201 / 61035156250000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2225831 / 50000000) (0 / 1)
    barrierCase2X2XV1LogArg (-4) (0) (70982025258755776201 / 61035156250000000000) (8425083101 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (8425083101 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X2XV1_approx_upper :
    barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-4) (0) (70982025258755776201 / 61035156250000000000) (0 / 1) <
      (-58352654213 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XV1_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-58352654213 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X2XV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XV1_error).2
  have ha : ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-4) (0) (70982025258755776201 / 61035156250000000000) (0 / 1) : ℚ) : ℝ) <
      (-58352654213 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XV1_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X2XV2LogArg : ℂ :=
  1 - ((Case2PointData.X2 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1

private theorem barrierCase2X2XV2_arg_eq :
    barrierCase2X2XV2LogArg = barrierComplex (208691361963 / 125000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XV2LogArg, Case2PointData.X2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X2XV2_weight_eq :
    (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XV2_error :
    |((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X2XV2LogArg).re -
      ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (43552084557971883213369 / 31250000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (1272699 / 50000000) (0 / 1)
    barrierCase2X2XV2LogArg (1) (0) (43552084557971883213369 / 31250000000000000000000) (208691361963 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (208691361963 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X2XV2_approx_upper :
    barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (43552084557971883213369 / 31250000000000000000000) (0 / 1) <
      (13046251285 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XV2_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (13046251285 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X2XV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XV2_error).2
  have ha : ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (43552084557971883213369 / 31250000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (13046251285 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XV2_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X2XV3LogArg : ℂ :=
  1 - ((Case2PointData.X2 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1

private theorem barrierCase2X2XV3_arg_eq :
    barrierCase2X2XV3LogArg = barrierComplex (344557807027 / 200000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XV3LogArg, Case2PointData.X2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X2XV3_weight_eq :
    (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XV3_error :
    |((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X2XV3LogArg).re -
      ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (118720082383255370578729 / 80000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2466317 / 50000000) (0 / 1)
    barrierCase2X2XV3LogArg (1) (0) (118720082383255370578729 / 80000000000000000000000) (344557807027 / 200000000000) (0 / 1)
  have hratio : ((0 / 1) / (344557807027 / 200000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X2XV3_approx_upper :
    barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (118720082383255370578729 / 80000000000000000000000) (0 / 1) <
      (-26830791821 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XV3_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (-26830791821 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X2XV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XV3_error).2
  have ha : ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (118720082383255370578729 / 80000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-26830791821 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XV3_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X2XV4LogArg : ℂ :=
  1 - ((Case2PointData.X2 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1

private theorem barrierCase2X2XV4_arg_eq :
    barrierCase2X2XV4LogArg = barrierComplex (2185821592859 / 1250000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XV4LogArg, Case2PointData.X2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X2XV4_weight_eq :
    (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XV4_error :
    |((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X2XV4LogArg).re -
      ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (4777816035808655959793881 / 3125000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (11618157 / 100000000) (0 / 1)
    barrierCase2X2XV4LogArg (1) (0) (4777816035808655959793881 / 3125000000000000000000000) (2185821592859 / 1250000000000) (0 / 1)
  have hratio : ((0 / 1) / (2185821592859 / 1250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X2XV4_approx_upper :
    barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (4777816035808655959793881 / 3125000000000000000000000) (0 / 1) <
      (64927863778 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XV4_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (64927863778 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X2XV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XV4_error).2
  have ha : ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (4777816035808655959793881 / 3125000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (64927863778 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XV4_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X2XV5LogArg : ℂ :=
  1 - ((Case2PointData.X2 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1

private theorem barrierCase2X2XV5_arg_eq :
    barrierCase2X2XV5LogArg = barrierComplex (1 / 1) (296723919687 / 500000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XV5LogArg, Case2PointData.X2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X2XV5_arg_regular :
    (barrierCase2X2XV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2X2XV5LogArg).re := by
  rw [barrierCase2X2XV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X2XV5_weight_eq :
    (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XV5_error :
    |((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X2XV5LogArg).re -
      ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (1) (338045084514417226177969 / 250000000000000000000000) (-203276080313 / 796723919687) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X2XV5LogArg (0) (1) (338045084514417226177969 / 250000000000000000000000) (796723919687 / 500000000000) (-203276080313 / 500000000000)
  have hratio : ((-203276080313 / 500000000000) / (796723919687 / 500000000000) : ℚ) = (-203276080313 / 796723919687) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X2XV5_approx_upper :
    barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (1) (338045084514417226177969 / 250000000000000000000000) (-203276080313 / 796723919687) <
      (-82415178458 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XV5_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-82415178458 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X2XV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XV5_error).2
  have ha : ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (1) (338045084514417226177969 / 250000000000000000000000) (-203276080313 / 796723919687) : ℚ) : ℝ) <
      (-82415178458 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XV5_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X2XV7LogArg : ℂ :=
  1 - ((Case2PointData.X2 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1

private theorem barrierCase2X2XV7_arg_eq :
    barrierCase2X2XV7LogArg = barrierComplex (1 / 1) (68474750697 / 100000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XV7LogArg, Case2PointData.X2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X2XV7_arg_regular :
    (barrierCase2X2XV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2X2XV7LogArg).re := by
  rw [barrierCase2X2XV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X2XV7_weight_eq :
    (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XV7_error :
    |((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X2XV7LogArg).re -
      ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (14688791483016301985809 / 10000000000000000000000) (-31525249303 / 168474750697) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X2XV7LogArg (0) (1) (14688791483016301985809 / 10000000000000000000000) (168474750697 / 100000000000) (-31525249303 / 100000000000)
  have hratio : ((-31525249303 / 100000000000) / (168474750697 / 100000000000) : ℚ) = (-31525249303 / 168474750697) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X2XV7_approx_upper :
    barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (14688791483016301985809 / 10000000000000000000000) (-31525249303 / 168474750697) <
      (-120755719726 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XV7_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-120755719726 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X2XV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XV7_error).2
  have ha : ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (14688791483016301985809 / 10000000000000000000000) (-31525249303 / 168474750697) : ℚ) : ℝ) <
      (-120755719726 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XV7_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X2XV9LogArg : ℂ :=
  1 - ((Case2PointData.X2 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1

private theorem barrierCase2X2XV9_arg_eq :
    barrierCase2X2XV9LogArg = barrierComplex (1 / 1) (1453186375903 / 2000000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XV9LogArg, Case2PointData.X2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X2XV9_arg_regular :
    (barrierCase2X2XV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2X2XV9LogArg).re := by
  rw [barrierCase2X2XV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X2XV9_weight_eq :
    (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XV9_error :
    |((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X2XV9LogArg).re -
      ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (6111750643110095219065409 / 4000000000000000000000000) (-546813624097 / 3453186375903) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X2XV9LogArg (0) (1) (6111750643110095219065409 / 4000000000000000000000000) (3453186375903 / 2000000000000) (-546813624097 / 2000000000000)
  have hratio : ((-546813624097 / 2000000000000) / (3453186375903 / 2000000000000) : ℚ) = (-546813624097 / 3453186375903) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X2XV9_approx_upper :
    barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (6111750643110095219065409 / 4000000000000000000000000) (-546813624097 / 3453186375903) <
      (30331627232 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XV9_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (30331627232 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X2XV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XV9_error).2
  have ha : ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (6111750643110095219065409 / 4000000000000000000000000) (-546813624097 / 3453186375903) : ℚ) : ℝ) <
      (30331627232 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XV9_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X2XV11LogArg : ℂ :=
  1 - ((Case2PointData.X2 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1

private theorem barrierCase2X2XV11_arg_eq :
    barrierCase2X2XV11LogArg = barrierComplex (1 / 1) (935821592859 / 1250000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XV11LogArg, Case2PointData.X2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X2XV11_arg_regular :
    (barrierCase2X2XV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2X2XV11LogArg).re := by
  rw [barrierCase2X2XV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X2XV11_weight_eq :
    (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XV11_error :
    |((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X2XV11LogArg).re -
      ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (2438262053661155959793881 / 1562500000000000000000000) (-314178407141 / 2185821592859) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X2XV11LogArg (0) (1) (2438262053661155959793881 / 1562500000000000000000000) (2185821592859 / 1250000000000) (-314178407141 / 1250000000000)
  have hratio : ((-314178407141 / 1250000000000) / (2185821592859 / 1250000000000) : ℚ) = (-314178407141 / 2185821592859) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X2XV11_approx_upper :
    barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (2438262053661155959793881 / 1562500000000000000000000) (-314178407141 / 2185821592859) <
      (-67491081131 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XV11_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-67491081131 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X2XV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XV11_error).2
  have ha : ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (2438262053661155959793881 / 1562500000000000000000000) (-314178407141 / 2185821592859) : ℚ) : ℝ) <
      (-67491081131 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XV11_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

open Case2PointData

private theorem barrierCase2X2_XP_tail_upper :
    (barrierP2Tail.map (barrierCase2XPLogTerm (X2 : ℝ))).sum <
      (-1113908580915 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [2, 4, 6, 8],
      barrierCase2XPLogTerm (X2 : ℝ) (barrierP2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XPLogTerm (X2 : ℝ) (barrierP2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierP2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X2XP2_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X2XP4_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X2XP6_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X2XP8_arg_regular
  rw [barrierP2Tail_paired_sum _ hp]
  linarith only [barrierCase2X2XP0_log_upper,
    barrierCase2X2XP1_log_upper,
    barrierCase2X2XP2_log_upper,
    barrierCase2X2XP4_log_upper,
    barrierCase2X2XP6_log_upper,
    barrierCase2X2XP8_log_upper]

private theorem barrierCase2X2_XV_tail_upper :
    (barrierV2Tail.map (barrierCase2XVLogTerm (X2 : ℝ))).sum <
      (-630467498304 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2XVLogTerm (X2 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XVLogTerm (X2 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X2XV5_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X2XV7_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X2XV9_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X2XV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2X2XV0_log_upper,
    barrierCase2X2XV1_log_upper,
    barrierCase2X2XV2_log_upper,
    barrierCase2X2XV3_log_upper,
    barrierCase2X2XV4_log_upper,
    barrierCase2X2XV5_log_upper,
    barrierCase2X2XV7_log_upper,
    barrierCase2X2XV9_log_upper,
    barrierCase2X2XV11_log_upper]

private theorem barrierCase2X2_approx_upper :
    barrierCase2XApproxRat X2 (-1) (0) (0) (7608305633 / 5000000000) (17608305633 / 10000000000) (157886314605139530689 / 100000000000000000000) + (-1113908580915 / 1000000000000) + (-630467498304 / 1000000000000) <
      (-98399 / 100000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase2XApproxRat barrierCase2XRat
  rw [barrierCase2TP_eq_explicit, barrierCase2SV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2X2_lt : barrierCase2X (X2 : ℝ) < (-98399 / 100000 : ℝ) := by
  have hx : |(X2 : ℝ)| ≤ 1 := by norm_num [X2]
  have he := (abs_lt.mp (barrierCase2X_realLog_approx_error X2 hx
    (-1) (0) (0) (7608305633 / 5000000000) (17608305633 / 10000000000) (157886314605139530689 / 100000000000000000000)
    X2_normalizations.1 X2_normalizations.2.1 X2_normalizations.2.2)).2
  have ha : ((barrierCase2XApproxRat X2 (-1) (0) (0) (7608305633 / 5000000000) (17608305633 / 10000000000) (157886314605139530689 / 100000000000000000000) : ℚ) : ℝ) +
      (-1113908580915 / 1000000000000) + (-630467498304 / 1000000000000) < (-98399 / 100000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith only [he, ha, barrierCase2X2_XP_tail_upper, barrierCase2X2_XV_tail_upper]

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Split.Fine
/-! Glue for the split of OpenAI's Catalan development (not OpenAI code): finer groups, and the
coarser published statements recovered from them. -/

namespace OAI

namespace InternalCatalan



























theorem barrierCase2X_table_left_lt_A1 :
    ∀ m ∈ ([-9601109148, -8942317572, -7608305633] : List ℤ),
      barrierCase2X (barrierBracketLeft m : ℝ) < (-98399 / 100000 : ℝ) := by
  intro m hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · convert barrierCase2X0_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.X0]
  · convert barrierCase2X1_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.X1]
  · convert barrierCase2X2_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.X2]














end InternalCatalan

end OAI

end

section
open OAI.InternalCatalan

theorem solution :
    ∀ m ∈ ([-9601109148, -8942317572, -7608305633] : List ℤ),
      barrierCase2X (barrierBracketLeft m : ℝ) < (-98399 / 100000 : ℝ) := by
  first
  | exact @OAI.InternalCatalan.barrierCase2X_table_left_lt_A1
  | (apply OAI.InternalCatalan.barrierCase2X_table_left_lt_A1 <;> assumption)

end
