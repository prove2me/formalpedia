-- Prove2me | solution 1 for OAI.InternalCatalan.barrierCase2X_table_left_lt_A2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T20:59:25.223628+00:00
-- url     : https://prove2.me/submissions/18f1daa6-110a-4fb9-a1a4-d72055fe538a

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




def X3 : ℚ := (-3251697397 / 5000000000)

def X4 : ℚ := (-1037172813 / 2000000000)

def X5 : ℚ := (-2007817079 / 5000000000)




































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




theorem X3_normalizations :
    FixedLogNormalization |(X3 : ℝ)| (-1) (3251697397 / 2500000000) ∧
    FixedLogNormalization (1 - (X3 : ℝ)) (0) (8251697397 / 5000000000) ∧
    FixedLogNormalization (1 + (X3 : ℝ) ^ 2) (0) (35573535961656575609 / 25000000000000000000) := by
  norm_num [FixedLogNormalization, X3, Set.mem_Icc]

theorem X4_normalizations :
    FixedLogNormalization |(X4 : ℝ)| (-1) (1037172813 / 1000000000) ∧
    FixedLogNormalization (1 - (X4 : ℝ)) (0) (3037172813 / 2000000000) ∧
    FixedLogNormalization (1 + (X4 : ℝ) ^ 2) (0) (5075727444026332969 / 4000000000000000000) := by
  norm_num [FixedLogNormalization, X4, Set.mem_Icc]

theorem X5_normalizations :
    FixedLogNormalization |(X5 : ℝ)| (-2) (2007817079 / 1250000000) ∧
    FixedLogNormalization (1 - (X5 : ℝ)) (0) (7007817079 / 5000000000) ∧
    FixedLogNormalization (1 + (X5 : ℝ) ^ 2) (0) (29031329422724092241 / 25000000000000000000) := by
  norm_num [FixedLogNormalization, X5, Set.mem_Icc]
































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
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoLogsX3Group0
namespace OAI

noncomputable section
namespace InternalCatalan

def barrierCase2X3XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X3 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X3XP0_arg_eq :
    barrierCase2X3XP0LogArg = barrierComplex (141403855749 / 50000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XP0LogArg, Case2PointData.X3, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X3XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X3XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (2) (0) (19995050420684000351001 / 10000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X3XP0LogArg (2) (0) (19995050420684000351001 / 10000000000000000000000) (141403855749 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (141403855749 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X3XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (2) (0) (19995050420684000351001 / 10000000000000000000000) (0 / 1) <
      (-194164536672 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X3 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (-194164536672 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X3XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (2) (0) (19995050420684000351001 / 10000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-194164536672 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XP0_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X3XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X3 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X3XP1_arg_eq :
    barrierCase2X3XP1LogArg = barrierComplex (388279777659 / 125000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XP1LogArg, Case2PointData.X3, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X3XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X3XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (150761185738922475520281 / 125000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X3XP1LogArg (3) (0) (150761185738922475520281 / 125000000000000000000000) (388279777659 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (388279777659 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X3XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (150761185738922475520281 / 125000000000000000000000) (0 / 1) <
      (-48544257915 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X3 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (-48544257915 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X3XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (150761185738922475520281 / 125000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-48544257915 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XP1_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X3XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X3 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X3XP2_arg_eq :
    barrierCase2X3XP2LogArg = barrierComplex (51 / 100) (22761881779 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XP2LogArg, Case2PointData.X3, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X3XP2_arg_regular :
    (barrierCase2X3XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X3XP2LogArg).re := by
  rw [barrierCase2X3XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X3XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X3XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (1) (680665762121172204841 / 625000000000000000000) (10011881779 / 35511881779) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X3XP2LogArg (0) (1) (680665762121172204841 / 625000000000000000000) (35511881779 / 25000000000) (10011881779 / 25000000000)
  have hratio : ((10011881779 / 25000000000) / (35511881779 / 25000000000) : ℚ) = (10011881779 / 35511881779) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X3XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (1) (680665762121172204841 / 625000000000000000000) (10011881779 / 35511881779) <
      (-366556874260 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X3 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (-366556874260 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X3XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (1) (680665762121172204841 / 625000000000000000000) (10011881779 / 35511881779) : ℚ) : ℝ) <
      (-366556874260 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XP2_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X3XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X3 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X3XP4_arg_eq :
    barrierCase2X3XP4LogArg = barrierComplex (111 / 400) (55278855749 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XP4LogArg, Case2PointData.X3, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X3XP4_arg_regular :
    (barrierCase2X3XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X3XP4LogArg).re := by
  rw [barrierCase2X3XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X3XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X3XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (0) (2) (3248267517918750351001 / 2500000000000000000000) (-13875000000 / 55278855749) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X3XP4LogArg (0) (2) (3248267517918750351001 / 2500000000000000000000) (55278855749 / 25000000000) (-111 / 200)
  have hratio : ((-111 / 200) / (55278855749 / 25000000000) : ℚ) = (-13875000000 / 55278855749) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X3XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (0) (2) (3248267517918750351001 / 2500000000000000000000) (-13875000000 / 55278855749) <
      (77915215782 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X3 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (77915215782 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X3XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (0) (2) (3248267517918750351001 / 2500000000000000000000) (-13875000000 / 55278855749) : ℚ) : ℝ) <
      (77915215782 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XP4_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X3XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X3 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X3XP6_arg_eq :
    barrierCase2X3XP6LogArg = barrierComplex (176079040131 / 625000000000) (85369040131 / 62500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XP6LogArg, Case2PointData.X3, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X3XP6_arg_regular :
    (barrierCase2X3XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X3XP6LogArg).re := by
  rw [barrierCase2X3XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X3XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X3XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (0) (2) (759791129662283158213261 / 390625000000000000000000) (-176079040131 / 853690401310) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X3XP6LogArg (0) (2) (759791129662283158213261 / 390625000000000000000000) (85369040131 / 31250000000) (-176079040131 / 312500000000)
  have hratio : ((-176079040131 / 312500000000) / (85369040131 / 31250000000) : ℚ) = (-176079040131 / 853690401310) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X3XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (0) (2) (759791129662283158213261 / 390625000000000000000000) (-176079040131 / 853690401310) <
      (111353046691 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X3 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (111353046691 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X3XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (0) (2) (759791129662283158213261 / 390625000000000000000000) (-176079040131 / 853690401310) : ℚ) : ℝ) <
      (111353046691 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XP6_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X3XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X3 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X3XP8_arg_eq :
    barrierCase2X3XP8LogArg = barrierComplex (26500959869 / 625000000000) (64209040131 / 62500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XP8LogArg, Case2PointData.X3, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X3XP8_arg_regular :
    (barrierCase2X3XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X3XP8LogArg).re := by
  rw [barrierCase2X3XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X3XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X3XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (0) (2) (412982384328415198213261 / 390625000000000000000000) (-26500959869 / 642090401310) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X3XP8LogArg (0) (2) (412982384328415198213261 / 390625000000000000000000) (64209040131 / 31250000000) (-26500959869 / 312500000000)
  have hratio : ((-26500959869 / 312500000000) / (64209040131 / 31250000000) : ℚ) = (-26500959869 / 642090401310) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X3XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (0) (2) (412982384328415198213261 / 390625000000000000000000) (-26500959869 / 642090401310) <
      (-139641427292 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X3 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (-139641427292 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X3XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (0) (2) (412982384328415198213261 / 390625000000000000000000) (-26500959869 / 642090401310) : ℚ) : ℝ) <
      (-139641427292 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XP8_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoLogsX4Group0
namespace OAI

noncomputable section
namespace InternalCatalan

def barrierCase2X4XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X4 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X4XP0_arg_eq :
    barrierCase2X4XP0LogArg = barrierComplex (52081937821 / 20000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XP0LogArg, Case2PointData.X4, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X4XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X4XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (2) (0) (2712528247190510228041 / 1600000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X4XP0LogArg (2) (0) (2712528247190510228041 / 1600000000000000000000) (52081937821 / 20000000000) (0 / 1)
  have hratio : ((0 / 1) / (52081937821 / 20000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X4XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (2) (0) (2712528247190510228041 / 1600000000000000000000) (0 / 1) <
      (-178754020753 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X4 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (-178754020753 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X4XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (2) (0) (2712528247190510228041 / 1600000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-178754020753 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XP0_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X4XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X4 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X4XP1_arg_eq :
    barrierCase2X4XP1LogArg = barrierComplex (142927122211 / 50000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XP1LogArg, Case2PointData.X4, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X4XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X4XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (20428162263518129528521 / 20000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X4XP1LogArg (3) (0) (20428162263518129528521 / 20000000000000000000000) (142927122211 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (142927122211 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X4XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (20428162263518129528521 / 20000000000000000000000) (0 / 1) <
      (-44985046020 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X4 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (-44985046020 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X4XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (20428162263518129528521 / 20000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-44985046020 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XP1_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X4XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X4 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X4XP2_arg_eq :
    barrierCase2X4XP2LogArg = barrierComplex (51 / 100) (7260209691 / 10000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XP2LogArg, Case2PointData.X4, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X4XP2_arg_regular :
    (barrierCase2X4XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X4XP2LogArg).re := by
  rw [barrierCase2X4XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X4XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X4XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-1) (1) (78720644757290315481 / 50000000000000000000) (720069897 / 4120069897) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X4XP2LogArg (-1) (1) (78720644757290315481 / 50000000000000000000) (12360209691 / 10000000000) (2160209691 / 10000000000)
  have hratio : ((2160209691 / 10000000000) / (12360209691 / 10000000000) : ℚ) = (720069897 / 4120069897) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X4XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-1) (1) (78720644757290315481 / 50000000000000000000) (720069897 / 4120069897) <
      (-226519279066 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X4 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (-226519279066 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X4XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-1) (1) (78720644757290315481 / 50000000000000000000) (720069897 / 4120069897) : ℚ) : ℝ) <
      (-226519279066 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XP2_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X4XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X4 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X4XP4_arg_eq :
    barrierCase2X4XP4LogArg = barrierComplex (111 / 400) (17631937821 / 20000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XP4LogArg, Case2PointData.X4, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X4XP4_arg_regular :
    (barrierCase2X4XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X4XP4LogArg).re := by
  rw [barrierCase2X4XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X4XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X4XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-1) (2) (341687731323610228041 / 200000000000000000000) (-1850000000 / 5877312607) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X4XP4LogArg (-1) (2) (341687731323610228041 / 200000000000000000000) (17631937821 / 10000000000) (-111 / 200)
  have hratio : ((-111 / 200) / (17631937821 / 10000000000) : ℚ) = (-1850000000 / 5877312607) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X4XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-1) (2) (341687731323610228041 / 200000000000000000000) (-1850000000 / 5877312607) <
      (76954522124 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X4 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (76954522124 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X4XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-1) (2) (341687731323610228041 / 200000000000000000000) (-1850000000 / 5877312607) : ℚ) : ℝ) <
      (76954522124 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XP4_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X4XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X4 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X4XP6_arg_eq :
    barrierCase2X4XP6LogArg = barrierComplex (64370974699 / 250000000000) (28086974699 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XP6LogArg, Case2PointData.X4, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X4XP6_arg_regular :
    (barrierCase2X4XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X4XP6LogArg).re := by
  rw [barrierCase2X4XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X4XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X4XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (0) (2) (83031437157925912200701 / 62500000000000000000000) (-64370974699 / 280869746990) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X4XP6LogArg (0) (2) (83031437157925912200701 / 62500000000000000000000) (28086974699 / 12500000000) (-64370974699 / 125000000000)
  have hratio : ((-64370974699 / 125000000000) / (28086974699 / 12500000000) : ℚ) = (-64370974699 / 280869746990) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X4XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (0) (2) (83031437157925912200701 / 62500000000000000000000) (-64370974699 / 280869746990) <
      (115547972121 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X4 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (115547972121 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X4XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (0) (2) (83031437157925912200701 / 62500000000000000000000) (-64370974699 / 280869746990) : ℚ) : ℝ) <
      (115547972121 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XP6_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X4XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X4 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X4XP8_arg_eq :
    barrierCase2X4XP8LogArg = barrierComplex (16661025301 / 250000000000) (19622974699 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XP8LogArg, Case2PointData.X4, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X4XP8_arg_regular :
    (barrierCase2X4XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X4XP8LogArg).re := by
  rw [barrierCase2X4XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X4XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X4XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-1) (2) (38783703367839976200701 / 31250000000000000000000) (-16661025301 / 196229746990) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X4XP8LogArg (-1) (2) (38783703367839976200701 / 31250000000000000000000) (19622974699 / 12500000000) (-16661025301 / 125000000000)
  have hratio : ((-16661025301 / 125000000000) / (19622974699 / 12500000000) : ℚ) = (-16661025301 / 196229746990) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X4XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-1) (2) (38783703367839976200701 / 31250000000000000000000) (-16661025301 / 196229746990) <
      (-130081594412 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X4 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (-130081594412 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X4XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-1) (2) (38783703367839976200701 / 31250000000000000000000) (-16661025301 / 196229746990) : ℚ) : ℝ) <
      (-130081594412 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XP8_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoLogsX5Group0
namespace OAI

noncomputable section
namespace InternalCatalan

def barrierCase2X5XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X5 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X5XP0_arg_eq :
    barrierCase2X5XP0LogArg = barrierComplex (120257890343 / 50000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XP0LogArg, Case2PointData.X5, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X5XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X5XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (2) (0) (14461960189749012657649 / 10000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X5XP0LogArg (2) (0) (14461960189749012657649 / 10000000000000000000000) (120257890343 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (120257890343 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X5XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (2) (0) (14461960189749012657649 / 10000000000000000000000) (0 / 1) <
      (-163911407703 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X5 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (-163911407703 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X5XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (2) (0) (14461960189749012657649 / 10000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-163911407703 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XP0_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X5XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X5 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X5XP1_arg_eq :
    barrierCase2X5XP1LogArg = barrierComplex (329817402713 / 125000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XP1LogArg, Case2PointData.X5, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X5XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X5XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (2) (0) (108779519132349219760369 / 62500000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X5XP1LogArg (2) (0) (108779519132349219760369 / 62500000000000000000000) (329817402713 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (329817402713 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X5XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (2) (0) (108779519132349219760369 / 62500000000000000000000) (0 / 1) <
      (-41554930187 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X5 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (-41554930187 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X5XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (2) (0) (108779519132349219760369 / 62500000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-41554930187 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XP1_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X5XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X5 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X5XP2_arg_eq :
    barrierCase2X5XP2LogArg = barrierComplex (51 / 100) (14054719553 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XP2LogArg, Case2PointData.X5, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X5XP2_arg_regular :
    (barrierCase2X5XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X5XP2LogArg).re := by
  rw [barrierCase2X5XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X5XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X5XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-1) (1) (360097641713480519809 / 312500000000000000000) (76748209 / 1576748209) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X5XP2LogArg (-1) (1) (360097641713480519809 / 312500000000000000000) (26804719553 / 25000000000) (1304719553 / 25000000000)
  have hratio : ((1304719553 / 25000000000) / (26804719553 / 25000000000) : ℚ) = (76748209 / 1576748209) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X5XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-1) (1) (360097641713480519809 / 312500000000000000000) (76748209 / 1576748209) <
      (-83399800385 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X5 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (-83399800385 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X5XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-1) (1) (360097641713480519809 / 312500000000000000000) (76748209 / 1576748209) : ℚ) : ℝ) <
      (-83399800385 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XP2_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X5XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X5 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X5XP4_arg_eq :
    barrierCase2X5XP4LogArg = barrierComplex (111 / 400) (34132890343 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XP4LogArg, Case2PointData.X5, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X5XP4_arg_regular :
    (barrierCase2X5XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X5XP4LogArg).re := by
  rw [barrierCase2X5XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X5XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X5XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-1) (1) (1357569828167262657649 / 1250000000000000000000) (20257890343 / 48007890343) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X5XP4LogArg (-1) (1) (1357569828167262657649 / 1250000000000000000000) (48007890343 / 50000000000) (20257890343 / 50000000000)
  have hratio : ((20257890343 / 50000000000) / (48007890343 / 50000000000) : ℚ) = (20257890343 / 48007890343) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X5XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-1) (1) (1357569828167262657649 / 1250000000000000000000) (20257890343 / 48007890343) <
      (74873507590 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X5 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (74873507590 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X5XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-1) (1) (1357569828167262657649 / 1250000000000000000000) (20257890343 / 48007890343) : ℚ) : ℝ) <
      (74873507590 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XP4_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X5XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X5 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X5XP6_arg_eq :
    barrierCase2X5XP6LogArg = barrierComplex (147469792817 / 625000000000) (56759792817 / 62500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XP6LogArg, Case2PointData.X5, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X5XP6_arg_regular :
    (barrierCase2X5XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X5XP6LogArg).re := by
  rw [barrierCase2X5XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X5XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X5XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-1) (2) (343914747856365384344389 / 195312500000000000000000) (-147469792817 / 567597928170) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X5XP6LogArg (-1) (2) (343914747856365384344389 / 195312500000000000000000) (56759792817 / 31250000000) (-147469792817 / 312500000000)
  have hratio : ((-147469792817 / 312500000000) / (56759792817 / 31250000000) : ℚ) = (-147469792817 / 567597928170) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X5XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-1) (2) (343914747856365384344389 / 195312500000000000000000) (-147469792817 / 567597928170) <
      (119603537326 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X5 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (119603537326 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X5XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-1) (2) (343914747856365384344389 / 195312500000000000000000) (-147469792817 / 567597928170) : ℚ) : ℝ) <
      (119603537326 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XP6_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X5XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X5 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X5XP8_arg_eq :
    barrierCase2X5XP8LogArg = barrierComplex (55110207183 / 625000000000) (35599792817 / 62500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XP8LogArg, Case2PointData.X5, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X5XP8_arg_regular :
    (barrierCase2X5XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X5XP8LogArg).re := by
  rw [barrierCase2X5XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X5XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X5XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-2) (2) (129771659797085664344389 / 97656250000000000000000) (-55110207183 / 355997928170) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X5XP8LogArg (-2) (2) (129771659797085664344389 / 97656250000000000000000) (35599792817 / 31250000000) (-55110207183 / 312500000000)
  have hratio : ((-55110207183 / 312500000000) / (35599792817 / 31250000000) : ℚ) = (-55110207183 / 355997928170) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X5XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-2) (2) (129771659797085664344389 / 97656250000000000000000) (-55110207183 / 355997928170) <
      (-117241478922 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X5 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (-117241478922 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X5XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-2) (2) (129771659797085664344389 / 97656250000000000000000) (-55110207183 / 355997928170) : ℚ) : ℝ) <
      (-117241478922 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XP8_approx_upper using 1 <;>
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
































































open Case2PointData





end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoPointX3
namespace OAI

noncomputable section

namespace InternalCatalan

def barrierCase2X3XV0LogArg : ℂ :=
  1 - ((Case2PointData.X3 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1

private theorem barrierCase2X3XV0_arg_eq :
    barrierCase2X3XV0LogArg = barrierComplex (2998302603 / 6250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XV0LogArg, Case2PointData.X3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X3XV0_weight_eq :
    (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XV0_error :
    |((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X3XV0LogArg).re -
      ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-3) (0) (8989818499156575609 / 4882812500000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (15199211 / 100000000) (0 / 1)
    barrierCase2X3XV0LogArg (-3) (0) (8989818499156575609 / 4882812500000000000) (2998302603 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (2998302603 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X3XV0_approx_upper :
    barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-3) (0) (8989818499156575609 / 4882812500000000000) (0 / 1) <
      (-111643544915 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XV0_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-111643544915 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X3XV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XV0_error).2
  have ha : ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-3) (0) (8989818499156575609 / 4882812500000000000) (0 / 1) : ℚ) : ℝ) <
      (-111643544915 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XV0_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X3XV1LogArg : ℂ :=
  1 - ((Case2PointData.X3 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1

private theorem barrierCase2X3XV1_arg_eq :
    barrierCase2X3XV1LogArg = barrierComplex (5869907809 / 15625000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XV1LogArg, Case2PointData.X3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X3XV1_weight_eq :
    (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XV1_error :
    |((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X3XV1LogArg).re -
      ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-3) (0) (34455817686159180481 / 30517578125000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2225831 / 50000000) (0 / 1)
    barrierCase2X3XV1LogArg (-3) (0) (34455817686159180481 / 30517578125000000000) (5869907809 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (5869907809 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X3XV1_approx_upper :
    barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-3) (0) (34455817686159180481 / 30517578125000000000) (0 / 1) <
      (-43583251929 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XV1_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-43583251929 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X3XV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XV1_error).2
  have ha : ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-3) (0) (34455817686159180481 / 30517578125000000000) (0 / 1) : ℚ) : ℝ) <
      (-43583251929 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XV1_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X3XV2LogArg : ℂ :=
  1 - ((Case2PointData.X3 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1

private theorem barrierCase2X3XV2_arg_eq :
    barrierCase2X3XV2LogArg = barrierComplex (98268671367 / 62500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XV2LogArg, Case2PointData.X3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X3XV2_weight_eq :
    (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XV2_error :
    |((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X3XV2LogArg).re -
      ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (9656731772235445648689 / 7812500000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (1272699 / 50000000) (0 / 1)
    barrierCase2X3XV2LogArg (1) (0) (9656731772235445648689 / 7812500000000000000000) (98268671367 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (98268671367 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X3XV2_approx_upper :
    barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (9656731772235445648689 / 7812500000000000000000) (0 / 1) <
      (11518911410 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XV2_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (11518911410 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X3XV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XV2_error).2
  have ha : ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (9656731772235445648689 / 7812500000000000000000) (0 / 1) : ℚ) : ℝ) <
      (11518911410 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XV2_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X3XV3LogArg : ℂ :=
  1 - ((Case2PointData.X3 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1

private theorem barrierCase2X3XV3_arg_eq :
    barrierCase2X3XV3LogArg = barrierComplex (161782250543 / 100000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XV3LogArg, Case2PointData.X3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X3XV3_weight_eq :
    (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XV3_error :
    |((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X3XV3LogArg).re -
      ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (26173496590758023794849 / 20000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2466317 / 50000000) (0 / 1)
    barrierCase2X3XV3LogArg (1) (0) (26173496590758023794849 / 20000000000000000000000) (161782250543 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (161782250543 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X3XV3_approx_upper :
    barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (26173496590758023794849 / 20000000000000000000000) (0 / 1) <
      (-23729970528 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XV3_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (-23729970528 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X3XV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XV3_error).2
  have ha : ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (26173496590758023794849 / 20000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-23729970528 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XV3_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X3XV4LogArg : ℂ :=
  1 - ((Case2PointData.X3 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1

private theorem barrierCase2X3XV4_arg_eq :
    barrierCase2X3XV4LogArg = barrierComplex (1024958779831 / 625000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XV4LogArg, Case2PointData.X3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X3XV4_weight_eq :
    (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XV4_error :
    |((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X3XV4LogArg).re -
      ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (1050540500352652332388561 / 781250000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (11618157 / 100000000) (0 / 1)
    barrierCase2X3XV4LogArg (1) (0) (1050540500352652332388561 / 781250000000000000000000) (1024958779831 / 625000000000) (0 / 1)
  have hratio : ((0 / 1) / (1024958779831 / 625000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X3XV4_approx_upper :
    barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (1050540500352652332388561 / 781250000000000000000000) (0 / 1) <
      (57469913739 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XV4_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (57469913739 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X3XV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XV4_error).2
  have ha : ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (1050540500352652332388561 / 781250000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (57469913739 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XV4_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X3XV5LogArg : ℂ :=
  1 - ((Case2PointData.X3 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1

private theorem barrierCase2X3XV5_arg_eq :
    barrierCase2X3XV5LogArg = barrierComplex (1 / 1) (126816198483 / 250000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XV5LogArg, Case2PointData.X3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X3XV5_arg_regular :
    (barrierCase2X3XV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2X3XV5LogArg).re := by
  rw [barrierCase2X3XV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X3XV5_weight_eq :
    (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XV5_error :
    |((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X3XV5LogArg).re -
      ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (1) (78582348197679651501289 / 62500000000000000000000) (-123183801517 / 376816198483) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X3XV5LogArg (0) (1) (78582348197679651501289 / 62500000000000000000000) (376816198483 / 250000000000) (-123183801517 / 250000000000)
  have hratio : ((-123183801517 / 250000000000) / (376816198483 / 250000000000) : ℚ) = (-123183801517 / 376816198483) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X3XV5_approx_upper :
    barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (1) (78582348197679651501289 / 62500000000000000000000) (-123183801517 / 376816198483) <
      (-74652644980 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XV5_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-74652644980 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X3XV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XV5_error).2
  have ha : ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (1) (78582348197679651501289 / 62500000000000000000000) (-123183801517 / 376816198483) : ℚ) : ℝ) <
      (-74652644980 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XV5_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X3XV7LogArg : ℂ :=
  1 - ((Case2PointData.X3 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1

private theorem barrierCase2X3XV7_arg_eq :
    barrierCase2X3XV7LogArg = barrierComplex (1 / 1) (29265276573 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XV7LogArg, Case2PointData.X3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X3XV7_arg_regular :
    (barrierCase2X3XV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2X3XV7LogArg).re := by
  rw [barrierCase2X3XV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X3XV7_weight_eq :
    (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XV7_error :
    |((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X3XV7LogArg).re -
      ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (3356456412894182624329 / 2500000000000000000000) (-20734723427 / 79265276573) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X3XV7LogArg (0) (1) (3356456412894182624329 / 2500000000000000000000) (79265276573 / 50000000000) (-20734723427 / 50000000000)
  have hratio : ((-20734723427 / 50000000000) / (79265276573 / 50000000000) : ℚ) = (-20734723427 / 79265276573) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X3XV7_approx_upper :
    barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (3356456412894182624329 / 2500000000000000000000) (-20734723427 / 79265276573) <
      (-103013873848 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XV7_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-103013873848 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X3XV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XV7_error).2
  have ha : ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (3356456412894182624329 / 2500000000000000000000) (-20734723427 / 79265276573) : ℚ) : ℝ) <
      (-103013873848 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XV7_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X3XV9LogArg : ℂ :=
  1 - ((Case2PointData.X3 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1

private theorem barrierCase2X3XV9_arg_eq :
    barrierCase2X3XV9LogArg = barrierComplex (1 / 1) (621074202827 / 1000000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XV9LogArg, Case2PointData.X3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X3XV9_arg_regular :
    (barrierCase2X3XV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2X3XV9LogArg).re := by
  rw [barrierCase2X3XV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X3XV9_weight_eq :
    (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XV9_error :
    |((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X3XV9LogArg).re -
      ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (1385733165417193534791929 / 1000000000000000000000000) (-378925797173 / 1621074202827) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X3XV9LogArg (0) (1) (1385733165417193534791929 / 1000000000000000000000000) (1621074202827 / 1000000000000) (-378925797173 / 1000000000000)
  have hratio : ((-378925797173 / 1000000000000) / (1621074202827 / 1000000000000) : ℚ) = (-378925797173 / 1621074202827) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X3XV9_approx_upper :
    barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (1385733165417193534791929 / 1000000000000000000000000) (-378925797173 / 1621074202827) <
      (27643368918 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XV9_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (27643368918 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X3XV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XV9_error).2
  have ha : ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (1385733165417193534791929 / 1000000000000000000000000) (-378925797173 / 1621074202827) : ℚ) : ℝ) <
      (27643368918 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XV9_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X3XV11LogArg : ℂ :=
  1 - ((Case2PointData.X3 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1

private theorem barrierCase2X3XV11_arg_eq :
    barrierCase2X3XV11LogArg = barrierComplex (1 / 1) (399958779831 / 625000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XV11LogArg, Case2PointData.X3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X3XV11_arg_regular :
    (barrierCase2X3XV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2X3XV11LogArg).re := by
  rw [barrierCase2X3XV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X3XV11_weight_eq :
    (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XV11_error :
    |((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X3XV11LogArg).re -
      ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (550592025563902332388561 / 390625000000000000000000) (-225041220169 / 1024958779831) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X3XV11LogArg (0) (1) (550592025563902332388561 / 390625000000000000000000) (1024958779831 / 625000000000) (-225041220169 / 625000000000)
  have hratio : ((-225041220169 / 625000000000) / (1024958779831 / 625000000000) : ℚ) = (-225041220169 / 1024958779831) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X3XV11_approx_upper :
    barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (550592025563902332388561 / 390625000000000000000000) (-225041220169 / 1024958779831) <
      (-60046906546 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XV11_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-60046906546 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X3XV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XV11_error).2
  have ha : ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (550592025563902332388561 / 390625000000000000000000) (-225041220169 / 1024958779831) : ℚ) : ℝ) <
      (-60046906546 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XV11_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

open Case2PointData

private theorem barrierCase2X3_XP_tail_upper :
    (barrierP2Tail.map (barrierCase2XPLogTerm (X3 : ℝ))).sum <
      (-876568872745 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [2, 4, 6, 8],
      barrierCase2XPLogTerm (X3 : ℝ) (barrierP2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XPLogTerm (X3 : ℝ) (barrierP2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierP2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X3XP2_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X3XP4_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X3XP6_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X3XP8_arg_regular
  rw [barrierP2Tail_paired_sum _ hp]
  linarith only [barrierCase2X3XP0_log_upper,
    barrierCase2X3XP1_log_upper,
    barrierCase2X3XP2_log_upper,
    barrierCase2X3XP4_log_upper,
    barrierCase2X3XP6_log_upper,
    barrierCase2X3XP8_log_upper]

private theorem barrierCase2X3_XV_tail_upper :
    (barrierV2Tail.map (barrierCase2XVLogTerm (X3 : ℝ))).sum <
      (-530108055135 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2XVLogTerm (X3 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XVLogTerm (X3 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X3XV5_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X3XV7_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X3XV9_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X3XV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2X3XV0_log_upper,
    barrierCase2X3XV1_log_upper,
    barrierCase2X3XV2_log_upper,
    barrierCase2X3XV3_log_upper,
    barrierCase2X3XV4_log_upper,
    barrierCase2X3XV5_log_upper,
    barrierCase2X3XV7_log_upper,
    barrierCase2X3XV9_log_upper,
    barrierCase2X3XV11_log_upper]

private theorem barrierCase2X3_approx_upper :
    barrierCase2XApproxRat X3 (-1) (0) (0) (3251697397 / 2500000000) (8251697397 / 5000000000) (35573535961656575609 / 25000000000000000000) + (-876568872745 / 1000000000000) + (-530108055135 / 1000000000000) <
      (-98399 / 100000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase2XApproxRat barrierCase2XRat
  rw [barrierCase2TP_eq_explicit, barrierCase2SV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2X3_lt : barrierCase2X (X3 : ℝ) < (-98399 / 100000 : ℝ) := by
  have hx : |(X3 : ℝ)| ≤ 1 := by norm_num [X3]
  have he := (abs_lt.mp (barrierCase2X_realLog_approx_error X3 hx
    (-1) (0) (0) (3251697397 / 2500000000) (8251697397 / 5000000000) (35573535961656575609 / 25000000000000000000)
    X3_normalizations.1 X3_normalizations.2.1 X3_normalizations.2.2)).2
  have ha : ((barrierCase2XApproxRat X3 (-1) (0) (0) (3251697397 / 2500000000) (8251697397 / 5000000000) (35573535961656575609 / 25000000000000000000) : ℚ) : ℝ) +
      (-876568872745 / 1000000000000) + (-530108055135 / 1000000000000) < (-98399 / 100000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith only [he, ha, barrierCase2X3_XP_tail_upper, barrierCase2X3_XV_tail_upper]

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoPointX4
namespace OAI

noncomputable section

namespace InternalCatalan

def barrierCase2X4XV0LogArg : ℂ :=
  1 - ((Case2PointData.X4 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1

private theorem barrierCase2X4XV0_arg_eq :
    barrierCase2X4XV0LogArg = barrierComplex (1462827187 / 2500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XV0LogArg, Case2PointData.X4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X4XV0_weight_eq :
    (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XV0_error :
    |((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X4XV0LogArg).re -
      ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-2) (0) (2139863379026332969 / 1562500000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (15199211 / 100000000) (0 / 1)
    barrierCase2X4XV0LogArg (-2) (0) (2139863379026332969 / 1562500000000000000) (1462827187 / 2500000000) (0 / 1)
  have hratio : ((0 / 1) / (1462827187 / 2500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X4XV0_approx_upper :
    barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-2) (0) (2139863379026332969 / 1562500000000000000) (0 / 1) <
      (-81455571945 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XV0_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-81455571945 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X4XV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XV0_error).2
  have ha : ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-2) (0) (2139863379026332969 / 1562500000000000000) (0 / 1) : ℚ) : ℝ) <
      (-81455571945 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XV0_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X4XV1LogArg : ℂ :=
  1 - ((Case2PointData.X4 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1

private theorem barrierCase2X4XV1_arg_eq :
    barrierCase2X4XV1LogArg = barrierComplex (3138481561 / 6250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XV1LogArg, Case2PointData.X4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X4XV1_weight_eq :
    (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XV1_error :
    |((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X4XV1LogArg).re -
      ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-2) (0) (9850066508736996721 / 9765625000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2225831 / 50000000) (0 / 1)
    barrierCase2X4XV1LogArg (-2) (0) (9850066508736996721 / 9765625000000000000) (3138481561 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (3138481561 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X4XV1_approx_upper :
    barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-2) (0) (9850066508736996721 / 9765625000000000000) (0 / 1) <
      (-30664933583 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XV1_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-30664933583 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X4XV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XV1_error).2
  have ha : ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-2) (0) (9850066508736996721 / 9765625000000000000) (0 / 1) : ℚ) : ℝ) <
      (-30664933583 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XV1_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X4XV2LogArg : ℂ :=
  1 - ((Case2PointData.X4 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1

private theorem barrierCase2X4XV2_arg_eq :
    barrierCase2X4XV2LogArg = barrierComplex (36408900943 / 25000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XV2LogArg, Case2PointData.X4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X4XV2_weight_eq :
    (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XV2_error :
    |((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X4XV2LogArg).re -
      ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (1325608067877186289249 / 1250000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (1272699 / 50000000) (0 / 1)
    barrierCase2X4XV2LogArg (1) (0) (1325608067877186289249 / 1250000000000000000000) (36408900943 / 25000000000) (0 / 1)
  have hratio : ((0 / 1) / (36408900943 / 25000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X4XV2_approx_upper :
    barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (1325608067877186289249 / 1250000000000000000000) (0 / 1) <
      (9569104368 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XV2_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (9569104368 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X4XV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XV2_error).2
  have ha : ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (1325608067877186289249 / 1250000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (9569104368 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XV2_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X4XV3LogArg : ℂ :=
  1 - ((Case2PointData.X4 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1

private theorem barrierCase2X4XV3_arg_eq :
    barrierCase2X4XV3LogArg = barrierComplex (59706283447 / 40000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XV3LogArg, Case2PointData.X4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X4XV3_weight_eq :
    (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XV3_error :
    |((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X4XV3LogArg).re -
      ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (3564840283053506201809 / 3200000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2466317 / 50000000) (0 / 1)
    barrierCase2X4XV3LogArg (1) (0) (3564840283053506201809 / 3200000000000000000000) (59706283447 / 40000000000) (0 / 1)
  have hratio : ((0 / 1) / (59706283447 / 40000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X4XV3_approx_upper :
    barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (3564840283053506201809 / 3200000000000000000000) (0 / 1) <
      (-19758050779 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XV3_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (-19758050779 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X4XV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XV3_error).2
  have ha : ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (3564840283053506201809 / 3200000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-19758050779 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XV3_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X4XV4LogArg : ℂ :=
  1 - ((Case2PointData.X4 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1

private theorem barrierCase2X4XV4_arg_eq :
    barrierCase2X4XV4LogArg = barrierComplex (377572255999 / 250000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XV4LogArg, Case2PointData.X4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X4XV4_weight_eq :
    (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XV4_error :
    |((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X4XV4LogArg).re -
      ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (142560808500174391488001 / 125000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (11618157 / 100000000) (0 / 1)
    barrierCase2X4XV4LogArg (1) (0) (142560808500174391488001 / 125000000000000000000000) (377572255999 / 250000000000) (0 / 1)
  have hratio : ((0 / 1) / (377572255999 / 250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X4XV4_approx_upper :
    barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (142560808500174391488001 / 125000000000000000000000) (0 / 1) <
      (47901782040 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XV4_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (47901782040 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X4XV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XV4_error).2
  have ha : ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (142560808500174391488001 / 125000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (47901782040 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XV4_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X4XV5LogArg : ℂ :=
  1 - ((Case2PointData.X4 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1

private theorem barrierCase2X4XV5_arg_eq :
    barrierCase2X4XV5LogArg = barrierComplex (1 / 1) (40449739707 / 100000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XV5LogArg, Case2PointData.X4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X4XV5_arg_regular :
    (barrierCase2X4XV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2X4XV5LogArg).re := by
  rw [barrierCase2X4XV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X4XV5_weight_eq :
    (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XV5_error :
    |((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X4XV5LogArg).re -
      ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (11636181442364052445849 / 10000000000000000000000) (40449739707 / 100000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X4XV5LogArg (0) (0) (11636181442364052445849 / 10000000000000000000000) (1 / 1) (40449739707 / 100000000000)
  have hratio : ((40449739707 / 100000000000) / (1 / 1) : ℚ) = (40449739707 / 100000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X4XV5_approx_upper :
    barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (11636181442364052445849 / 10000000000000000000000) (40449739707 / 100000000000) <
      (-63573597776 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XV5_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-63573597776 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X4XV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XV5_error).2
  have ha : ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (11636181442364052445849 / 10000000000000000000000) (40449739707 / 100000000000) : ℚ) : ℝ) <
      (-63573597776 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XV5_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X4XV7LogArg : ℂ :=
  1 - ((Case2PointData.X4 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1

private theorem barrierCase2X4XV7_arg_eq :
    barrierCase2X4XV7LogArg = barrierComplex (1 / 1) (9334555317 / 20000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XV7LogArg, Case2PointData.X4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X4XV7_arg_regular :
    (barrierCase2X4XV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2X4XV7LogArg).re := by
  rw [barrierCase2X4XV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X4XV7_weight_eq :
    (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XV7_error :
    |((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X4XV7LogArg).re -
      ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (487133922966132970489 / 400000000000000000000) (9334555317 / 20000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X4XV7LogArg (0) (0) (487133922966132970489 / 400000000000000000000) (1 / 1) (9334555317 / 20000000000)
  have hratio : ((9334555317 / 20000000000) / (1 / 1) : ℚ) = (9334555317 / 20000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X4XV7_approx_upper :
    barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (487133922966132970489 / 400000000000000000000) (9334555317 / 20000000000) <
      (-81355116341 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XV7_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-81355116341 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X4XV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XV7_error).2
  have ha : ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (487133922966132970489 / 400000000000000000000) (9334555317 / 20000000000) : ℚ) : ℝ) <
      (-81355116341 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XV7_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X4XV9LogArg : ℂ :=
  1 - ((Case2PointData.X4 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1

private theorem barrierCase2X4XV9_arg_eq :
    barrierCase2X4XV9LogArg = barrierComplex (1 / 1) (198100007283 / 400000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XV9LogArg, Case2PointData.X4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X4XV9_arg_regular :
    (barrierCase2X4XV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2X4XV9LogArg).re := by
  rw [barrierCase2X4XV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X4XV9_weight_eq :
    (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XV9_error :
    |((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X4XV9LogArg).re -
      ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (199243612885524653042089 / 160000000000000000000000) (198100007283 / 400000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X4XV9LogArg (0) (0) (199243612885524653042089 / 160000000000000000000000) (1 / 1) (198100007283 / 400000000000)
  have hratio : ((198100007283 / 400000000000) / (1 / 1) : ℚ) = (198100007283 / 400000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X4XV9_approx_upper :
    barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (199243612885524653042089 / 160000000000000000000000) (198100007283 / 400000000000) <
      (23718033220 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XV9_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (23718033220 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X4XV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XV9_error).2
  have ha : ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (199243612885524653042089 / 160000000000000000000000) (198100007283 / 400000000000) : ℚ) : ℝ) <
      (23718033220 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XV9_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X4XV11LogArg : ℂ :=
  1 - ((Case2PointData.X4 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1

private theorem barrierCase2X4XV11_arg_eq :
    barrierCase2X4XV11LogArg = barrierComplex (1 / 1) (127572255999 / 250000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XV11LogArg, Case2PointData.X4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X4XV11_arg_regular :
    (barrierCase2X4XV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2X4XV11LogArg).re := by
  rw [barrierCase2X4XV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X4XV11_weight_eq :
    (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XV11_error :
    |((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X4XV11LogArg).re -
      ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (78774680500674391488001 / 62500000000000000000000) (-122427744001 / 377572255999) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X4XV11LogArg (0) (1) (78774680500674391488001 / 62500000000000000000000) (377572255999 / 250000000000) (-122427744001 / 250000000000)
  have hratio : ((-122427744001 / 250000000000) / (377572255999 / 250000000000) : ℚ) = (-122427744001 / 377572255999) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X4XV11_approx_upper :
    barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (78774680500674391488001 / 62500000000000000000000) (-122427744001 / 377572255999) <
      (-50043494195 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XV11_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-50043494195 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X4XV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XV11_error).2
  have ha : ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (78774680500674391488001 / 62500000000000000000000) (-122427744001 / 377572255999) : ℚ) : ℝ) <
      (-50043494195 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XV11_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

open Case2PointData

private theorem barrierCase2X4_XP_tail_upper :
    (barrierP2Tail.map (barrierCase2XPLogTerm (X4 : ℝ))).sum <
      (-551935825239 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [2, 4, 6, 8],
      barrierCase2XPLogTerm (X4 : ℝ) (barrierP2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XPLogTerm (X4 : ℝ) (barrierP2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierP2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X4XP2_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X4XP4_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X4XP6_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X4XP8_arg_regular
  rw [barrierP2Tail_paired_sum _ hp]
  linarith only [barrierCase2X4XP0_log_upper,
    barrierCase2X4XP1_log_upper,
    barrierCase2X4XP2_log_upper,
    barrierCase2X4XP4_log_upper,
    barrierCase2X4XP6_log_upper,
    barrierCase2X4XP8_log_upper]

private theorem barrierCase2X4_XV_tail_upper :
    (barrierV2Tail.map (barrierCase2XVLogTerm (X4 : ℝ))).sum <
      (-416916020083 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2XVLogTerm (X4 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XVLogTerm (X4 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X4XV5_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X4XV7_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X4XV9_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X4XV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2X4XV0_log_upper,
    barrierCase2X4XV1_log_upper,
    barrierCase2X4XV2_log_upper,
    barrierCase2X4XV3_log_upper,
    barrierCase2X4XV4_log_upper,
    barrierCase2X4XV5_log_upper,
    barrierCase2X4XV7_log_upper,
    barrierCase2X4XV9_log_upper,
    barrierCase2X4XV11_log_upper]

private theorem barrierCase2X4_approx_upper :
    barrierCase2XApproxRat X4 (-1) (0) (0) (1037172813 / 1000000000) (3037172813 / 2000000000) (5075727444026332969 / 4000000000000000000) + (-551935825239 / 1000000000000) + (-416916020083 / 1000000000000) <
      (-98399 / 100000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase2XApproxRat barrierCase2XRat
  rw [barrierCase2TP_eq_explicit, barrierCase2SV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2X4_lt : barrierCase2X (X4 : ℝ) < (-98399 / 100000 : ℝ) := by
  have hx : |(X4 : ℝ)| ≤ 1 := by norm_num [X4]
  have he := (abs_lt.mp (barrierCase2X_realLog_approx_error X4 hx
    (-1) (0) (0) (1037172813 / 1000000000) (3037172813 / 2000000000) (5075727444026332969 / 4000000000000000000)
    X4_normalizations.1 X4_normalizations.2.1 X4_normalizations.2.2)).2
  have ha : ((barrierCase2XApproxRat X4 (-1) (0) (0) (1037172813 / 1000000000) (3037172813 / 2000000000) (5075727444026332969 / 4000000000000000000) : ℚ) : ℝ) +
      (-551935825239 / 1000000000000) + (-416916020083 / 1000000000000) < (-98399 / 100000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith only [he, ha, barrierCase2X4_XP_tail_upper, barrierCase2X4_XV_tail_upper]

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoPointX5
namespace OAI

noncomputable section

namespace InternalCatalan

def barrierCase2X5XV0LogArg : ℂ :=
  1 - ((Case2PointData.X5 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1

private theorem barrierCase2X5XV0_arg_eq :
    barrierCase2X5XV0LogArg = barrierComplex (4242182921 / 6250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XV0LogArg, Case2PointData.X5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X5XV0_weight_eq :
    (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XV0_error :
    |((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X5XV0LogArg).re -
      ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-2) (0) (17996115935224092241 / 9765625000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (15199211 / 100000000) (0 / 1)
    barrierCase2X5XV0LogArg (-2) (0) (17996115935224092241 / 9765625000000000000) (4242182921 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (4242182921 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X5XV0_approx_upper :
    barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-2) (0) (17996115935224092241 / 9765625000000000000) (0 / 1) <
      (-58897472640 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XV0_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-58897472640 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X5XV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XV0_error).2
  have ha : ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-2) (0) (17996115935224092241 / 9765625000000000000) (0 / 1) : ℚ) : ℝ) <
      (-58897472640 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XV0_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X5XV1LogArg : ℂ :=
  1 - ((Case2PointData.X5 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1

private theorem barrierCase2X5XV1_arg_eq :
    barrierCase2X5XV1LogArg = barrierComplex (9601548763 / 15625000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XV1LogArg, Case2PointData.X5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X5XV1_weight_eq :
    (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XV1_error :
    |((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X5XV1LogArg).re -
      ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-2) (0) (92189738648266830169 / 61035156250000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2225831 / 50000000) (0 / 1)
    barrierCase2X5XV1LogArg (-2) (0) (92189738648266830169 / 61035156250000000000) (9601548763 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (9601548763 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X5XV1_approx_upper :
    barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-2) (0) (92189738648266830169 / 61035156250000000000) (0 / 1) <
      (-21677269311 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XV1_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-21677269311 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X5XV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XV1_error).2
  have ha : ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-2) (0) (92189738648266830169 / 61035156250000000000) (0 / 1) : ℚ) : ℝ) <
      (-21677269311 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XV1_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X5XV2LogArg : ℂ :=
  1 - ((Case2PointData.X5 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1

private theorem barrierCase2X5XV2_arg_eq :
    barrierCase2X5XV2LogArg = barrierComplex (84585987869 / 62500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XV2LogArg, Case2PointData.X5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X5XV2_weight_eq :
    (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XV2_error :
    |((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X5XV2LogArg).re -
      ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (0) (0) (7154789343774615161161 / 3906250000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (1272699 / 50000000) (0 / 1)
    barrierCase2X5XV2LogArg (0) (0) (7154789343774615161161 / 3906250000000000000000) (84585987869 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (84585987869 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X5XV2_approx_upper :
    barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (0) (0) (7154789343774615161161 / 3906250000000000000000) (0 / 1) <
      (7702426992 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XV2_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (7702426992 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X5XV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XV2_error).2
  have ha : ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (0) (0) (7154789343774615161161 / 3906250000000000000000) (0 / 1) : ℚ) : ℝ) <
      (7702426992 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XV2_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X5XV3LogArg : ℂ :=
  1 - ((Case2PointData.X5 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1

private theorem barrierCase2X5XV3_arg_eq :
    barrierCase2X5XV3LogArg = barrierComplex (138148524501 / 100000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XV3LogArg, Case2PointData.X5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X5XV3_weight_eq :
    (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XV3_error :
    |((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X5XV3LogArg).re -
      ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (0) (0) (19085014821803397299001 / 10000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2466317 / 50000000) (0 / 1)
    barrierCase2X5XV3LogArg (0) (0) (19085014821803397299001 / 10000000000000000000000) (138148524501 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (138148524501 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X5XV3_approx_upper :
    barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (0) (0) (19085014821803397299001 / 10000000000000000000000) (0 / 1) <
      (-15940259828 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XV3_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (-15940259828 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X5XV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XV3_error).2
  have ha : ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (0) (0) (19085014821803397299001 / 10000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-15940259828 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XV3_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X5XV4LogArg : ℂ :=
  1 - ((Case2PointData.X5 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1

private theorem barrierCase2X5XV4_arg_eq :
    barrierCase2X5XV4LogArg = barrierComplex (871961500717 / 625000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XV4LogArg, Case2PointData.X5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]


private theorem barrierCase2X5XV4_weight_eq :
    (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XV4_error :
    |((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X5XV4LogArg).re -
      ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (0) (0) (760316858732642791514089 / 390625000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (11618157 / 100000000) (0 / 1)
    barrierCase2X5XV4LogArg (0) (0) (760316858732642791514089 / 390625000000000000000000) (871961500717 / 625000000000) (0 / 1)
  have hratio : ((0 / 1) / (871961500717 / 625000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X5XV4_approx_upper :
    barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (0) (0) (760316858732642791514089 / 390625000000000000000000) (0 / 1) <
      (38687721880 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XV4_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (38687721880 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X5XV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XV4_error).2
  have ha : ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (0) (0) (760316858732642791514089 / 390625000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (38687721880 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XV4_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X5XV5LogArg : ℂ :=
  1 - ((Case2PointData.X5 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1

private theorem barrierCase2X5XV5_arg_eq :
    barrierCase2X5XV5LogArg = barrierComplex (1 / 1) (78304866081 / 250000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XV5LogArg, Case2PointData.X5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X5XV5_arg_regular :
    (barrierCase2X5XV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2X5XV5LogArg).re := by
  rw [barrierCase2X5XV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X5XV5_weight_eq :
    (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XV5_error :
    |((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X5XV5LogArg).re -
      ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (68631652051963344298561 / 62500000000000000000000) (78304866081 / 250000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X5XV5LogArg (0) (0) (68631652051963344298561 / 62500000000000000000000) (1 / 1) (78304866081 / 250000000000)
  have hratio : ((78304866081 / 250000000000) / (1 / 1) : ℚ) = (78304866081 / 250000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X5XV5_approx_upper :
    barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (68631652051963344298561 / 62500000000000000000000) (78304866081 / 250000000000) <
      (-51979476494 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XV5_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-51979476494 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X5XV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XV5_error).2
  have ha : ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (68631652051963344298561 / 62500000000000000000000) (78304866081 / 250000000000) : ℚ) : ℝ) <
      (-51979476494 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XV5_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X5XV7LogArg : ℂ :=
  1 - ((Case2PointData.X5 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1

private theorem barrierCase2X5XV7_arg_eq :
    barrierCase2X5XV7LogArg = barrierComplex (1 / 1) (18070353711 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XV7LogArg, Case2PointData.X5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X5XV7_arg_regular :
    (barrierCase2X5XV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2X5XV7LogArg).re := by
  rw [barrierCase2X5XV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X5XV7_weight_eq :
    (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XV7_error :
    |((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X5XV7LogArg).re -
      ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (2826537683240651471521 / 2500000000000000000000) (18070353711 / 50000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X5XV7LogArg (0) (0) (2826537683240651471521 / 2500000000000000000000) (1 / 1) (18070353711 / 50000000000)
  have hratio : ((18070353711 / 50000000000) / (1 / 1) : ℚ) = (18070353711 / 50000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X5XV7_approx_upper :
    barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (2826537683240651471521 / 2500000000000000000000) (18070353711 / 50000000000) <
      (-61966174193 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XV7_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-61966174193 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X5XV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XV7_error).2
  have ha : ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (2826537683240651471521 / 2500000000000000000000) (18070353711 / 50000000000) : ℚ) : ℝ) <
      (-61966174193 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XV7_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X5XV9LogArg : ℂ :=
  1 - ((Case2PointData.X5 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1

private theorem barrierCase2X5XV9_arg_eq :
    barrierCase2X5XV9LogArg = barrierComplex (1 / 1) (383493062089 / 1000000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XV9LogArg, Case2PointData.X5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X5XV9_arg_regular :
    (barrierCase2X5XV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2X5XV9LogArg).re := by
  rw [barrierCase2X5XV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X5XV9_weight_eq :
    (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XV9_error :
    |((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X5XV9LogArg).re -
      ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (1147066928670397609043921 / 1000000000000000000000000) (383493062089 / 1000000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X5XV9LogArg (0) (0) (1147066928670397609043921 / 1000000000000000000000000) (1 / 1) (383493062089 / 1000000000000)
  have hratio : ((383493062089 / 1000000000000) / (1 / 1) : ℚ) = (383493062089 / 1000000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X5XV9_approx_upper :
    barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (1147066928670397609043921 / 1000000000000000000000000) (383493062089 / 1000000000000) <
      (19515063396 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XV9_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (19515063396 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X5XV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XV9_error).2
  have ha : ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (1147066928670397609043921 / 1000000000000000000000000) (383493062089 / 1000000000000) : ℚ) : ℝ) <
      (19515063396 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XV9_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

def barrierCase2X5XV11LogArg : ℂ :=
  1 - ((Case2PointData.X5 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1

private theorem barrierCase2X5XV11_arg_eq :
    barrierCase2X5XV11LogArg = barrierComplex (1 / 1) (246961500717 / 625000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XV11LogArg, Case2PointData.X5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X5XV11_arg_regular :
    (barrierCase2X5XV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2X5XV11LogArg).re := by
  rw [barrierCase2X5XV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X5XV11_weight_eq :
    (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XV11_error :
    |((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X5XV11LogArg).re -
      ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (451614982836392791514089 / 390625000000000000000000) (246961500717 / 625000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X5XV11LogArg (0) (0) (451614982836392791514089 / 390625000000000000000000) (1 / 1) (246961500717 / 625000000000)
  have hratio : ((246961500717 / 625000000000) / (1 / 1) : ℚ) = (246961500717 / 625000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two, portInt_toNat_ofNat]

private theorem barrierCase2X5XV11_approx_upper :
    barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (451614982836392791514089 / 390625000000000000000000) (246961500717 / 625000000000) <
      (-40113838448 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XV11_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-40113838448 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X5XV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XV11_error).2
  have ha : ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (451614982836392791514089 / 390625000000000000000000) (246961500717 / 625000000000) : ℚ) : ℝ) <
      (-40113838448 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XV11_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith

open Case2PointData

private theorem barrierCase2X5_XP_tail_upper :
    (barrierP2Tail.map (barrierCase2XPLogTerm (X5 : ℝ))).sum <
      (-217794806672 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [2, 4, 6, 8],
      barrierCase2XPLogTerm (X5 : ℝ) (barrierP2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XPLogTerm (X5 : ℝ) (barrierP2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierP2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X5XP2_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X5XP4_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X5XP6_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X5XP8_arg_regular
  rw [barrierP2Tail_paired_sum _ hp]
  linarith only [barrierCase2X5XP0_log_upper,
    barrierCase2X5XP1_log_upper,
    barrierCase2X5XP2_log_upper,
    barrierCase2X5XP4_log_upper,
    barrierCase2X5XP6_log_upper,
    barrierCase2X5XP8_log_upper]

private theorem barrierCase2X5_XV_tail_upper :
    (barrierV2Tail.map (barrierCase2XVLogTerm (X5 : ℝ))).sum <
      (-319213704385 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2XVLogTerm (X5 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XVLogTerm (X5 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X5XV5_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X5XV7_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X5XV9_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X5XV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2X5XV0_log_upper,
    barrierCase2X5XV1_log_upper,
    barrierCase2X5XV2_log_upper,
    barrierCase2X5XV3_log_upper,
    barrierCase2X5XV4_log_upper,
    barrierCase2X5XV5_log_upper,
    barrierCase2X5XV7_log_upper,
    barrierCase2X5XV9_log_upper,
    barrierCase2X5XV11_log_upper]

private theorem barrierCase2X5_approx_upper :
    barrierCase2XApproxRat X5 (-2) (0) (0) (2007817079 / 1250000000) (7007817079 / 5000000000) (29031329422724092241 / 25000000000000000000) + (-217794806672 / 1000000000000) + (-319213704385 / 1000000000000) <
      (-98399 / 100000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase2XApproxRat barrierCase2XRat
  rw [barrierCase2TP_eq_explicit, barrierCase2SV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2X5_lt : barrierCase2X (X5 : ℝ) < (-98399 / 100000 : ℝ) := by
  have hx : |(X5 : ℝ)| ≤ 1 := by norm_num [X5]
  have he := (abs_lt.mp (barrierCase2X_realLog_approx_error X5 hx
    (-2) (0) (0) (2007817079 / 1250000000) (7007817079 / 5000000000) (29031329422724092241 / 25000000000000000000)
    X5_normalizations.1 X5_normalizations.2.1 X5_normalizations.2.2)).2
  have ha : ((barrierCase2XApproxRat X5 (-2) (0) (0) (2007817079 / 1250000000) (7007817079 / 5000000000) (29031329422724092241 / 25000000000000000000) : ℚ) : ℝ) +
      (-217794806672 / 1000000000000) + (-319213704385 / 1000000000000) < (-98399 / 100000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5_approx_upper using 1 <;>
      first | with_reducible_and_instances rfl | norm_num
  linarith only [he, ha, barrierCase2X5_XP_tail_upper, barrierCase2X5_XV_tail_upper]

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




























theorem barrierCase2X_table_left_lt_A2 :
    ∀ m ∈ ([-6503394794, -5185864065, -4015634158] : List ℤ),
      barrierCase2X (barrierBracketLeft m : ℝ) < (-98399 / 100000 : ℝ) := by
  intro m hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · convert barrierCase2X3_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.X3]
  · convert barrierCase2X4_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.X4]
  · convert barrierCase2X5_lt using 1
    norm_num [barrierBracketLeft, Case2PointData.X5]













end InternalCatalan

end OAI

end

section
open OAI.InternalCatalan

theorem solution :
    ∀ m ∈ ([-6503394794, -5185864065, -4015634158] : List ℤ),
      barrierCase2X (barrierBracketLeft m : ℝ) < (-98399 / 100000 : ℝ) := by
  first
  | exact @OAI.InternalCatalan.barrierCase2X_table_left_lt_A2
  | (apply OAI.InternalCatalan.barrierCase2X_table_left_lt_A2 <;> assumption)

end
