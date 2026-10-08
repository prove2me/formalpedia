-- Prove2me | solution 1 for OAI.InternalCatalan.catalan_irrational
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T19:31:07.081413+00:00
-- url     : https://prove2.me/submissions/2453fd16-31a3-4908-887a-6632a903cec0

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
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
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Union
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Convert
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
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_OAICatalanIrrationality
import Theorems.Thm_OAI_InternalCatalan_determinantRat_finite_place_threshold
import Theorems.Thm_OAI_InternalCatalan_determinantRat_prime_ne_zero
import Theorems.Thm_OAI_InternalCatalan_eventually_realDeterminant_log_upper

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

theorem centralCoeffKernel_of_neg {d : ℤ} (hd : d < 0) :
    centralCoeffKernel d = 0 := by
  simp [centralCoeffKernel, not_le.mpr hd]

theorem centralCoeffKernel_of_odd {d : ℤ} (hd : d % 2 ≠ 0) :
    centralCoeffKernel d = 0 := by
  simp [centralCoeffKernel, hd]

theorem centralCoeffKernel_two_mul (l : ℕ) :
    centralCoeffKernel (2 * (l : ℤ)) = centralCoeff l := by
  have hn : 0 ≤ 2 * (l : ℤ) := by positivity
  have he : (2 * (l : ℤ)) % 2 = 0 := by omega
  have ht : (2 * (l : ℤ)).toNat = 2 * l := by omega
  simp [centralCoeffKernel, hn, he, ht]


@[simp] theorem momentScalar_zero : momentScalar 0 = 2 := by
  norm_num [momentScalar]

theorem momentScalar_even (l : ℕ) :
    momentScalar (2 * l) = 2 / (((2 * l + 1 : ℕ) : ℚ) * centralCoeff l) := by
  simp [momentScalar]

theorem momentScalar_odd (l : ℕ) : momentScalar (2 * l + 1) = 0 := by
  simp [momentScalar]



@[simp] theorem boundaryMinus_zero : boundaryMinus 0 = 0 := rfl
@[simp] theorem boundaryMinus_one : boundaryMinus 1 = 2 := rfl
@[simp] theorem boundaryPlus_zero : boundaryPlus 0 = 0 := rfl
@[simp] theorem boundaryPlus_one : boundaryPlus 1 = 0 := rfl

theorem boundaryMinus_step (d : ℕ) :
    ((d + 2 : ℕ) : ℚ) * boundaryMinus (d + 2) =
      ((d + 1 : ℕ) : ℚ) * boundaryMinus d + momentScalar d + momentScalar (d + 1) := by
  have hd : ((d + 2 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [boundaryMinus]
  field_simp

theorem boundaryPlus_step (d : ℕ) :
    ((d + 1 : ℕ) : ℚ) * boundaryPlus (d + 2) =
      (d : ℚ) * boundaryPlus d + 2 / ((d + 1 : ℕ) : ℚ) := by
  have hd : ((d + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [boundaryPlus]
  field_simp




theorem momentRat_of_le {i j : ℕ} (hji : j ≤ i) :
    momentRat i j = boundaryMinus (i - j) -
      ∑ k ∈ Finset.range j, momentScalar (i - j + k) / ((k + 1 : ℕ) : ℚ) := by
  simp [momentRat, hji]

theorem momentRat_of_lt {i j : ℕ} (hij : i < j) :
    momentRat i j = boundaryPlus (j - i) -
      ∑ k ∈ Finset.range i, momentScalar k / ((j - i + k + 1 : ℕ) : ℚ) := by
  simp [momentRat, not_le.mpr hij]

@[simp] theorem momentRat_zero_right (i : ℕ) : momentRat i 0 = boundaryMinus i := by
  simp [momentRat]

@[simp] theorem momentRat_zero_left (j : ℕ) : momentRat 0 j = boundaryPlus j := by
  cases j with
  | zero => simp [momentRat]
  | succ j => simp [momentRat]


theorem momentRat_step (i j : ℕ) :
    momentRat i j - momentRat (i + 1) (j + 1) =
      momentScalar i / ((j + 1 : ℕ) : ℚ) := by
  by_cases hji : j ≤ i
  · have hs : j + 1 ≤ i + 1 := by omega
    have hi : i - j + j = i := Nat.sub_add_cancel hji
    rw [momentRat_of_le hji, momentRat_of_le hs]
    simp only [Nat.add_sub_add_right, Finset.sum_range_succ, hi]
    ring
  · have hij : i < j := Nat.lt_of_not_ge hji
    have hs : i + 1 < j + 1 := by omega
    have hj : j - i + i = j := Nat.sub_add_cancel (Nat.le_of_lt hij)
    rw [momentRat_of_lt hij, momentRat_of_lt hs]
    simp only [Nat.add_sub_add_right, Finset.sum_range_succ, hj]
    ring




@[simp] theorem harmonicRat_zero (d : ℕ) : harmonicRat d 0 = 0 := by
  simp [harmonicRat]

theorem harmonicRat_succ (d n : ℕ) :
    harmonicRat d (n + 1) = harmonicRat d n + 1 / (((n + 1 : ℕ) : ℚ) ^ d) := by
  simp [harmonicRat, Finset.sum_range_succ]


@[simp] theorem zetaRat_diagonal (i : ℕ) : zetaRat i i = -harmonicRat 2 i := by
  simp [zetaRat]

theorem zetaRat_of_ne {i j : ℕ} (hij : i ≠ j) :
    zetaRat i j = (harmonicRat 1 i - harmonicRat 1 j) / ((i : ℚ) - (j : ℚ)) := by
  simp [zetaRat, hij]

theorem zetaRat_symm (i j : ℕ) : zetaRat i j = zetaRat j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · rw [zetaRat_of_ne hij, zetaRat_of_ne (Ne.symm hij)]
    have hcast : (i : ℚ) ≠ (j : ℚ) := fun h => hij (Nat.cast_injective h)
    apply (div_eq_div_iff (sub_ne_zero.mpr hcast) (sub_ne_zero.mpr (Ne.symm hcast))).2
    ring


end

theorem centralCoeff_pos (l : ℕ) : 0 < centralCoeff l := by
  unfold centralCoeff
  apply div_pos
  · exact_mod_cast Nat.centralBinom_pos l
  · positivity

theorem centralCoeff_ne_zero (l : ℕ) : centralCoeff l ≠ 0 :=
  ne_of_gt (centralCoeff_pos l)

theorem centralCoeff_step (l : ℕ) :
    ((2 * l + 2 : ℕ) : ℚ) * centralCoeff (l + 1) =
      ((2 * l + 1 : ℕ) : ℚ) * centralCoeff l := by
  have hc : ((l + 1 : ℕ) : ℚ) * (((2 * (l + 1)).choose (l + 1) : ℕ) : ℚ) =
      2 * ((2 * l + 1 : ℕ) : ℚ) * (((2 * l).choose l : ℕ) : ℚ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ l
  have hp : (4 : ℚ) ^ l ≠ 0 := pow_ne_zero l (by norm_num)
  unfold centralCoeff
  rw [pow_succ]
  push_cast at hc ⊢
  field_simp
  nlinarith only [hc]










end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Analysis.ContactSeries
namespace OAI

noncomputable section

namespace InternalCatalan

open PowerSeries

def centralKernelSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun d => centralCoeffKernel (d : ℤ))

@[simp] theorem coeff_centralKernelSeries (d : ℕ) :
    PowerSeries.coeff d centralKernelSeries = centralCoeffKernel (d : ℤ) :=
  PowerSeries.coeff_mk d _

@[simp] theorem constantCoeff_centralKernelSeries :
    PowerSeries.constantCoeff centralKernelSeries = 1 := by
  simp [centralKernelSeries]

theorem centralCoeffKernel_nat_even (l : ℕ) :
    centralCoeffKernel ((2 * l : ℕ) : ℤ) = centralCoeff l := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using centralCoeffKernel_two_mul l

theorem centralCoeffKernel_nat_odd (l : ℕ) :
    centralCoeffKernel ((2 * l + 1 : ℕ) : ℤ) = 0 := by
  apply centralCoeffKernel_of_odd
  omega

theorem centralCoeffKernel_nat_step (d : ℕ) :
    ((d + 2 : ℕ) : ℚ) * centralCoeffKernel ((d + 2 : ℕ) : ℤ) =
      ((d + 1 : ℕ) : ℚ) * centralCoeffKernel (d : ℤ) := by
  by_cases hd : d % 2 = 0
  · obtain ⟨l, rfl⟩ : ∃ l : ℕ, d = 2 * l := ⟨d / 2, by omega⟩
    rw [show 2 * l + 2 = 2 * (l + 1) by omega,
      centralCoeffKernel_nat_even, centralCoeffKernel_nat_even]
    convert centralCoeff_step l using 1 <;> push_cast <;> ring
  · obtain ⟨l, rfl⟩ : ∃ l : ℕ, d = 2 * l + 1 := ⟨d / 2, by omega⟩
    rw [show 2 * l + 1 + 2 = 2 * (l + 1) + 1 by omega,
      centralCoeffKernel_nat_odd, centralCoeffKernel_nat_odd]
    simp



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Analysis.LogMonomial
namespace OAI

open MeasureTheory Real Set Filter intervalIntegral
open scoped Topology Interval

namespace InternalCatalan

theorem intervalIntegrable_pow_neg_log (k : ℕ) :
    IntervalIntegrable (fun x : ℝ => x ^ k * (-Real.log x)) volume 0 1 := by
  exact intervalIntegrable_log'.neg.continuousOn_mul (continuous_pow k).continuousOn

theorem integral_pow_neg_log (k : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ k * (-Real.log x)) =
      1 / ((k + 1 : ℕ) : ℝ) ^ 2 := by
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hpow : Tendsto (fun x : ℝ => x ^ (k + 1)) (𝓝[>] 0) (𝓝 0) := by
    simpa using
      (tendsto_nhdsWithin_of_tendsto_nhds
        (Filter.tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0))).pow (k + 1)
  have hlog : Tendsto (fun x : ℝ => Real.log x * x ^ (k + 1))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (tendsto_log_mul_rpow_nhdsGT_zero
        (show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) by positivity))
  have h := integral_eq_sub_of_hasDerivAt_of_tendsto
    (f := fun x : ℝ => x ^ (k + 1) / ((k + 1 : ℕ) : ℝ) ^ 2 -
      Real.log x * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ))
    (f' := fun x : ℝ => x ^ k * (-Real.log x))
    (fa := 0) (fb := 1 / ((k + 1 : ℕ) : ℝ) ^ 2)
    (show (0 : ℝ) < 1 by norm_num)
    (by
      intro x hx
      convert ((hasDerivAt_pow (k + 1) x).div_const
        (((k + 1 : ℕ) : ℝ) ^ 2)).sub
        (((Real.hasDerivAt_log hx.1.ne').mul
          (hasDerivAt_pow (k + 1) x)).div_const ((k + 1 : ℕ) : ℝ)) using 1
      · rfl
      simp only [Nat.add_sub_cancel, pow_succ]
      field_simp [hx.1.ne', hk]
      ring)
    (intervalIntegrable_pow_neg_log k)
    (by
      simpa using ((hpow.div_const (((k + 1 : ℕ) : ℝ) ^ 2)).sub
        (hlog.div_const ((k + 1 : ℕ) : ℝ))))
    (by
      have hc : ContinuousAt (fun x : ℝ =>
          x ^ (k + 1) / ((k + 1 : ℕ) : ℝ) ^ 2 -
          Real.log x * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) 1 := by
        fun_prop (disch := positivity)
      simpa using tendsto_nhdsWithin_of_tendsto_nhds hc.tendsto)
  simpa using h

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.TwoAdicQuadratic
namespace OAI

namespace InternalCatalan

section

def L (N : ℕ) : ℕ := 59 * N



theorem L_eq_n_add_b_add_q (N : ℕ) : L N = n N + b N + q N := by
  unfold L n b q
  omega

theorem Cdegree_eq_L_add_g (N : ℕ) : Cdegree N = L N + g N := by
  unfold Cdegree L g
  omega

theorem H_eq_Cdegree_add_h (N : ℕ) : H N = Cdegree N + h N := by
  unfold H Cdegree h
  omega



theorem rawColumn_lt_L {N k v : ℕ} (hk : k < n N) (hv : v ≤ q N) :
    b N + k + v < L N := by
  rw [L_eq_n_add_b_add_q]
  omega


theorem rowDistance_le {N r : ℕ} (hN : 0 < N) (hr : r < n N) :
    rowDistance N r ≤ n N - 1 - g N := by
  unfold rowDistance rowOffset n g at *
  omega

theorem rowDistance_lt_Cdegree {N r : ℕ} (hN : 0 < N) (hr : r < n N) :
    rowDistance N r < Cdegree N := by
  have hd := rowDistance_le hN hr
  unfold n g Cdegree at *
  omega











end

noncomputable section
open Set
open scoped BigOperators



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

theorem reversedRow_coeff_eq_zero_of_ge (C : ℕ) (F : ℤ[X])
    {i : ℕ} (hi : C ≤ i) : (reversedRow C F).coeff i = 0 := by
  rw [reversedRow_coeff, if_neg (by omega)]

theorem reversedRow_natDegree_le (C : ℕ) (F : ℤ[X]) :
    (reversedRow C F).natDegree ≤ C - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  apply reversedRow_coeff_eq_zero_of_ge
  omega

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

theorem natDegree_one_sub_X : (1 - X : ℤ[X]).natDegree = 1 := by
  rw [Polynomial.natDegree_sub]
  simpa using (Polynomial.natDegree_X_sub_C (1 : ℤ))

theorem rowFactor_natDegree_le (N : ℕ) :
    ((1 - X : ℤ[X]) ^ h N).natDegree ≤ h N := by
  calc
    _ ≤ h N * (1 - X : ℤ[X]).natDegree := Polynomial.natDegree_pow_le
    _ = h N := by rw [InternalCatalan.natDegree_one_sub_X, mul_one]

theorem rowP_natDegree_le {N : ℕ} (hN : 0 < N) (r : ℕ) :
    (rowP N r).natDegree ≤ H N - 1 := by
  unfold rowP
  calc
    _ ≤ ((1 - X : ℤ[X]) ^ h N).natDegree +
        (reversedRow (Cdegree N) (Chebyshev.T ℤ (rowDistance N r : ℤ))).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ h N + (Cdegree N - 1) :=
      Nat.add_le_add (rowFactor_natDegree_le N) (reversedRow_natDegree_le _ _)
    _ ≤ H N - 1 := by unfold h Cdegree H; omega

theorem rowD_natDegree_le {N : ℕ} (hN : 0 < N) (r : ℕ) :
    (rowD N r).natDegree ≤ H N - 1 := by
  unfold rowD
  rw [mul_assoc]
  calc
    _ ≤ (((1 - X : ℤ[X]) ^ h N) *
        reversedRow (Cdegree N) (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1))).natDegree :=
      Polynomial.natDegree_C_mul_le _ _
    _ ≤ ((1 - X : ℤ[X]) ^ h N).natDegree +
        (reversedRow (Cdegree N)
          (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1))).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ h N + (Cdegree N - 1) :=
      Nat.add_le_add (rowFactor_natDegree_le N) (reversedRow_natDegree_le _ _)
    _ ≤ H N - 1 := by unfold h Cdegree H; omega


theorem rowD_eq_zero_of_distance_zero {N r : ℕ} (hd : rowDistance N r = 0) :
    rowD N r = 0 := by
  simp [rowD, hd]


theorem rowP_coeff_eq_zero_of_ge {N r i : ℕ} (hN : 0 < N)
    (hi : H N ≤ i) : (rowP N r).coeff i = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have hdeg := rowP_natDegree_le hN r
  have hH : 0 < H N := by unfold H; omega
  omega

theorem rowD_coeff_eq_zero_of_ge {N r i : ℕ} (hN : 0 < N)
    (hi : H N ≤ i) : (rowD N r).coeff i = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have hdeg := rowD_natDegree_le hN r
  have hH : 0 < H N := by unfold H; omega
  omega





















end

section

open scoped BigOperators









end

section

open Polynomial

theorem rowDistance_of_le_g {N r : ℕ} (hrg : r ≤ g N) :
    rowDistance N r = g N - r := by
  unfold rowDistance rowOffset
  omega

theorem rowP_coeff_eq_zero_of_lt_left_contact {N r i : ℕ} (hN : 0 < N)
    (hr : r < n N) (hrg : r ≤ g N) (hi : i < L N - 1) :
    (rowP N r).coeff i = 0 := by
  have hdist := rowDistance_of_le_g hrg
  have hmin : L N - 1 ≤ Cdegree N - 1 - rowDistance N r := by
    rw [hdist]
    unfold L Cdegree g
    omega
  unfold rowP
  apply coeff_mul_eq_zero_below_right _ _ (L N - 1) _ hi
  intro j hj
  apply reversedRow_coeff_eq_zero_of_lt _ (rowDistance N r) _
  · simp [Chebyshev.natDegree_T]
  · exact rowDistance_lt_Cdegree hN hr
  · exact lt_of_lt_of_le hj hmin

theorem rowD_coeff_eq_zero_of_lt_left_contact {N r i : ℕ} (hN : 0 < N)
    (hr : r < n N) (hrg : r ≤ g N) (hi : i < L N) :
    (rowD N r).coeff i = 0 := by
  by_cases hd : rowDistance N r = 0
  · simp [rowD_eq_zero_of_distance_zero hd]
  · have hdist := rowDistance_of_le_g hrg
    have hmin : L N ≤ Cdegree N - 1 - (rowDistance N r - 1) := by
      rw [hdist]
      rw [hdist] at hd
      unfold L Cdegree g at *
      omega
    unfold rowD
    apply coeff_mul_eq_zero_below_right _ _ (L N) _ hi
    intro j hj
    apply reversedRow_coeff_eq_zero_of_lt _ (rowDistance N r - 1) _
    · simp [Chebyshev.natDegree_U]
    · have hdc := rowDistance_lt_Cdegree hN hr
      omega
    · exact lt_of_lt_of_le hj hmin

theorem row_contact_of_le_g {N r j : ℕ} (hN : 0 < N)
    (hr : r < n N) (hrg : r ≤ g N) (hj : j < L N) :
    (∑ i ∈ Finset.range (H N),
      ((rowP N r).coeff i : ℚ) * centralCoeffKernel ((j : ℤ) - i - 1)) =
      ((rowD N r).coeff j : ℚ) := by
  rw [rowD_coeff_eq_zero_of_lt_left_contact hN hr hrg hj, Int.cast_zero]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hil : i < L N - 1
  · rw [rowP_coeff_eq_zero_of_lt_left_contact hN hr hrg hil, Int.cast_zero, zero_mul]
  · rw [centralCoeffKernel_of_neg (by omega : (j : ℤ) - i - 1 < 0), mul_zero]



variable {K : Type*} [Field K]




end

open Polynomial



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.MixedMajorant
namespace OAI

noncomputable section

namespace InternalCatalan

theorem mixed_denominator_rpow_bound {t s : ℝ}
    (ht : |t| < 1) (hs0 : 0 < s) (hs1 : s < 1) :
    (1 - t * s)⁻¹ ≤
      (1 - |t|) ^ (-(1 / 4) : ℝ) * (1 - s) ^ (-(3 / 4) : ℝ) := by
  have hts_abs : t * s ≤ |t| := calc
    t * s ≤ |t| * s := mul_le_mul_of_nonneg_right (le_abs_self t) hs0.le
    _ ≤ |t| := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hs1.le (abs_nonneg t)
  have hts_s : t * s ≤ s := calc
    t * s ≤ 1 * s :=
      mul_le_mul_of_nonneg_right ((le_abs_self t).trans ht.le) hs0.le
    _ = s := one_mul s
  have ha : 0 < 1 - |t| := sub_pos.mpr ht
  have hb : 0 < 1 - s := sub_pos.mpr hs1
  have hDa : 1 - |t| ≤ 1 - t * s := sub_le_sub_left hts_abs 1
  have hDb : 1 - s ≤ 1 - t * s := sub_le_sub_left hts_s 1
  have hD : 0 < 1 - t * s := ha.trans_le hDa
  calc
    (1 - t * s)⁻¹ =
        (1 - t * s) ^ (-(1 / 4) : ℝ) *
          (1 - t * s) ^ (-(3 / 4) : ℝ) := by
      rw [← Real.rpow_add hD,
        show -(1 / 4 : ℝ) + -(3 / 4 : ℝ) = (-1 : ℝ) by norm_num,
        Real.rpow_neg_one]
    _ ≤ (1 - |t|) ^ (-(1 / 4) : ℝ) * (1 - s) ^ (-(3 / 4) : ℝ) :=
      mul_le_mul
        (Real.rpow_le_rpow_of_nonpos ha hDa (by norm_num))
        (Real.rpow_le_rpow_of_nonpos hb hDb (by norm_num))
        (Real.rpow_nonneg hD.le _) (Real.rpow_nonneg ha.le _)

theorem scalar_weight_le_rpow {t : ℝ} (ht : |t| < 1) :
    |t| / Real.sqrt (1 - t ^ 2) ≤ (1 - |t|) ^ (-(1 / 2) : ℝ) := by
  have ht_sq : t ^ 2 ≤ |t| := by
    have hmul := mul_le_mul_of_nonneg_left ht.le (abs_nonneg t)
    nlinarith [sq_abs t]
  have ha : 0 < 1 - |t| := sub_pos.mpr ht
  have haq : 1 - |t| ≤ 1 - t ^ 2 := sub_le_sub_left ht_sq 1
  have hq : 0 < 1 - t ^ 2 := ha.trans_le haq
  calc
    |t| / Real.sqrt (1 - t ^ 2) ≤ 1 / Real.sqrt (1 - t ^ 2) :=
      div_le_div_of_nonneg_right ht.le (Real.sqrt_nonneg _)
    _ = (1 - t ^ 2) ^ (-(1 / 2) : ℝ) := by
      rw [one_div, Real.sqrt_eq_rpow, Real.rpow_neg hq.le]
    _ ≤ (1 - |t|) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos ha haq (by norm_num)

theorem mixed_kernel_norm_le {t s : ℝ} (i j : ℕ)
    (ht : |t| < 1) (hs0 : 0 < s) (hs1 : s < 1) :
    ‖(|t| / Real.sqrt (1 - t ^ 2)) * (t ^ i * s ^ j) / (1 - t * s)‖ ≤
      (1 - |t|) ^ (-(3 / 4) : ℝ) * (1 - s) ^ (-(3 / 4) : ℝ) := by
  have ha : 0 < 1 - |t| := sub_pos.mpr ht
  have hts : t * s < 1 := calc
    t * s ≤ |t| * s := mul_le_mul_of_nonneg_right (le_abs_self t) hs0.le
    _ ≤ |t| := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hs1.le (abs_nonneg t)
    _ < 1 := ht
  have hD : 0 < 1 - t * s := sub_pos.mpr hts
  have hw : 0 ≤ |t| / Real.sqrt (1 - t ^ 2) :=
    div_nonneg (abs_nonneg t) (Real.sqrt_nonneg _)
  have hti : |t| ^ i ≤ 1 := pow_le_one₀ (abs_nonneg t) ht.le
  have hsj : s ^ j ≤ 1 := pow_le_one₀ hs0.le hs1.le
  have hm : |t| ^ i * s ^ j ≤ 1 := by
    have h := mul_le_mul hti hsj (pow_nonneg hs0.le j) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using h
  calc
    ‖(|t| / Real.sqrt (1 - t ^ 2)) * (t ^ i * s ^ j) / (1 - t * s)‖ =
        ((|t| / Real.sqrt (1 - t ^ 2)) * (|t| ^ i * s ^ j)) *
          (1 - t * s)⁻¹ := by
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hw,
        abs_mul, abs_pow, abs_pow, abs_of_nonneg hs0.le, abs_of_pos hD,
        div_eq_mul_inv]
    _ ≤ ((|t| / Real.sqrt (1 - t ^ 2)) * 1) * (1 - t * s)⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hw)
        (inv_nonneg.mpr hD.le)
    _ = (|t| / Real.sqrt (1 - t ^ 2)) * (1 - t * s)⁻¹ := by rw [mul_one]
    _ ≤ (1 - |t|) ^ (-(1 / 2) : ℝ) *
        ((1 - |t|) ^ (-(1 / 4) : ℝ) * (1 - s) ^ (-(3 / 4) : ℝ)) :=
      mul_le_mul (scalar_weight_le_rpow ht) (mixed_denominator_rpow_bound ht hs0 hs1)
        (inv_nonneg.mpr hD.le) (Real.rpow_nonneg ha.le _)
    _ = (1 - |t|) ^ (-(3 / 4) : ℝ) * (1 - s) ^ (-(3 / 4) : ℝ) := by
      rw [← mul_assoc, ← Real.rpow_add ha,
        show -(1 / 2 : ℝ) + -(1 / 4 : ℝ) = -(3 / 4 : ℝ) by norm_num]

theorem norm_mixedKernel_le (i j : ℕ) {t s : ℝ}
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    ‖(|t| / Real.sqrt (1 - t ^ 2)) * (t ^ i * s ^ j) / (1 - t * s)‖ ≤
      (1 - |t|) ^ (-(3 / 4) : ℝ) * (1 - s) ^ (-(3 / 4) : ℝ) :=
  mixed_kernel_norm_le i j (abs_lt.mpr ht) hs.1 hs.2

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.ScalarMomentDecay
namespace OAI

noncomputable section

namespace InternalCatalan

section

open MeasureTheory Set Real
open scoped Interval

def scalarMoment (i : ℕ) : ℝ :=
  ∫ t in (-1 : ℝ)..1, t ^ i * (|t| / Real.sqrt (1 - t ^ 2))

private theorem sine_deriv_nonneg (x : ℝ)
    (hx : x ∈ Ioo (min (-(π / 2)) (π / 2)) (max (-(π / 2)) (π / 2))) :
    0 ≤ cos x := by
  have hp : -(π / 2) ≤ π / 2 := by linarith [pi_pos]
  rw [min_eq_left hp, max_eq_right hp] at hx
  exact (cos_pos_of_mem_Ioo hx).le

private theorem scalar_sine_cancel (i : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (-(π / 2)) (π / 2)) :
    (sin x ^ i * (|sin x| / sqrt (1 - sin x ^ 2))) * cos x =
      sin x ^ i * |sin x| := by
  rw [← cos_eq_sqrt_one_sub_sin_sq hx.1.le hx.2.le]
  have hc : cos x ≠ 0 := (cos_pos_of_mem_Ioo hx).ne'
  field_simp

theorem scalarMoment_eq_sine (i : ℕ) :
    scalarMoment i =
      ∫ x in (-(π / 2))..(π / 2), sin x ^ i * |sin x| := by
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := -(π / 2)) (b := π / 2) (f := sin) (f' := cos)
    (g := fun t : ℝ => t ^ i * (|t| / sqrt (1 - t ^ 2)))
    continuous_sin.continuousOn (fun x _ => hasDerivAt_sin x) sine_deriv_nonneg
  simp only [Function.comp_apply, sin_neg, sin_pi_div_two] at hsub
  unfold scalarMoment
  rw [← hsub]
  apply intervalIntegral.integral_congr_Ioo_of_le (by linarith [pi_pos])
  intro x hx
  exact scalar_sine_cancel i hx

theorem intervalIntegrable_scalarMoment (i : ℕ) :
    IntervalIntegrable (fun t : ℝ => t ^ i * (|t| / sqrt (1 - t ^ 2)))
      volume (-1) 1 := by
  have hsub := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := -(π / 2)) (b := π / 2) (f := sin) (f' := cos)
    (g := fun t : ℝ => t ^ i * (|t| / sqrt (1 - t ^ 2)))
    continuous_sin.continuousOn (fun x _ => hasDerivAt_sin x) sine_deriv_nonneg
  simp only [sin_neg, sin_pi_div_two] at hsub
  apply hsub.mp
  have hc : Continuous (fun x : ℝ => sin x ^ i * |sin x|) := by fun_prop
  apply (hc.intervalIntegrable (-(π / 2)) (π / 2)).congr_uIoo
  intro x hx
  rw [uIoo_of_le (show -(π / 2) ≤ π / 2 by linarith [pi_pos])] at hx
  exact (scalar_sine_cancel i hx).symm

theorem scalarMoment_integrand_odd (k : ℕ) (t : ℝ) :
    (-t) ^ (2 * k + 1) * (|-t| / Real.sqrt (1 - (-t) ^ 2)) =
      -(t ^ (2 * k + 1) * (|t| / Real.sqrt (1 - t ^ 2))) := by
  simp only [abs_neg, neg_sq, pow_add, pow_mul, pow_one]
  ring

theorem scalarMoment_odd (k : ℕ) : scalarMoment (2 * k + 1) = 0 := by
  have h := intervalIntegral.integral_comp_neg
    (a := (-1 : ℝ)) (b := (1 : ℝ))
    (fun t : ℝ => t ^ (2 * k + 1) * (|t| / Real.sqrt (1 - t ^ 2)))
  simp only [neg_neg, scalarMoment_integrand_odd, intervalIntegral.integral_neg] at h
  change -scalarMoment (2 * k + 1) = scalarMoment (2 * k + 1) at h
  linarith


private theorem interval_even_double (f : ℝ → ℝ) (hf : Function.Even f) {a : ℝ}
    (hint : IntervalIntegrable f volume (-a) a) (ha : 0 ≤ a) :
    (∫ x in -a..a, f x) = 2 * ∫ x in (0 : ℝ)..a, f x := by
  have h0 : (0 : ℝ) ∈ Set.uIcc (-a) a := by
    rw [Set.uIcc_of_le (by linarith : -a ≤ a)]
    exact ⟨by linarith, ha⟩
  obtain ⟨hl, hr⟩ := (IntervalIntegrable.trans_iff h0).mp hint
  have hf' (x : ℝ) : f (-x) = f x := hf x
  have hleft : (∫ x in -a..0, f x) = ∫ x in (0 : ℝ)..a, f x := by
    simpa only [hf', neg_zero] using
      (intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := a) f).symm
  calc
    (∫ x in -a..a, f x) = (∫ x in -a..0, f x) + ∫ x in (0 : ℝ)..a, f x :=
      (intervalIntegral.integral_add_adjacent_intervals hl hr).symm
    _ = 2 * ∫ x in (0 : ℝ)..a, f x := by rw [hleft]; ring

theorem scalarMoment_even_eq_sine (l : ℕ) :
    scalarMoment (2 * l) =
      2 * (∫ x in (0 : ℝ)..(π / 2), sin x ^ (2 * l + 1)) := by
  rw [scalarMoment_eq_sine]
  have hf : Function.Even (fun x : ℝ => sin x ^ (2 * l) * |sin x|) := by
    intro x
    simp only [sin_neg, abs_neg, pow_mul, neg_sq]
  have hc : Continuous (fun x : ℝ => sin x ^ (2 * l) * |sin x|) := by fun_prop
  rw [interval_even_double _ hf (hc.intervalIntegrable (-(π / 2)) (π / 2)) (by positivity)]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le (by positivity)
  intro x hx
  have hs : 0 ≤ sin x := sin_nonneg_of_nonneg_of_le_pi hx.1.le (by linarith [hx.2, pi_pos])
  change sin x ^ (2 * l) * |sin x| = sin x ^ (2 * l + 1)
  rw [abs_of_nonneg hs, pow_succ]

theorem two_integral_sine_odd_eq_momentScalar (l : ℕ) :
    2 * (∫ x in (0 : ℝ)..(π / 2), sin x ^ (2 * l + 1)) =
      (momentScalar (2 * l) : ℝ) := by
  induction l with
  | zero => simp
  | succ l ih =>
    have he : 2 * (l + 1) + 1 = (2 * l + 1) + 2 := by omega
    have hrec := integral_sin_pow (a := 0) (b := π / 2) (2 * l + 1)
    have hexp : 0 < 2 * l + 1 + 1 := by omega
    simp only [sin_zero, zero_pow (Nat.ne_of_gt hexp), cos_zero, zero_mul,
      sin_pi_div_two, one_pow, cos_pi_div_two, mul_zero, sub_self, zero_div,
      zero_add] at hrec
    rw [he, hrec]
    rw [show 2 * ((↑(2 * l + 1) + 1) / (↑(2 * l + 1) + 2) *
      (∫ x in (0 : ℝ)..(π / 2), sin x ^ (2 * l + 1))) =
        ((↑(2 * l + 1) + 1) / (↑(2 * l + 1) + 2)) *
          (2 * (∫ x in (0 : ℝ)..(π / 2), sin x ^ (2 * l + 1))) by ring, ih]
    rw [momentScalar_even, momentScalar_even]
    have hc : (↑(2 * l + 2) : ℝ) * (centralCoeff (l + 1) : ℝ) =
        (↑(2 * l + 1) : ℝ) * (centralCoeff l : ℝ) := by
      exact_mod_cast centralCoeff_step l
    have hc0 : (centralCoeff l : ℝ) ≠ 0 := by
      exact_mod_cast centralCoeff_ne_zero l
    have hc1 : (centralCoeff (l + 1) : ℝ) ≠ 0 := by
      exact_mod_cast centralCoeff_ne_zero (l + 1)
    push_cast at hc ⊢
    field_simp
    nlinarith only [hc]

theorem scalarMoment_eq_momentScalar (i : ℕ) :
    scalarMoment i = (momentScalar i : ℝ) := by
  rcases Nat.even_or_odd' i with ⟨l, rfl | rfl⟩
  · exact (scalarMoment_even_eq_sine l).trans
      (two_integral_sine_odd_eq_momentScalar l)
  · rw [scalarMoment_odd, momentScalar_odd, Rat.cast_zero]

@[simp] theorem scalarMoment_zero : scalarMoment 0 = 2 := by
  rw [scalarMoment_eq_momentScalar, momentScalar_zero]
  norm_num

end

open MeasureTheory Set Real Filter
open scoped Interval Topology

theorem tendsto_scalarMoment_zero :
    Tendsto scalarMoment atTop (𝓝 0) := by
  have h :
      Tendsto
        (fun n : ℕ => ∫ t in (-1 : ℝ)..1,
          t ^ n * (|t| / Real.sqrt (1 - t ^ 2)))
        atTop (𝓝 (∫ _t in (-1 : ℝ)..1, (0 : ℝ))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun t : ℝ => |t| / Real.sqrt (1 - t ^ 2))
    · exact Eventually.of_forall fun n =>
        (intervalIntegrable_scalarMoment n).aestronglyMeasurable_restrict_uIoc
    · refine Eventually.of_forall fun n => Eventually.of_forall ?_
      intro t ht
      rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
      have ht_abs : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2⟩
      have hw : 0 ≤ |t| / Real.sqrt (1 - t ^ 2) :=
        div_nonneg (abs_nonneg t) (Real.sqrt_nonneg _)
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hw]
      exact mul_le_of_le_one_left hw (pow_le_one₀ (abs_nonneg t) ht_abs)
    · simpa only [pow_zero, one_mul] using intervalIntegrable_scalarMoment 0
    · refine Eventually.of_forall ?_
      intro t ht
      rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
      by_cases ht1 : t = 1
      · subst t
        simpa only [one_pow, sub_self, Real.sqrt_zero, abs_one, div_zero, mul_zero]
          using (tendsto_const_nhds :
            Tendsto (fun _n : ℕ => (0 : ℝ)) atTop (𝓝 0))
      · have ht_abs : |t| < 1 :=
          abs_lt.mpr ⟨ht.1, (lt_or_eq_of_le ht.2).resolve_right ht1⟩
        simpa only [zero_mul] using
          (tendsto_pow_atTop_nhds_zero_of_abs_lt_one ht_abs).mul_const
            (|t| / Real.sqrt (1 - t ^ 2))
  change Tendsto
    (fun n : ℕ => ∫ t in (-1 : ℝ)..1,
      t ^ n * (|t| / Real.sqrt (1 - t ^ 2))) atTop (𝓝 0)
  simpa only [intervalIntegral.integral_zero] using h

theorem tendsto_momentScalar_zero :
    Tendsto (fun n : ℕ => (momentScalar n : ℝ)) atTop (𝓝 0) := by
  simpa only [scalarMoment_eq_momentScalar] using
    (show Tendsto (fun n : ℕ => scalarMoment n) atTop (𝓝 0) from
      tendsto_scalarMoment_zero)

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Analysis.MixedSeries
namespace OAI

noncomputable section

namespace InternalCatalan

open MeasureTheory Set Real Polynomial

private theorem intervalIntegrable_one_sub_rpow :
    IntervalIntegrable (fun t : ℝ => (1 - t) ^ (-(3 / 4) : ℝ)) volume 0 1 := by
  have h := intervalIntegral.intervalIntegrable_rpow'
    (a := (0 : ℝ)) (b := 1) (r := -(3 / 4)) (by norm_num)
  simpa only [sub_zero, sub_self] using (h.comp_sub_left 1).symm

private theorem intervalIntegrable_one_sub_abs_rpow :
    IntervalIntegrable (fun t : ℝ => (1 - |t|) ^ (-(3 / 4) : ℝ)) volume (-1) 1 := by
  have hp : IntervalIntegrable (fun t : ℝ => (1 - |t|) ^ (-(3 / 4) : ℝ))
      volume 0 1 := by
    apply intervalIntegrable_one_sub_rpow.congr_uIoo
    intro t ht
    rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    simp only [abs_of_pos ht.1]
  have hn : IntervalIntegrable (fun t : ℝ => (1 - |t|) ^ (-(3 / 4) : ℝ))
      volume (-1) 0 := by
    simpa only [zero_sub, sub_zero, abs_neg] using (hp.comp_sub_left 0).symm
  exact hn.trans hp

theorem integrable_mixedMajorant :
    Integrable (fun p : ℝ × ℝ =>
      (1 - |p.1|) ^ (-(3 / 4) : ℝ) * (1 - p.2) ^ (-(3 / 4) : ℝ))
      ((volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have ht := (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (by norm_num : (-1 : ℝ) ≤ 1)).mp intervalIntegrable_one_sub_abs_rpow
  have hs := (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (by norm_num : (0 : ℝ) ≤ 1)).mp intervalIntegrable_one_sub_rpow
  exact ht.mul_prod hs

theorem ae_mem_mixed_rectangle :
    ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Ioo (-1 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1)),
      p ∈ Ioo (-1 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
  apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioo.prod measurableSet_Ioo)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact ⟨ht, hs⟩

theorem integrable_mixedKernel (i j : ℕ) :
    Integrable (fun p : ℝ × ℝ =>
      (|p.1| / sqrt (1 - p.1 ^ 2)) * (p.1 ^ i * p.2 ^ j) / (1 - p.1 * p.2))
      ((volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      (|p.1| / sqrt (1 - p.1 ^ 2)) * (p.1 ^ i * p.2 ^ j) / (1 - p.1 * p.2)) := by
    fun_prop
  apply integrable_mixedMajorant.mono' hm.aestronglyMeasurable
  filter_upwards [ae_mem_mixed_rectangle] with p hp
  exact norm_mixedKernel_le i j hp.1 hp.2

theorem mixedMoment_X_pow_eq_integral_prod (i j : ℕ) :
    mixedMoment (X ^ i) (X ^ j) =
      ∫ p : ℝ × ℝ,
        (|p.1| / sqrt (1 - p.1 ^ 2)) * (p.1 ^ i * p.2 ^ j) / (1 - p.1 * p.2)
        ∂(volume.restrict (Ioo (-1 : ℝ) 1)).prod
          (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have h := integral_prod
    (fun p : ℝ × ℝ =>
      (|p.1| / sqrt (1 - p.1 ^ 2)) * (p.1 ^ i * p.2 ^ j) / (1 - p.1 * p.2))
    (integrable_mixedKernel i j)
  simpa only [mixedMoment, Polynomial.eval_pow, Polynomial.eval_X,
    intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo] using h.symm

theorem integral_prod_mixedMonomial (i j : ℕ) :
    (∫ p : ℝ × ℝ, (|p.1| / sqrt (1 - p.1 ^ 2)) * (p.1 ^ i * p.2 ^ j)
      ∂(volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) =
      (momentScalar i : ℝ) / ((j + 1 : ℕ) : ℝ) := by
  have ht : (∫ t in Ioo (-1 : ℝ) 1, t ^ i * (|t| / sqrt (1 - t ^ 2))) =
      scalarMoment i := by
    simp only [scalarMoment, intervalIntegral.integral_of_le
      (show (-1 : ℝ) ≤ 1 by norm_num), integral_Ioc_eq_integral_Ioo]
  have hs : (∫ s in Ioo (0 : ℝ) 1, s ^ j) = 1 / ((j + 1 : ℕ) : ℝ) := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num), integral_pow]
    simp only [one_pow, zero_pow (Nat.add_one_ne_zero _), sub_zero, Nat.cast_add,
      Nat.cast_one]
  calc
    _ = ∫ p : ℝ × ℝ, (p.1 ^ i * (|p.1| / sqrt (1 - p.1 ^ 2))) * p.2 ^ j
        ∂(volume.restrict (Ioo (-1 : ℝ) 1)).prod
          (volume.restrict (Ioo (0 : ℝ) 1)) := by
      apply integral_congr_ae
      filter_upwards with p
      ring
    _ = (scalarMoment i) * (1 / ((j + 1 : ℕ) : ℝ)) := by
      rw [integral_prod_mul (fun t : ℝ => t ^ i * (|t| / sqrt (1 - t ^ 2)))
        (fun s : ℝ => s ^ j), ht, hs]
    _ = _ := by rw [scalarMoment_eq_momentScalar]; ring

theorem mixedMoment_X_pow_step (i j : ℕ) :
    mixedMoment (X ^ i) (X ^ j) - mixedMoment (X ^ (i + 1)) (X ^ (j + 1)) =
      (momentScalar i : ℝ) / ((j + 1 : ℕ) : ℝ) := by
  rw [mixedMoment_X_pow_eq_integral_prod, mixedMoment_X_pow_eq_integral_prod,
    ← integral_sub (integrable_mixedKernel i j) (integrable_mixedKernel (i + 1) (j + 1))]
  rw [← integral_prod_mixedMonomial i j]
  apply integral_congr_ae
  filter_upwards [ae_mem_mixed_rectangle] with p hp
  have habs : |p.1| < 1 := abs_lt.mpr hp.1
  have ht : p.1 * p.2 < 1 := by
    have hle : p.1 * p.2 ≤ |p.1| * p.2 := mul_le_mul_of_nonneg_right (le_abs_self _) hp.2.1.le
    have hlt : |p.1| * p.2 < 1 := by nlinarith [abs_nonneg p.1, habs, hp.2.1, hp.2.2]
    exact hle.trans_lt hlt
  have hd : 1 - p.1 * p.2 ≠ 0 := by linarith
  simp only [pow_succ]
  rw [← sub_div]
  apply (div_eq_iff hd).mpr
  ring

open MeasureTheory Set Real Polynomial
open scoped BigOperators Topology

theorem hasSum_mixedKernel (i j : ℕ) {t s : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun u : ℕ =>
      (|t| / sqrt (1 - t ^ 2)) * (t ^ (i + u) * s ^ (j + u)))
      ((|t| / sqrt (1 - t ^ 2)) * (t ^ i * s ^ j) / (1 - t * s)) := by
  have ha : |t| < 1 := abs_lt.mpr ht
  have hts : |t * s| < 1 := by
    rw [abs_mul, abs_of_pos hs.1]
    have hle : |t| * s ≤ |t| := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hs.2.le (abs_nonneg t)
    exact hle.trans_lt ha
  convert (hasSum_geometric_of_abs_lt_one hts).mul_left
    ((|t| / sqrt (1 - t ^ 2)) * (t ^ i * s ^ j)) using 1
  · rfl
  · ext u
    simp only [pow_add, mul_pow]
    ring
  · rfl

theorem integrable_abs_mixedKernel (i j : ℕ) :
    Integrable (fun p : ℝ × ℝ =>
      (|p.1| / sqrt (1 - p.1 ^ 2)) * (|p.1| ^ i * p.2 ^ j) / (1 - |p.1| * p.2))
      ((volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      (|p.1| / sqrt (1 - p.1 ^ 2)) * (|p.1| ^ i * p.2 ^ j) / (1 - |p.1| * p.2)) := by
    fun_prop
  apply integrable_mixedMajorant.mono' hm.aestronglyMeasurable
  filter_upwards [ae_mem_mixed_rectangle] with p hp
  have ht : |p.1| ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by linarith [abs_nonneg p.1], abs_lt.mpr hp.1⟩
  simpa only [abs_abs, sq_abs] using norm_mixedKernel_le i j ht hp.2

theorem hasSum_mixedMoment_X_pow (i j : ℕ) :
    HasSum (fun u : ℕ =>
      (momentScalar (i + u) : ℝ) / ((j + u + 1 : ℕ) : ℝ))
      (mixedMoment (X ^ i) (X ^ j)) := by
  let μ := (volume.restrict (Ioo (-1 : ℝ) 1)).prod
    (volume.restrict (Ioo (0 : ℝ) 1))
  let F : ℕ → ℝ × ℝ → ℝ := fun u p =>
    (|p.1| / sqrt (1 - p.1 ^ 2)) * (p.1 ^ (i + u) * p.2 ^ (j + u))
  let B : ℕ → ℝ × ℝ → ℝ := fun u p =>
    (|p.1| / sqrt (1 - p.1 ^ 2)) * (|p.1| ^ (i + u) * p.2 ^ (j + u))
  let G : ℝ × ℝ → ℝ := fun p =>
    (|p.1| / sqrt (1 - p.1 ^ 2)) * (|p.1| ^ i * p.2 ^ j) / (1 - |p.1| * p.2)
  have hsumB : ∀ᵐ p ∂μ, HasSum (fun u => B u p) (G p) := by
    filter_upwards [ae_mem_mixed_rectangle] with p hp
    have ht : |p.1| ∈ Ioo (-1 : ℝ) 1 :=
      ⟨by linarith [abs_nonneg p.1], abs_lt.mpr hp.1⟩
    simpa only [B, G, abs_abs, sq_abs] using hasSum_mixedKernel i j ht hp.2
  have hsum_int : Integrable (fun p => ∑' u, B u p) μ := by
    apply (integrable_abs_mixedKernel i j).congr
    filter_upwards [hsumB] with p hp
    exact hp.tsum_eq.symm
  have hbound : ∀ u, ∀ᵐ p ∂μ, ‖F u p‖ ≤ B u p := by
    intro u
    filter_upwards [ae_mem_mixed_rectangle] with p hp
    have hw : 0 ≤ |p.1| / sqrt (1 - p.1 ^ 2) :=
      div_nonneg (abs_nonneg _) (sqrt_nonneg _)
    simp only [F, B, Real.norm_eq_abs, abs_mul, abs_of_nonneg hw,
      abs_pow, abs_of_pos hp.2.1, le_refl]
  have hlim : ∀ᵐ p ∂μ, HasSum (fun u => F u p)
      ((|p.1| / sqrt (1 - p.1 ^ 2)) * (p.1 ^ i * p.2 ^ j) / (1 - p.1 * p.2)) := by
    filter_upwards [ae_mem_mixed_rectangle] with p hp
    exact hasSum_mixedKernel i j hp.1 hp.2
  have hmeas (u : ℕ) : AEStronglyMeasurable (F u) μ := by
    have hm : Measurable (F u) := by dsimp only [F]; fun_prop
    exact hm.aestronglyMeasurable
  have h := hasSum_integral_of_dominated_convergence B
    hmeas hbound
    (hsumB.mono fun _ hp => hp.summable) hsum_int hlim
  have hterm (u : ℕ) : (∫ p, F u p ∂μ) =
      (momentScalar (i + u) : ℝ) / ((j + u + 1 : ℕ) : ℝ) :=
    integral_prod_mixedMonomial (i + u) (j + u)
  simp only [hterm] at h
  rw [mixedMoment_X_pow_eq_integral_prod]
  exact h

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.Contract
namespace OAI

noncomputable section

namespace InternalCatalan

def catalan : ℝ :=
  ∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Analysis.ZetaIntegral
namespace OAI

noncomputable section

namespace InternalCatalan

section

open Filter
open scoped BigOperators Topology

def zetaTerm (i j u : ℕ) : ℝ :=
  1 / (((i + u + 1 : ℕ) : ℝ) * ((j + u + 1 : ℕ) : ℝ))

def zetaSeries (i j : ℕ) : ℝ := ∑' u : ℕ, zetaTerm i j u

theorem zetaTerm_nonneg (i j u : ℕ) : 0 ≤ zetaTerm i j u := by
  unfold zetaTerm
  positivity

theorem zetaTerm_le_inverse_square (i j u : ℕ) :
    zetaTerm i j u ≤ 1 / ((u + 1 : ℕ) : ℝ) ^ 2 := by
  unfold zetaTerm
  apply one_div_le_one_div_of_le (by positivity)
  have hi : ((u + 1 : ℕ) : ℝ) ≤ ((i + u + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show u + 1 ≤ i + u + 1 by omega)
  have hj : ((u + 1 : ℕ) : ℝ) ≤ ((j + u + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show u + 1 ≤ j + u + 1 by omega)
  simpa only [pow_two] using
    mul_le_mul hi hj (by positivity) (by positivity)

theorem summable_inverse_square_succ :
    Summable (fun u : ℕ => 1 / ((u + 1 : ℕ) : ℝ) ^ 2) := by
  have h : Summable (fun u : ℕ => 1 / (u : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)
  exact h.comp_injective (show Function.Injective (fun u : ℕ => u + 1) by
    intro a b hab
    change a + 1 = b + 1 at hab
    omega)

theorem summable_zetaTerm (i j : ℕ) : Summable (zetaTerm i j) := by
  apply summable_inverse_square_succ.of_norm_bounded
  intro u
  rw [Real.norm_eq_abs, abs_of_nonneg (zetaTerm_nonneg i j u)]
  exact zetaTerm_le_inverse_square i j u


theorem hasSum_zetaSeries (i j : ℕ) : HasSum (zetaTerm i j) (zetaSeries i j) :=
  (summable_zetaTerm i j).hasSum

theorem tendsto_partial_sums_zetaSeries (i j : ℕ) :
    Tendsto (fun m : ℕ => ∑ u ∈ Finset.range m, zetaTerm i j u)
      atTop (𝓝 (zetaSeries i j)) :=
  (hasSum_zetaSeries i j).tendsto_sum_nat

theorem zetaSeries_nonneg (i j : ℕ) : 0 ≤ zetaSeries i j :=
  tsum_nonneg (zetaTerm_nonneg i j)

theorem zetaSeries_symm (i j : ℕ) : zetaSeries i j = zetaSeries j i := by
  apply tsum_congr
  intro u
  simp only [zetaTerm, mul_comm]

theorem zetaTerm_shift (i j u m : ℕ) :
    zetaTerm i j (u + m) = zetaTerm (i + m) (j + m) u := by
  simp only [zetaTerm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem zetaSeries_split (i j m : ℕ) :
    (∑ u ∈ Finset.range m, zetaTerm i j u) + zetaSeries (i + m) (j + m) =
      zetaSeries i j := by
  have h := (summable_zetaTerm i j).sum_add_tsum_nat_add m
  simpa only [zetaTerm_shift, zetaSeries] using h

theorem zetaSeries_step (i j : ℕ) :
    zetaSeries i j - zetaSeries (i + 1) (j + 1) =
      1 / (((i + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) := by
  have h := zetaSeries_split i j 1
  simp only [Finset.sum_range_one, zetaTerm, Nat.add_zero] at h
  linarith



theorem zetaSeries_diagonal (i : ℕ) :
    zetaSeries i i = (zetaRat i i : ℝ) + zetaSeries 0 0 := by
  have h := zetaSeries_split 0 0 i
  have hs : (∑ u ∈ Finset.range i, zetaTerm 0 0 u) = (harmonicRat 2 i : ℝ) := by
    simp [zetaTerm, harmonicRat, pow_two]
  rw [hs] at h
  simp only [Nat.zero_add] at h
  rw [zetaRat_diagonal, Rat.cast_neg]
  linarith

end

section

open Filter
open scoped Topology

theorem summable_odd_reciprocal_squares :
    Summable (fun j : ℕ => 1 / ((2 * j + 1 : ℕ) : ℝ) ^ 2) := by
  have h : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)
  exact h.comp_injective (show Function.Injective (fun j : ℕ => 2 * j + 1) by
    intro i j hij
    change 2 * i + 1 = 2 * j + 1 at hij
    omega)






end

section

open MeasureTheory
open scoped BigOperators Topology

theorem hasSum_zetaKernel (i j : ℕ) {t s : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    HasSum (fun u : ℕ => t ^ (i + u) * s ^ (j + u))
      (t ^ i * s ^ j / (1 - t * s)) := by
  have hts : |t * s| < 1 := by
    rw [abs_of_nonneg (mul_nonneg ht.1.le hs.1.le)]
    have hmul : t * s < t := by nlinarith [ht.1, hs.2]
    exact hmul.trans ht.2
  convert (hasSum_geometric_of_abs_lt_one hts).mul_left (t ^ i * s ^ j) using 1
  · rfl
  · ext u
    simp only [pow_add, mul_pow]
    ring
  · rfl

theorem integrableOn_pow_unit (k : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ k) (Set.Ioo (0 : ℝ) 1) := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
  exact (continuous_id.pow k).intervalIntegrable 0 1

theorem integrable_zetaMonomial (i j u : ℕ) :
    Integrable (fun p : ℝ × ℝ => p.1 ^ (i + u) * p.2 ^ (j + u))
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Set.Ioo (0 : ℝ) 1))) :=
  (integrableOn_pow_unit (i + u)).mul_prod (integrableOn_pow_unit (j + u))

theorem integral_zetaMonomial (i j u : ℕ) :
    (∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1,
      t ^ (i + u) * s ^ (j + u)) = zetaTerm i j u := by
  simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
    integral_pow, one_pow, zero_pow (Nat.add_one_ne_zero _),
    sub_zero, zetaTerm, Nat.cast_add, Nat.cast_one]
  simp only [one_div, mul_inv_rev]
  ring

end

section

open MeasureTheory Set
open scoped BigOperators Topology

theorem hasSum_catalanLogKernel {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * (x ^ (2 * n) * (-Real.log x)))
      (-Real.log x / (1 + x ^ 2)) := by
  have hsq : |(-1 : ℝ) * x ^ 2| < 1 := by
    rw [abs_mul, abs_neg, abs_one, one_mul, abs_of_nonneg (sq_nonneg x)]
    nlinarith [hx.1, hx.2]
  convert (hasSum_geometric_of_abs_lt_one hsq).mul_left (-Real.log x) using 1
  · rfl
  · ext n
    rw [mul_pow, ← pow_mul]
    ring
  · simp only [neg_one_mul, sub_neg_eq_add, div_eq_mul_inv]



theorem integral_Ioo_catalanLogKernel :
    (∫ x : ℝ in Ioo (0 : ℝ) 1, -Real.log x / (1 + x ^ 2)) = catalan := by
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  let F : ℕ → ℝ → ℝ := fun n x => (-1 : ℝ) ^ n * (x ^ (2 * n) * (-Real.log x))
  have hF (n : ℕ) : Integrable (F n) μ := by
    exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).mp
        (intervalIntegrable_pow_neg_log (2 * n))).const_mul ((-1 : ℝ) ^ n)
  have hbase (n : ℕ) :
      (∫ x : ℝ, x ^ (2 * n) * (-Real.log x) ∂μ) =
        1 / ((2 * n + 1 : ℕ) : ℝ) ^ 2 := by
    simpa only [μ, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
      integral_Ioc_eq_integral_Ioo] using integral_pow_neg_log (2 * n)
  have hterm (n : ℕ) : (∫ x, F n x ∂μ) =
      (-1 : ℝ) ^ n / ((2 * n + 1 : ℕ) : ℝ) ^ 2 := by
    change (∫ x : ℝ, (-1 : ℝ) ^ n * (x ^ (2 * n) * (-Real.log x)) ∂μ) = _
    rw [integral_const_mul, hbase]
    ring
  have hnorm (n : ℕ) : (∫ x, ‖F n x‖ ∂μ) =
      1 / ((2 * n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [← hbase n]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    dsimp only [F]
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact Real.norm_of_nonneg (mul_nonneg (pow_nonneg hx.1.le _)
      (neg_nonneg.mpr (Real.log_nonpos hx.1.le hx.2.le)))
  have hsum : Summable (fun n => ∫ x, ‖F n x‖ ∂μ) := by
    simpa only [hnorm] using summable_odd_reciprocal_squares
  have hgeom : (fun x => ∑' n, F n x) =ᵐ[μ]
      (fun x : ℝ => -Real.log x / (1 + x ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (hasSum_catalanLogKernel hx).tsum_eq
  calc
    (∫ x : ℝ, -Real.log x / (1 + x ^ 2) ∂μ) =
        ∫ x, (∑' n, F n x) ∂μ := integral_congr_ae hgeom.symm
    _ = ∑' n, ∫ x, F n x ∂μ :=
      (integral_tsum_of_summable_integral_norm hF hsum).symm
    _ = catalan := by simp only [hterm, catalan]

theorem integral_catalanLogKernel :
    (∫ x in (0 : ℝ)..1, -Real.log x / (1 + x ^ 2)) = catalan := by
  simpa only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo] using integral_Ioo_catalanLogKernel

theorem hasSum_reciprocal_squares_zetaSeries :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2) (zetaSeries 0 0) := by
  have hbase := hasSum_zetaSeries 0 0
  change HasSum (fun n : ℕ =>
    1 / (((0 + n + 1 : ℕ) : ℝ) * ((0 + n + 1 : ℕ) : ℝ)))
      (zetaSeries 0 0) at hbase
  have htail : HasSum (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2)
      (zetaSeries 0 0) := by
    simpa only [Nat.zero_add, pow_two] using hbase
  have h := HasSum.zero_add (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) htail
  simpa only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), div_zero, zero_add]
    using h

theorem hasSum_even_reciprocal_squares :
    HasSum (fun n : ℕ => 1 / ((2 * n : ℕ) : ℝ) ^ 2)
      ((1 / 4 : ℝ) * zetaSeries 0 0) := by
  convert hasSum_reciprocal_squares_zetaSeries.mul_left (1 / 4 : ℝ) using 1
  rfl
  ext n
  simp only [Nat.cast_mul, Nat.cast_ofNat, mul_pow, one_div, mul_inv_rev]
  norm_num
  ring

theorem tsum_odd_reciprocal_squares :
    (∑' n : ℕ, 1 / ((2 * n + 1 : ℕ) : ℝ) ^ 2) =
      (3 / 4 : ℝ) * zetaSeries 0 0 := by
  have h := hasSum_reciprocal_squares_zetaSeries.unique
    (HasSum.even_add_odd (f := fun n : ℕ => 1 / (n : ℝ) ^ 2)
      hasSum_even_reciprocal_squares summable_odd_reciprocal_squares.hasSum)
  linarith

theorem hasSum_oddLogKernel {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ => x ^ (2 * n) * (-Real.log x))
      (-Real.log x / (1 - x ^ 2)) := by
  have hsq : |x ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg x)]
    nlinarith [hx.1, hx.2]
  convert (hasSum_geometric_of_abs_lt_one hsq).mul_left (-Real.log x) using 1
  · rfl
  · ext n
    rw [← pow_mul]
    ring
  · rfl

theorem integral_Ioo_oddLogKernel :
    (∫ x : ℝ in Ioo (0 : ℝ) 1, -Real.log x / (1 - x ^ 2)) =
      (3 / 4 : ℝ) * zetaSeries 0 0 := by
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  let F : ℕ → ℝ → ℝ := fun n x => x ^ (2 * n) * (-Real.log x)
  have hF (n : ℕ) : Integrable (F n) μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).mp (intervalIntegrable_pow_neg_log (2 * n))
  have hterm (n : ℕ) : (∫ x, F n x ∂μ) =
      1 / ((2 * n + 1 : ℕ) : ℝ) ^ 2 := by
    simpa only [μ, F, intervalIntegral.integral_of_le
      (show (0 : ℝ) ≤ 1 by norm_num), integral_Ioc_eq_integral_Ioo]
      using integral_pow_neg_log (2 * n)
  have hnorm (n : ℕ) : (∫ x, ‖F n x‖ ∂μ) =
      1 / ((2 * n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [← hterm n]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact Real.norm_of_nonneg (mul_nonneg (pow_nonneg hx.1.le _)
      (neg_nonneg.mpr (Real.log_nonpos hx.1.le hx.2.le)))
  have hsum : Summable (fun n => ∫ x, ‖F n x‖ ∂μ) := by
    simpa only [hnorm] using summable_odd_reciprocal_squares
  have hgeom : (fun x => ∑' n, F n x) =ᵐ[μ]
      (fun x : ℝ => -Real.log x / (1 - x ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (hasSum_oddLogKernel hx).tsum_eq
  calc
    (∫ x : ℝ, -Real.log x / (1 - x ^ 2) ∂μ) =
        ∫ x, (∑' n, F n x) ∂μ := integral_congr_ae hgeom.symm
    _ = ∑' n, ∫ x, F n x ∂μ :=
      (integral_tsum_of_summable_integral_norm hF hsum).symm
    _ = (3 / 4 : ℝ) * zetaSeries 0 0 := by
      simpa only [hterm] using tsum_odd_reciprocal_squares

theorem integral_two_oddLogKernel :
    (∫ x in (0 : ℝ)..1, -2 * Real.log x / (1 - x ^ 2)) =
      (3 / 2 : ℝ) * zetaSeries 0 0 := by
  have h : (∫ x in (0 : ℝ)..1, -Real.log x / (1 - x ^ 2)) =
      (3 / 4 : ℝ) * zetaSeries 0 0 := by
    simpa only [intervalIntegral.integral_of_le
      (show (0 : ℝ) ≤ 1 by norm_num), integral_Ioc_eq_integral_Ioo]
      using integral_Ioo_oddLogKernel
  calc
    _ = 2 * ∫ x in (0 : ℝ)..1, -Real.log x / (1 - x ^ 2) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _
      ring
    _ = _ := by rw [h]; ring

end

open MeasureTheory Set Polynomial
open scoped BigOperators Topology

private theorem ae_mem_unit_square :
    ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1)),
      p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
  apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioo.prod measurableSet_Ioo)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact ⟨ht, hs⟩

theorem integral_prod_zetaKernel (i j : ℕ) :
    (∫ p : ℝ × ℝ, p.1 ^ i * p.2 ^ j / (1 - p.1 * p.2)
      ∂(volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) = zetaSeries i j := by
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  let F : ℕ → ℝ × ℝ → ℝ := fun u p => p.1 ^ (i + u) * p.2 ^ (j + u)
  have hF : ∀ u, Integrable (F u) (μ.prod μ) := fun u =>
    integrable_zetaMonomial i j u
  have hterm (u : ℕ) : (∫ p, F u p ∂μ.prod μ) = zetaTerm i j u := by
    rw [integral_prod _ (hF u)]
    simpa only [μ, F, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
      integral_Ioc_eq_integral_Ioo] using integral_zetaMonomial i j u
  have hnorm (u : ℕ) : (∫ p, ‖F u p‖ ∂μ.prod μ) = zetaTerm i j u := by
    rw [← hterm u]
    apply integral_congr_ae
    filter_upwards [ae_mem_unit_square] with p hp
    exact Real.norm_of_nonneg
      (mul_nonneg (pow_nonneg hp.1.1.le _) (pow_nonneg hp.2.1.le _))
  have hsum : Summable (fun u => ∫ p, ‖F u p‖ ∂μ.prod μ) := by
    simpa only [hnorm] using summable_zetaTerm i j
  have hinterchange := integral_tsum_of_summable_integral_norm hF hsum
  have hgeom : (fun p => ∑' u, F u p) =ᵐ[μ.prod μ]
      (fun p : ℝ × ℝ => p.1 ^ i * p.2 ^ j / (1 - p.1 * p.2)) := by
    filter_upwards [ae_mem_unit_square] with p hp
    exact (hasSum_zetaKernel i j hp.1 hp.2).tsum_eq
  calc
    (∫ p : ℝ × ℝ, p.1 ^ i * p.2 ^ j / (1 - p.1 * p.2) ∂μ.prod μ) =
        ∫ p, (∑' u, F u p) ∂μ.prod μ := integral_congr_ae hgeom.symm
    _ = ∑' u, ∫ p, F u p ∂μ.prod μ := hinterchange.symm
    _ = zetaSeries i j := by simp only [hterm, zetaSeries]

theorem integrable_zetaKernel (i j : ℕ) :
    Integrable (fun p : ℝ × ℝ => p.1 ^ i * p.2 ^ j / (1 - p.1 * p.2))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_prod_zetaKernel]
  have hstep := zetaSeries_step i j
  have htail := zetaSeries_nonneg (i + 1) (j + 1)
  have hzero : 0 < 1 / (((i + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) := by positivity
  have hpos : 0 < zetaSeries i j := by linarith
  exact hpos.ne'



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Arithmetic.FinitePlaceNumerics
namespace OAI


namespace InternalCatalan

open scoped BigOperators



theorem finitePlace_realPlace_threshold_gap :
    -(22909 / 10000 : ℝ) < -(229084 / 100000 : ℝ) := by
  norm_num

end InternalCatalan

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
-- module Solutions.OAICatalan.Catalan.Polynomial.MixedPolynomial
namespace OAI

noncomputable section
open MeasureTheory Set Polynomial
open scoped BigOperators

namespace InternalCatalan

theorem mixedPolynomial_kernel_eq (P Q : ℝ[X]) (t s : ℝ) :
    (|t| / Real.sqrt (1 - t ^ 2)) * (P.eval t * Q.eval s) / (1 - t * s) =
      ∑ i ∈ P.support, ∑ j ∈ Q.support,
        (P.coeff i * Q.coeff j) *
          ((|t| / Real.sqrt (1 - t ^ 2)) * (t ^ i * s ^ j) / (1 - t * s)) := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  simp only [Polynomial.sum_def, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem integrable_mixedPolynomial (P Q : ℝ[X]) :
    Integrable (fun p : ℝ × ℝ => (|p.1| / Real.sqrt (1 - p.1 ^ 2)) *
      (P.eval p.1 * Q.eval p.2) / (1 - p.1 * p.2))
      ((volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  simp_rw [mixedPolynomial_kernel_eq]
  exact integrable_finsetSum P.support fun i _ =>
    integrable_finsetSum Q.support fun j _ =>
      (integrable_mixedKernel i j).const_mul (P.coeff i * Q.coeff j)

theorem integral_prod_mixedPolynomial (P Q : ℝ[X]) :
    (∫ p : ℝ × ℝ, (|p.1| / Real.sqrt (1 - p.1 ^ 2)) *
      (P.eval p.1 * Q.eval p.2) / (1 - p.1 * p.2)
      ∂(volume.restrict (Ioo (-1 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) =
      ∑ i ∈ P.support, ∑ j ∈ Q.support,
        (P.coeff i * Q.coeff j) * mixedMoment (X ^ i) (X ^ j) := by
  simp_rw [mixedPolynomial_kernel_eq]
  rw [integral_finsetSum P.support (fun i _ =>
    integrable_finsetSum Q.support fun j _ =>
      (integrable_mixedKernel i j).const_mul (P.coeff i * Q.coeff j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum Q.support (fun j _ =>
    (integrable_mixedKernel i j).const_mul (P.coeff i * Q.coeff j))]
  simp only [MeasureTheory.integral_const_mul, mixedMoment_X_pow_eq_integral_prod]

theorem mixedMoment_eq_sum (P Q : ℝ[X]) :
    mixedMoment P Q = ∑ i ∈ P.support, ∑ j ∈ Q.support,
      (P.coeff i * Q.coeff j) * mixedMoment (X ^ i) (X ^ j) := by
  have h := integral_prod
    (fun p : ℝ × ℝ => (|p.1| / Real.sqrt (1 - p.1 ^ 2)) *
      (P.eval p.1 * Q.eval p.2) / (1 - p.1 * p.2))
    (integrable_mixedPolynomial P Q)
  rw [integral_prod_mixedPolynomial] at h
  simpa only [mixedMoment,
    intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo] using h.symm

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.ZetaOffDiagonal
namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology

namespace InternalCatalan

theorem zetaTerm_adjacent (i u : ℕ) :
    zetaTerm i (i + 1) u =
      1 / ((i + u + 1 : ℕ) : ℝ) - 1 / ((i + u + 2 : ℕ) : ℝ) := by
  unfold zetaTerm
  rw [show i + 1 + u + 1 = i + u + 2 by omega]
  push_cast
  have ha : (i : ℝ) + (u : ℝ) + 1 ≠ 0 := by positivity
  have hb : (i : ℝ) + (u : ℝ) + 2 ≠ 0 := by positivity
  field_simp [ha, hb]
  ring

theorem sum_zetaTerm_adjacent (i m : ℕ) :
    (∑ u ∈ Finset.range m, zetaTerm i (i + 1) u) =
      1 / ((i + 1 : ℕ) : ℝ) - 1 / ((i + m + 1 : ℕ) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, zetaTerm_adjacent]
    rw [show i + (m + 1) + 1 = i + m + 2 by omega]
    ring

theorem zetaSeries_adjacent (i : ℕ) :
    zetaSeries i (i + 1) = 1 / ((i + 1 : ℕ) : ℝ) := by
  have ht : Tendsto (fun m : ℕ => 1 / ((i + m + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
    have h := (tendsto_add_atTop_iff_nat (i + 1)).2
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  apply tendsto_nhds_unique (tendsto_partial_sums_zetaSeries i (i + 1))
  simp_rw [sum_zetaTerm_adjacent]
  simpa only [sub_zero] using
    (tendsto_const_nhds (x := 1 / ((i + 1 : ℕ) : ℝ))).sub ht

theorem zetaTerm_gap_step (i d u : ℕ) :
    ((d + 1 : ℕ) : ℝ) * zetaTerm i (i + d + 1) u =
      (d : ℝ) * zetaTerm i (i + d) u + zetaTerm (i + d) (i + d + 1) u := by
  unfold zetaTerm
  push_cast
  have ha : (i : ℝ) + (u : ℝ) + 1 ≠ 0 := by positivity
  have hb : (i : ℝ) + (d : ℝ) + (u : ℝ) + 1 ≠ 0 := by positivity
  have hc : (i : ℝ) + (d : ℝ) + 1 + (u : ℝ) + 1 ≠ 0 := by positivity
  field_simp [ha, hb, hc]
  ring

theorem zetaSeries_gap_step (i d : ℕ) :
    ((d + 1 : ℕ) : ℝ) * zetaSeries i (i + d + 1) =
      (d : ℝ) * zetaSeries i (i + d) + 1 / ((i + d + 1 : ℕ) : ℝ) := by
  have hs := ((hasSum_zetaSeries i (i + d)).mul_left (d : ℝ)).add
    (hasSum_zetaSeries (i + d) (i + d + 1))
  calc
    ((d + 1 : ℕ) : ℝ) * zetaSeries i (i + d + 1) =
        ∑' u : ℕ, ((d + 1 : ℕ) : ℝ) * zetaTerm i (i + d + 1) u := by
      exact tsum_mul_left.symm
    _ = ∑' u : ℕ, ((d : ℝ) * zetaTerm i (i + d) u +
        zetaTerm (i + d) (i + d + 1) u) :=
      tsum_congr (zetaTerm_gap_step i d)
    _ = (d : ℝ) * zetaSeries i (i + d) + zetaSeries (i + d) (i + d + 1) :=
      hs.tsum_eq
    _ = _ := by rw [zetaSeries_adjacent]

theorem zetaSeries_mul_gap (i d : ℕ) :
    ((d + 1 : ℕ) : ℝ) * zetaSeries i (i + (d + 1)) =
      (harmonicRat 1 (i + (d + 1)) : ℝ) - (harmonicRat 1 i : ℝ) := by
  induction d with
  | zero =>
    simp only [Nat.zero_add, Nat.cast_one, one_mul]
    rw [zetaSeries_adjacent, harmonicRat_succ]
    push_cast
    simp only [pow_one]
    ring
  | succ d ih =>
    have hH := congrArg (fun q : ℚ => (q : ℝ)) (harmonicRat_succ 1 (i + (d + 1)))
    push_cast at hH
    simp only [pow_one] at hH
    calc
      ((d + 1 + 1 : ℕ) : ℝ) * zetaSeries i (i + (d + 1 + 1)) =
          ((d + 1 : ℕ) : ℝ) * zetaSeries i (i + (d + 1)) +
            1 / ((i + (d + 1) + 1 : ℕ) : ℝ) := by
        simpa only [Nat.add_assoc] using zetaSeries_gap_step i (d + 1)
      _ = (harmonicRat 1 (i + (d + 1 + 1)) : ℝ) - (harmonicRat 1 i : ℝ) := by
        rw [ih, show i + (d + 1 + 1) = i + (d + 1) + 1 by omega, hH]
        push_cast
        ring

theorem zetaSeries_eq_harmonic_div {i j : ℕ} (hij : i < j) :
    zetaSeries i j =
      ((harmonicRat 1 j : ℝ) - (harmonicRat 1 i : ℝ)) / ((j : ℝ) - (i : ℝ)) := by
  let d := j - i - 1
  have he : j = i + (d + 1) := by dsimp [d]; omega
  have hd : (j : ℝ) - (i : ℝ) = ((d + 1 : ℕ) : ℝ) := by
    rw [he]
    push_cast
    ring
  have hd0 : ((d + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [hd]
  apply (eq_div_iff hd0).2
  have h := zetaSeries_mul_gap i d
  rw [← he] at h
  simpa only [mul_comm] using h

theorem zetaSeries_eq_zetaRat_of_lt {i j : ℕ} (hij : i < j) :
    zetaSeries i j = (zetaRat i j : ℝ) := by
  rw [zetaSeries_eq_harmonic_div hij, zetaRat_of_ne (ne_of_lt hij)]
  push_cast
  have hlt : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
  apply (div_eq_div_iff (sub_ne_zero.mpr (ne_of_gt hlt))
    (sub_ne_zero.mpr (ne_of_lt hlt))).2
  ring

theorem zetaSeries_offDiagonal {i j : ℕ} (hij : i ≠ j) :
    zetaSeries i j = (zetaRat i j : ℝ) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact zetaSeries_eq_zetaRat_of_lt hlt
  · rw [zetaSeries_symm i j, zetaRat_symm i j]
    exact zetaSeries_eq_zetaRat_of_lt hgt

theorem zetaSeries_eq_zetaRat_add (i j : ℕ) :
    zetaSeries i j = (zetaRat i j : ℝ) +
      if i = j then zetaSeries 0 0 else 0 := by
  by_cases hij : i = j
  · subst j
    simpa using zetaSeries_diagonal i
  · rw [if_neg hij, add_zero]
    exact zetaSeries_offDiagonal hij

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Polynomial.ZetaPolynomial
namespace OAI

noncomputable section

open MeasureTheory Set Polynomial
open scoped BigOperators

namespace InternalCatalan

theorem zetaPolynomial_kernel_eq (P Q : ℝ[X]) (t s : ℝ) :
    P.eval t * Q.eval s / (1 - t * s) =
      ∑ i ∈ P.support, ∑ j ∈ Q.support,
        (P.coeff i * Q.coeff j) * (t ^ i * s ^ j / (1 - t * s)) := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  simp only [Polynomial.sum_def, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem integrable_zetaPolynomial (P Q : ℝ[X]) :
    Integrable (fun p : ℝ × ℝ => P.eval p.1 * Q.eval p.2 / (1 - p.1 * p.2))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  simp_rw [zetaPolynomial_kernel_eq]
  exact integrable_finsetSum P.support fun i _ =>
    integrable_finsetSum Q.support fun j _ =>
      (integrable_zetaKernel i j).const_mul (P.coeff i * Q.coeff j)

theorem integral_prod_zetaPolynomial (P Q : ℝ[X]) :
    (∫ p : ℝ × ℝ, P.eval p.1 * Q.eval p.2 / (1 - p.1 * p.2)
      ∂(volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) =
      ∑ i ∈ P.support, ∑ j ∈ Q.support,
        (P.coeff i * Q.coeff j) * zetaSeries i j := by
  simp_rw [zetaPolynomial_kernel_eq]
  rw [integral_finsetSum P.support (fun i _ =>
    integrable_finsetSum Q.support fun j _ =>
      (integrable_zetaKernel i j).const_mul (P.coeff i * Q.coeff j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum Q.support (fun j _ =>
    (integrable_zetaKernel i j).const_mul (P.coeff i * Q.coeff j))]
  simp only [MeasureTheory.integral_const_mul, integral_prod_zetaKernel]

theorem zetaMoment_eq_sum (P Q : ℝ[X]) :
    zetaMoment P Q = ∑ i ∈ P.support, ∑ j ∈ Q.support,
      (P.coeff i * Q.coeff j) * zetaSeries i j := by
  have h := integral_prod
    (fun p : ℝ × ℝ => P.eval p.1 * Q.eval p.2 / (1 - p.1 * p.2))
    (integrable_zetaPolynomial P Q)
  rw [integral_prod_zetaPolynomial] at h
  simpa only [zetaMoment,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo] using h.symm



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.RowMomentExpansion
namespace OAI


noncomputable section

open Polynomial
open scoped BigOperators

namespace InternalCatalan

@[simp] theorem realPoly_coeff (F : ℤ[X]) (i : ℕ) :
    (realPoly F).coeff i = (F.coeff i : ℝ) := by
  rw [realPoly, Polynomial.coeff_map]
  rfl

theorem realPoly_support_subset_range (F : ℤ[X]) (D : ℕ)
    (hF : ∀ i, D ≤ i → F.coeff i = 0) :
    (realPoly F).support ⊆ Finset.range D := by
  intro i hi
  apply Finset.mem_range.mpr
  by_contra h
  have hzero : (realPoly F).coeff i = 0 := by
    rw [realPoly_coeff, hF i (by omega)]
    exact Int.cast_zero
  exact (Polynomial.mem_support_iff.mp hi) hzero

theorem mixedMoment_realPoly_X_pow_eq_sum_range (F : ℤ[X]) (D j : ℕ)
    (hF : ∀ i, D ≤ i → F.coeff i = 0) :
    mixedMoment (realPoly F) (X ^ j) =
      ∑ i ∈ Finset.range D,
        (F.coeff i : ℝ) * mixedMoment (X ^ i) (X ^ j) := by
  rw [mixedMoment_eq_sum]
  simp only [Polynomial.support_X_pow, Finset.sum_singleton,
    Polynomial.coeff_X_pow_self, mul_one]
  simpa only [Polynomial.sum_def, realPoly_coeff] using
    (Polynomial.sum_eq_of_subset (p := realPoly F)
      (fun i a => a * mixedMoment (X ^ i) (X ^ j))
      (fun _ => zero_mul _) (realPoly_support_subset_range F D hF))

theorem zetaMoment_realPoly_X_pow_eq_sum_range (F : ℤ[X]) (D j : ℕ)
    (hF : ∀ i, D ≤ i → F.coeff i = 0) :
    zetaMoment (realPoly F) (X ^ j) =
      ∑ i ∈ Finset.range D, (F.coeff i : ℝ) * zetaSeries i j := by
  rw [zetaMoment_eq_sum]
  simp only [Polynomial.support_X_pow, Finset.sum_singleton,
    Polynomial.coeff_X_pow_self, mul_one]
  simpa only [Polynomial.sum_def, realPoly_coeff] using
    (Polynomial.sum_eq_of_subset (p := realPoly F)
      (fun i a => a * zetaSeries i j)
      (fun _ => zero_mul _) (realPoly_support_subset_range F D hF))

theorem mixedMoment_rowP_X_pow_eq_sum_range {N : ℕ} (hN : 0 < N) (r j : ℕ) :
    mixedMoment (realPoly (rowP N r)) (X ^ j) =
      ∑ i ∈ Finset.range (H N),
        ((rowP N r).coeff i : ℝ) * mixedMoment (X ^ i) (X ^ j) := by
  exact mixedMoment_realPoly_X_pow_eq_sum_range (rowP N r) (H N) j
    (fun _ hi => rowP_coeff_eq_zero_of_ge hN hi)

theorem zetaMoment_rowD_X_pow_eq_sum_range {N : ℕ} (hN : 0 < N) (r j : ℕ) :
    zetaMoment (realPoly (rowD N r)) (X ^ j) =
      ∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℝ) * zetaSeries i j := by
  exact zetaMoment_realPoly_X_pow_eq_sum_range (rowD N r) (H N) j
    (fun _ hi => rowD_coeff_eq_zero_of_ge hN hi)

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.ChebyshevContact
namespace OAI


noncomputable section

open Polynomial

namespace InternalCatalan

def centralCoefficientMap (m : ℤ) (k : ℕ) : ℚ →ₗ[ℚ] ℚ where
  toFun a := a * centralCoeffKernel ((k : ℤ) - m)
  map_add' a b := by ring
  map_smul' a b := by simp only [smul_eq_mul, RingHom.id_apply]; ring

def centralFunctional (m : ℤ) : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum (centralCoefficientMap m)

@[simp] theorem centralFunctional_monomial (m : ℤ) (k : ℕ) (a : ℚ) :
    centralFunctional m (monomial k a) = a * centralCoeffKernel ((k : ℤ) - m) := by
  simp [centralFunctional, Polynomial.lsum_apply, Polynomial.sum_monomial_index,
    centralCoefficientMap]

theorem centralFunctional_C_mul (m : ℤ) (a : ℚ) (P : ℚ[X]) :
    centralFunctional m (Polynomial.C a * P) = a * centralFunctional m P := by
  rw [← smul_eq_C_mul, (centralFunctional m).map_smul]
  rfl

theorem centralFunctional_X_mul (m : ℤ) (P : ℚ[X]) :
    centralFunctional m (X * P) = centralFunctional (m - 1) P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [mul_add, map_add, hP, hQ]
  | monomial k a =>
      rw [X_mul_monomial, centralFunctional_monomial, centralFunctional_monomial]
      congr 2
      push_cast
      omega

theorem centralFunctional_stein (P : ℚ[X]) :
    centralFunctional 0 ((1 - X ^ 2) * derivative P) =
      centralFunctional 0 (X * P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [mul_add, map_add, hP, hQ]
  | monomial k a =>
      cases k with
      | zero =>
          rw [X_mul_monomial]
          simp [centralCoeffKernel]
      | succ k =>
          rw [derivative_monomial_succ, sub_mul, one_mul, X_pow_mul_monomial,
            X_mul_monomial, map_sub]
          simp only [centralFunctional_monomial, sub_zero]
          have hs := centralCoeffKernel_nat_step k
          have hscaled := congrArg (fun z : ℚ => a * z) hs
          push_cast at hscaled ⊢
          norm_num only [add_assoc, Int.reduceAdd] at hscaled ⊢
          nlinarith only [hscaled]

theorem centralFunctional_T_zero (d : ℕ) (hd : 0 < d) :
    centralFunctional 0 (Chebyshev.T ℚ (d : ℤ)) = 0 := by
  have hode := congrArg (centralFunctional 0)
    (Chebyshev.one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T (R := ℚ) (d : ℤ))
  have hstein := centralFunctional_stein (derivative (Chebyshev.T ℚ (d : ℤ)))
  have hcast : ((d : ℤ) ^ 2 : ℚ[X]) = Polynomial.C ((d : ℚ) ^ 2) := by
    simp
  simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq] at hode
  rw [map_sub, hcast, centralFunctional_C_mul] at hode
  have hz : (d : ℚ) ^ 2 * centralFunctional 0 (Chebyshev.T ℚ (d : ℤ)) = 0 := by
    linarith only [hode, hstein]
  have hdn : (d : ℚ) ^ 2 ≠ 0 := by positivity
  exact (mul_eq_zero.mp hz).resolve_left hdn

theorem centralFunctional_two_X_mul (m : ℤ) (P : ℚ[X]) :
    centralFunctional m (2 * X * P) = 2 * centralFunctional (m - 1) P := by
  rw [← Polynomial.C_ofNat, mul_assoc,
    centralFunctional_C_mul, centralFunctional_X_mul]

theorem centralFunctional_T_tail (d : ℕ) : ∀ m : ℕ,
    centralFunctional ((m : ℤ) + 1) (Chebyshev.T ℚ (d : ℤ)) =
      (Chebyshev.U ℚ ((d : ℤ) - 1)).coeff m := by
  induction d using Nat.twoStepInduction with
  | zero =>
      intro m
      rw [Nat.cast_zero, Chebyshev.T_zero, zero_sub, Chebyshev.U_neg_one,
        coeff_zero, ← monomial_zero_one, centralFunctional_monomial,
        centralCoeffKernel_of_neg (by omega : ((0 : ℕ) : ℤ) - ((m : ℤ) + 1) < 0)]
      ring
  | one =>
      intro m
      rw [Nat.cast_one, Chebyshev.T_one, sub_self, Chebyshev.U_zero,
        ← monomial_one_one_eq_X, centralFunctional_monomial]
      cases m with
      | zero => norm_num
      | succ m =>
          rw [centralCoeffKernel_of_neg (by omega :
            ((1 : ℕ) : ℤ) - (((m + 1 : ℕ) : ℤ) + 1) < 0)]
          simp [Polynomial.coeff_one]
  | more d ih0 ih1 =>
      intro m
      have hindex : ((d + 2 : ℕ) : ℤ) - 1 = (d : ℤ) + 1 := by omega
      rw [hindex, Nat.cast_add, Nat.cast_ofNat, Chebyshev.T_add_two,
        map_sub, centralFunctional_two_X_mul, Chebyshev.U_add_one]
      rw [coeff_sub, mul_assoc, coeff_ofNat_mul]
      cases m with
      | zero =>
          norm_num only [Nat.cast_zero, zero_add, sub_self]
          have hvan := centralFunctional_T_zero (d + 1) (by omega)
          simp only [Nat.cast_add, Nat.cast_one] at hvan
          have hprev := ih0 0
          simp only [Nat.cast_zero, zero_add] at hprev
          rw [hvan, hprev, coeff_X_mul_zero]
      | succ m =>
          have hmain := ih1 m
          simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hmain
          have hprev := ih0 (m + 1)
          simp only [Nat.cast_add, Nat.cast_one] at hprev
          simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
          rw [hmain, hprev, coeff_X_mul]

end InternalCatalan

end



noncomputable section

open Polynomial

namespace InternalCatalan

private theorem rationalIntCast_apply (z : ℤ) :
    (Int.castRingHom ℚ) z = (z : ℚ) := rfl

theorem centralFunctional_eq_sum_range (m : ℤ) {P : ℚ[X]} {C : ℕ}
    (hP : P.natDegree < C) :
    centralFunctional m P = ∑ u ∈ Finset.range C,
      P.coeff u * centralCoeffKernel ((u : ℤ) - m) := by
  change P.sum (fun u a => a * centralCoeffKernel ((u : ℤ) - m)) = _
  apply Polynomial.sum_eq_of_subset
  · intro u
    simp
  · intro u hu
    apply Finset.mem_range.mpr
    exact lt_of_le_of_lt (Polynomial.le_natDegree_of_ne_zero
      (Polynomial.mem_support_iff.mp hu)) hP

theorem reversedRow_centralFunctional {C j : ℕ} (hj : j < C) (F : ℤ[X])
    (hF : F.natDegree < C) :
    (∑ i ∈ Finset.range C,
      ((reversedRow C F).coeff i : ℚ) * centralCoeffKernel ((j : ℤ) - i - 1)) =
      centralFunctional ((C : ℤ) - j) (F.map (Int.castRingHom ℚ)) := by
  have hC : 0 < C := (Nat.zero_le j).trans_lt hj
  have hmap : (F.map (Int.castRingHom ℚ)).natDegree < C :=
    lt_of_le_of_lt Polynomial.natDegree_map_le hF
  rw [centralFunctional_eq_sum_range _ hmap]
  simp only [Polynomial.coeff_map, rationalIntCast_apply]
  calc
    _ = ∑ i ∈ Finset.range C, (F.coeff (C - 1 - i) : ℚ) *
        centralCoeffKernel ((((C - 1 - i : ℕ) : ℤ)) - ((C : ℤ) - j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [reversedRow_coeff, if_pos hi']
      congr 2
      omega
    _ = _ := Finset.sum_range_reflect
      (fun u => (F.coeff u : ℚ) * centralCoeffKernel ((u : ℤ) - ((C : ℤ) - j))) C

theorem reversedChebyshev_contact {C d j : ℕ} (hd : d < C) (hj : j < C) :
    (∑ i ∈ Finset.range C,
      ((reversedRow C (Chebyshev.T ℤ (d : ℤ))).coeff i : ℚ) *
        centralCoeffKernel ((j : ℤ) - i - 1)) =
      ((reversedRow C (Chebyshev.U ℤ ((d : ℤ) - 1))).coeff j : ℚ) := by
  rw [reversedRow_centralFunctional hj _ (by simpa using hd), Chebyshev.map_T]
  have hindex : (C : ℤ) - j = ((C - 1 - j : ℕ) : ℤ) + 1 := by omega
  rw [hindex, centralFunctional_T_tail, reversedRow_coeff, if_pos hj]
  have hmap := congrArg (fun P : ℚ[X] => P.coeff (C - 1 - j))
    (Chebyshev.map_U (Int.castRingHom ℚ) ((d : ℤ) - 1))
  simpa only [Polynomial.coeff_map, rationalIntCast_apply] using hmap.symm

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.MomentFilter
namespace OAI

section

open scoped BigOperators Polynomial

noncomputable section

namespace InternalCatalan

open Polynomial

def filteredColumnInt (N k : ℕ) : ℤ[X] :=
  X ^ (b N + k) * (1 - X) ^ q N


theorem one_sub_X_pow_expansion (Q : ℕ) :
    ((1 : ℤ[X]) - X) ^ Q =
      ∑ v ∈ Finset.range (Q + 1),
        C ((-1 : ℤ) ^ v * (Nat.choose Q v : ℤ)) * X ^ v := by
  calc
    ((1 : ℤ[X]) - X) ^ Q = (-X + 1) ^ Q := by
      congr 1
      ring
    _ = ∑ v ∈ Finset.range (Q + 1),
        (-X : ℤ[X]) ^ v * 1 ^ (Q - v) * (Nat.choose Q v : ℤ[X]) :=
      add_pow (-X : ℤ[X]) 1 Q
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [neg_pow]
      simp only [one_pow, mul_one, map_mul, map_pow, map_neg,
        map_one, C_eq_natCast]
      ring


theorem filteredColumnInt_expansion (N k : ℕ) :
    filteredColumnInt N k =
      ∑ v ∈ Finset.range (q N + 1),
        C ((-1 : ℤ) ^ v * (Nat.choose (q N) v : ℤ)) *
          X ^ (b N + k + v) := by
  rw [filteredColumnInt, one_sub_X_pow_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [pow_add]
  ring








variable {V : Type*} [AddCommGroup V]




end InternalCatalan

end

end


noncomputable section

open Polynomial
open scoped BigOperators

namespace InternalCatalan

theorem realPoly_filteredColumnInt (N k : ℕ) :
    realPoly (filteredColumnInt N k) = filteredColumn N k := by
  simp [realPoly, filteredColumnInt, filteredColumn]

theorem filteredColumn_expansion (N k : ℕ) :
    filteredColumn N k =
      ∑ v ∈ Finset.range (q N + 1),
        Polynomial.C (filterCoeffRat N v : ℝ) *
          Polynomial.X ^ (b N + k + v) := by
  rw [← realPoly_filteredColumnInt, filteredColumnInt_expansion]
  simp [realPoly, Polynomial.map_sum, filterCoeffRat]

def coefficientPairingRight (K : ℕ → ℕ → ℝ) (P : ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum fun j =>
    { toFun := fun a => ∑ i ∈ P.support, (P.coeff i * a) * K i j
      map_add' := by
        intro a b
        simp only [mul_add, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        change (∑ i ∈ P.support, (P.coeff i * (c * a)) * K i j) =
          c * ∑ i ∈ P.support, (P.coeff i * a) * K i j
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring }

theorem coefficientPairingRight_apply (K : ℕ → ℕ → ℝ) (P Q : ℝ[X]) :
    coefficientPairingRight K P Q =
      ∑ i ∈ P.support, ∑ j ∈ Q.support,
        (P.coeff i * Q.coeff j) * K i j := by
  change (∑ j ∈ Q.support, ∑ i ∈ P.support,
    (P.coeff i * Q.coeff j) * K i j) = _
  exact Finset.sum_comm

def mixedMomentRightLinear (P : ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ :=
  coefficientPairingRight
    (fun i j => mixedMoment (Polynomial.X ^ i) (Polynomial.X ^ j)) P

theorem mixedMomentRightLinear_apply (P Q : ℝ[X]) :
    mixedMomentRightLinear P Q = mixedMoment P Q := by
  rw [mixedMomentRightLinear, coefficientPairingRight_apply, mixedMoment_eq_sum]

def zetaMomentRightLinear (P : ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ :=
  coefficientPairingRight zetaSeries P

theorem zetaMomentRightLinear_apply (P Q : ℝ[X]) :
    zetaMomentRightLinear P Q = zetaMoment P Q := by
  rw [zetaMomentRightLinear, coefficientPairingRight_apply, zetaMoment_eq_sum]

theorem map_filteredColumn (F : ℝ[X] →ₗ[ℝ] ℝ) (N k : ℕ) :
    F (filteredColumn N k) =
      ∑ v ∈ Finset.range (q N + 1),
        (filterCoeffRat N v : ℝ) * F (Polynomial.X ^ (b N + k + v)) := by
  rw [filteredColumn_expansion, map_sum]
  apply Finset.sum_congr rfl
  intro v hv
  simpa only [Polynomial.smul_eq_C_mul, smul_eq_mul] using
    F.map_smul (filterCoeffRat N v : ℝ) (Polynomial.X ^ (b N + k + v))

theorem mixedMoment_filteredColumn (P : ℝ[X]) (N k : ℕ) :
    mixedMoment P (filteredColumn N k) =
      ∑ v ∈ Finset.range (q N + 1),
        (filterCoeffRat N v : ℝ) *
          mixedMoment P (Polynomial.X ^ (b N + k + v)) := by
  rw [← mixedMomentRightLinear_apply P (filteredColumn N k), map_filteredColumn]
  apply Finset.sum_congr rfl
  intro v hv
  rw [mixedMomentRightLinear_apply]

theorem zetaMoment_filteredColumn (P : ℝ[X]) (N k : ℕ) :
    zetaMoment P (filteredColumn N k) =
      ∑ v ∈ Finset.range (q N + 1),
        (filterCoeffRat N v : ℝ) *
          zetaMoment P (Polynomial.X ^ (b N + k + v)) := by
  rw [← zetaMomentRightLinear_apply P (filteredColumn N k), map_filteredColumn]
  apply Finset.sum_congr rfl
  intro v hv
  rw [zetaMomentRightLinear_apply]

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Determinants.TwoAdicSmoothedMinor
namespace OAI


noncomputable section

open Polynomial
open scoped BigOperators

namespace InternalCatalan











end InternalCatalan

end



noncomputable section

open Polynomial

namespace InternalCatalan

def intPolynomialSeries (P : ℤ[X]) : PowerSeries ℚ :=
  (P.map (Int.castRingHom ℚ) : ℚ[X])

@[simp] theorem coeff_intPolynomialSeries (P : ℤ[X]) (j : ℕ) :
    PowerSeries.coeff j (intPolynomialSeries P) = (P.coeff j : ℚ) := by
  simp [intPolynomialSeries]

@[simp] theorem intPolynomialSeries_mul (P Q : ℤ[X]) :
    intPolynomialSeries (P * Q) = intPolynomialSeries P * intPolynomialSeries Q := by
  simp [intPolynomialSeries]

def contactSeries (P : ℤ[X]) : PowerSeries ℚ :=
  intPolynomialSeries P * (PowerSeries.X * centralKernelSeries)

theorem coeff_X_centralKernelSeries (j : ℕ) :
    PowerSeries.coeff j (PowerSeries.X * centralKernelSeries) =
      centralCoeffKernel ((j : ℤ) - 1) := by
  cases j with
  | zero =>
      rw [PowerSeries.coeff_zero_X_mul, Nat.cast_zero,
        centralCoeffKernel_of_neg (by norm_num : (0 : ℤ) - 1 < 0)]
  | succ j =>
      rw [PowerSeries.coeff_succ_X_mul, coeff_centralKernelSeries]
      congr 1
      omega

theorem contactSeries_coeff_eq_sum (P : ℤ[X]) {B j : ℕ} (hj : j < B) :
    PowerSeries.coeff j (contactSeries P) =
      ∑ i ∈ Finset.range B,
        (P.coeff i : ℚ) * centralCoeffKernel ((j : ℤ) - i - 1) := by
  unfold contactSeries
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i k => PowerSeries.coeff i (intPolynomialSeries P) *
        PowerSeries.coeff k (PowerSeries.X * centralKernelSeries)) j]
  calc
    _ = ∑ i ∈ Finset.range (j + 1),
        (P.coeff i : ℚ) * centralCoeffKernel ((j : ℤ) - i - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [coeff_intPolynomialSeries, coeff_X_centralKernelSeries]
      congr 2
      have hi' := Finset.mem_range.mp hi
      omega
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono (by omega : j + 1 ≤ B))
      intro i hi hin
      have hin' : ¬ i < j + 1 := by simpa only [Finset.mem_range] using hin
      rw [centralCoeffKernel_of_neg (by omega : (j : ℤ) - i - 1 < 0), mul_zero]

theorem series_coeff_mul_congr_below {S T : PowerSeries ℚ} {B : ℕ}
    (hST : ∀ j < B, PowerSeries.coeff j S = PowerSeries.coeff j T)
    (Q : PowerSeries ℚ) {j : ℕ} (hj : j < B) :
    PowerSeries.coeff j (Q * S) = PowerSeries.coeff j (Q * T) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨u, v⟩ huv
  have huv' : u + v = j := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
  rw [hST v (by omega)]

theorem contactSeries_mul (P Q : ℤ[X]) :
    contactSeries (P * Q) = intPolynomialSeries P * contactSeries Q := by
  simp only [contactSeries, intPolynomialSeries_mul, mul_assoc]

theorem reversedChebyshev_contact_series {C d j : ℕ}
    (hd : d < C) (hj : j < C) :
    PowerSeries.coeff j
        (contactSeries (reversedRow C (Chebyshev.T ℤ (d : ℤ)))) =
      PowerSeries.coeff j
        (intPolynomialSeries (reversedRow C (Chebyshev.U ℤ ((d : ℤ) - 1)))) := by
  rw [contactSeries_coeff_eq_sum _ hj, coeff_intPolynomialSeries]
  exact reversedChebyshev_contact hd hj

theorem row_contact_of_gt_g {N r j : ℕ} (hN : 0 < N)
    (hr : r < n N) (hrg : g N < r) (hj : j < L N) :
    (∑ i ∈ Finset.range (H N),
      ((rowP N r).coeff i : ℚ) * centralCoeffKernel ((j : ℤ) - i - 1)) =
      ((rowD N r).coeff j : ℚ) := by
  have hjC : j < Cdegree N := by
    rw [Cdegree_eq_L_add_g]
    omega
  have hjH : j < H N := by
    rw [H_eq_Cdegree_add_h]
    omega
  have hd : rowDistance N r < Cdegree N := rowDistance_lt_Cdegree hN hr
  have hs : Int.sign (rowOffset N r) = 1 := by
    apply Int.sign_eq_one_of_pos
    unfold rowOffset
    omega
  have hbase : ∀ l < Cdegree N,
      PowerSeries.coeff l
          (contactSeries
            (reversedRow (Cdegree N) (Chebyshev.T ℤ (rowDistance N r : ℤ)))) =
        PowerSeries.coeff l
          (intPolynomialSeries
            (reversedRow (Cdegree N)
              (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1)))) := by
    intro l hl
    exact reversedChebyshev_contact_series hd hl
  have hmul := series_coeff_mul_congr_below hbase
    (intPolynomialSeries ((1 - X : ℤ[X]) ^ h N)) hjC
  rw [← contactSeries_mul, ← intPolynomialSeries_mul] at hmul
  rw [contactSeries_coeff_eq_sum _ hjH, coeff_intPolynomialSeries] at hmul
  simpa only [rowP, rowD, hs, Polynomial.C_1, one_mul] using hmul

theorem row_contact {N r j : ℕ} (hN : 0 < N)
    (hr : r < n N) (hj : j < L N) :
    (∑ i ∈ Finset.range (H N),
      ((rowP N r).coeff i : ℚ) * centralCoeffKernel ((j : ℤ) - i - 1)) =
      ((rowD N r).coeff j : ℚ) := by
  rcases le_or_gt r (g N) with hrg | hrg
  · exact row_contact_of_le_g hN hr hrg hj
  · exact row_contact_of_gt_g hN hr hrg hj

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators





end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators






end InternalCatalan

end



noncomputable section

namespace InternalCatalan










open scoped BigOperators



end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.MixedOneStart
namespace OAI

noncomputable section

namespace InternalCatalan

open MeasureTheory Set Real

private theorem hasDerivAt_sqrt_one_sub_sq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x : ℝ => sqrt (1 - x ^ 2))
      (-x / sqrt (1 - x ^ 2)) x := by
  have hp : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  convert ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_pow 2 x)).sqrt hp.ne' using 1
  all_goals first
    | rfl
    | (norm_num [Pi.sub_apply]
       try ring)

private theorem mixedOne_complement_cancel {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (-log (1 - sqrt (1 - x ^ 2) ^ 2) /
        (sqrt (1 - x ^ 2) * sqrt (1 - sqrt (1 - x ^ 2) ^ 2))) *
      (-x / sqrt (1 - x ^ 2)) = 2 * log x / (1 - x ^ 2) := by
  have hp : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hsq : sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 := sq_sqrt hp.le
  have hc : 1 - sqrt (1 - x ^ 2) ^ 2 = x ^ 2 := by rw [hsq]; ring
  rw [hc, sqrt_sq hx.1.le, log_pow]
  norm_num only [Nat.cast_ofNat]
  have hs : sqrt (1 - x ^ 2) ≠ 0 := (sqrt_pos.mpr hp).ne'
  calc
    _ = 2 * log x / sqrt (1 - x ^ 2) ^ 2 := by
      field_simp [hx.1.ne', hs]
    _ = _ := by rw [hsq]

theorem integral_mixedOne_logKernel :
    (∫ t in (0 : ℝ)..1, -log (1 - t ^ 2) / (t * sqrt (1 - t ^ 2))) =
      (3 / 2 : ℝ) * zetaSeries 0 0 := by
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (a := (0 : ℝ)) (b := 1)
    (f := fun x : ℝ => sqrt (1 - x ^ 2))
    (f' := fun x : ℝ => -x / sqrt (1 - x ^ 2))
    (g := fun t : ℝ => -log (1 - t ^ 2) / (t * sqrt (1 - t ^ 2)))
    (show Continuous (fun x : ℝ => sqrt (1 - x ^ 2)) by fun_prop).continuousOn
    (by
      intro x hx
      simp only [min_eq_left (show (0 : ℝ) ≤ 1 by norm_num),
        max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)] at hx
      exact hasDerivAt_sqrt_one_sub_sq hx)
    (by
      intro x hx
      simp only [min_eq_left (show (0 : ℝ) ≤ 1 by norm_num),
        max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)] at hx
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx.1.le) (sqrt_nonneg _))
  have hleft :
      (∫ x in (0 : ℝ)..1,
        ((fun t : ℝ => -log (1 - t ^ 2) / (t * sqrt (1 - t ^ 2))) ∘
          (fun x : ℝ => sqrt (1 - x ^ 2))) x *
          (-x / sqrt (1 - x ^ 2))) =
        -(3 / 2 : ℝ) * zetaSeries 0 0 := by
    calc
      _ = ∫ x in (0 : ℝ)..1, -( -2 * log x / (1 - x ^ 2)) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro x hx
        dsimp only [Function.comp_apply]
        rw [mixedOne_complement_cancel hx]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_neg, integral_two_oddLogKernel]
        ring
  simp only [zero_pow (by decide : 2 ≠ 0), sub_zero, sqrt_one, one_pow,
    sub_self, sqrt_zero] at hsub
  rw [hleft, intervalIntegral.integral_symm] at hsub
  linarith

open MeasureTheory Set Real Polynomial
open scoped Interval

theorem mixed_affine_denominator_pos {t s : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) : 0 < 1 - t * s := by
  by_cases ht0 : 0 ≤ t
  · have hts : t * s ≤ t := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hs.2)]
    linarith [ht.2]
  · have hts : t * s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ht0) hs.1
    linarith

theorem integral_reciprocal_affine {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1)
    (ht0 : t ≠ 0) :
    (∫ s in (0 : ℝ)..1, 1 / (1 - t * s)) = -log (1 - t) / t := by
  have hint : IntervalIntegrable (fun s : ℝ => 1 / (1 - t * s)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact continuousOn_const.div
      (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
      (fun s hs => (mixed_affine_denominator_pos ht hs).ne')
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (f := fun s : ℝ => -log (1 - t * s) / t)
    (f' := fun s : ℝ => 1 / (1 - t * s)) (fun s hs => by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      have hd : 1 - t * s ≠ 0 := (mixed_affine_denominator_pos ht hs).ne'
      have hderiv := ((((hasDerivAt_id s).const_mul t).const_sub 1).log hd).neg.div_const t
      convert hderiv using 1
      all_goals first
        | rfl
        | (dsimp; field_simp)
        | field_simp) hint
  simpa only [mul_one, mul_zero, sub_zero, log_one, neg_zero, zero_div] using h

theorem intervalIntegrable_mixedMoment_outer (i j : ℕ) :
    IntervalIntegrable (fun t : ℝ => ∫ s in (0 : ℝ)..1,
      (|t| / sqrt (1 - t ^ 2)) * (t ^ i * s ^ j) / (1 - t * s)) volume (-1) 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (by norm_num : (-1 : ℝ) ≤ 1)).mpr
  change Integrable (fun t : ℝ => ∫ s in (0 : ℝ)..1,
    (|t| / sqrt (1 - t ^ 2)) * (t ^ i * s ^ j) / (1 - t * s))
      (volume.restrict (Ioo (-1 : ℝ) 1))
  simp only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo]
  exact (integrable_mixedKernel i j).integral_prod_left

theorem integral_mixedZeroLogKernel :
    (∫ t in (0 : ℝ)..1, log ((1 + t) / (1 - t)) / sqrt (1 - t ^ 2)) =
      4 * catalan := by
  let f : ℝ → ℝ := fun x => (1 - x ^ 2) / (1 + x ^ 2)
  let f' : ℝ → ℝ := fun x => -4 * x / (1 + x ^ 2) ^ 2
  let g : ℝ → ℝ := fun t => log ((1 + t) / (1 - t)) / sqrt (1 - t ^ 2)
  have hf : Continuous f :=
    (continuous_const.sub (continuous_id.pow 2)).div
      (continuous_const.add (continuous_id.pow 2)) (fun x => by positivity)
  have hderiv (x : ℝ) : HasDerivAt f (f' x) x := by
    have h := ((hasDerivAt_pow 2 x).const_sub 1).div
      ((hasDerivAt_pow 2 x).const_add 1) (by positivity : 1 + x ^ 2 ≠ 0)
    convert h using 1
    all_goals first
      | rfl
      | (dsimp [f, f']
         ring)
  have hneg (x : ℝ) (hx : x ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1)) :
      f' x ≤ 0 := by
    have hx0 : 0 ≤ x := by simpa using hx.1.le
    dsimp only [f']
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (sq_nonneg _)
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (a := (0 : ℝ)) (b := 1) (g := g) hf.continuousOn
    (fun x _ => hderiv x) hneg
  have hpoint (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      g (f x) * f' x = -4 * (-log x / (1 + x ^ 2)) := by
    have hx0 : x ≠ 0 := hx.1.ne'
    have hd : 1 + x ^ 2 ≠ 0 := by positivity
    have hp : 1 + f x = 2 / (1 + x ^ 2) := by
      dsimp only [f]
      field_simp
      ring
    have hm : 1 - f x = 2 * x ^ 2 / (1 + x ^ 2) := by
      dsimp only [f]
      field_simp
      ring
    have hr : (1 + f x) / (1 - f x) = 1 / x ^ 2 := by
      rw [hp, hm]
      field_simp
    have hs : 1 - f x ^ 2 = (2 * x / (1 + x ^ 2)) ^ 2 := by
      dsimp only [f]
      field_simp
      ring
    dsimp only [g, f']
    rw [hr, hs, sqrt_sq (div_nonneg (mul_nonneg (by norm_num) hx.1.le) (by positivity)),
      log_div one_ne_zero (pow_ne_zero 2 hx0), log_one, log_pow]
    field_simp
    ring
  have hi : (∫ x in (0 : ℝ)..1, g (f x) * f' x) = -4 * catalan := by
    calc
      _ = ∫ x in (0 : ℝ)..1, -4 * (-log x / (1 + x ^ 2)) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        exact hpoint
      _ = -4 * catalan := by
        rw [intervalIntegral.integral_const_mul, integral_catalanLogKernel]
  have he : (∫ x in (0 : ℝ)..1, g (f x) * f' x) = -(∫ t in (0 : ℝ)..1, g t) := by
    simpa only [Function.comp_apply, f, zero_pow (by decide : 2 ≠ 0), one_pow,
      sub_zero, add_zero, div_one, sub_self, zero_div,
      intervalIntegral.integral_symm (a := (0 : ℝ)) (b := 1)] using hsub
  change (∫ t in (0 : ℝ)..1, g t) = 4 * catalan
  linarith

theorem mixedMoment_zero_zero_eq_log_integral :
    mixedMoment (X ^ 0) (X ^ 0) =
      ∫ t in (0 : ℝ)..1, log ((1 + t) / (1 - t)) / sqrt (1 - t ^ 2) := by
  let F : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..1,
    (|t| / sqrt (1 - t ^ 2)) / (1 - t * s)
  have hint : IntervalIntegrable F volume (-1) 1 := by
    simpa only [F, pow_zero, one_mul, mul_one] using intervalIntegrable_mixedMoment_outer 0 0
  have h0 : (0 : ℝ) ∈ uIcc (-1 : ℝ) 1 := by norm_num
  obtain ⟨hn, hp⟩ := (IntervalIntegrable.trans_iff h0).mp hint
  have hnr : IntervalIntegrable (fun t => F (-t)) volume 0 1 := by
    simpa only [zero_sub, sub_zero, neg_neg] using (hn.comp_sub_left 0).symm
  have hinner {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) (ht0 : t ≠ 0) :
      F t = (|t| / sqrt (1 - t ^ 2)) * (-log (1 - t) / t) := by
    calc
      F t = (|t| / sqrt (1 - t ^ 2)) * (∫ s in (0 : ℝ)..1, 1 / (1 - t * s)) := by
        simp only [F, div_eq_mul_inv, one_mul, intervalIntegral.integral_const_mul]
      _ = _ := by rw [integral_reciprocal_affine ht ht0]
  have hpair {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
      F (-t) + F t = log ((1 + t) / (1 - t)) / sqrt (1 - t ^ 2) := by
    have ht' : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
    have hnt : -t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have ht0 : t ≠ 0 := ht.1.ne'
    have hp0 : 1 + t ≠ 0 := by linarith [ht.1]
    have hm0 : 1 - t ≠ 0 := by linarith [ht.2]
    have hs0 : sqrt (1 - t ^ 2) ≠ 0 := (sqrt_pos.mpr (by nlinarith [ht.1, ht.2])).ne'
    rw [hinner hnt (neg_ne_zero.mpr ht0), hinner ht' ht0,
      abs_neg, abs_of_pos ht.1, neg_sq, sub_neg_eq_add, log_div hp0 hm0]
    field_simp
    ring
  simp only [mixedMoment, pow_zero, Polynomial.eval_one, mul_one]
  change (∫ t in (-1 : ℝ)..1, F t) = _
  calc
    _ = (∫ t in (-1 : ℝ)..0, F t) + ∫ t in (0 : ℝ)..1, F t :=
      (intervalIntegral.integral_add_adjacent_intervals hn hp).symm
    _ = (∫ t in (0 : ℝ)..1, F (-t)) + ∫ t in (0 : ℝ)..1, F t := by
      rw [intervalIntegral.integral_comp_neg]
      norm_num
    _ = ∫ t in (0 : ℝ)..1, F (-t) + F t :=
      (intervalIntegral.integral_add hnr hp).symm
    _ = _ := intervalIntegral.integral_congr_Ioo_of_le (by norm_num) (fun t ht => hpair ht)

theorem mixedMoment_zero_zero : mixedMoment (X ^ 0) (X ^ 0) = 4 * catalan :=
  mixedMoment_zero_zero_eq_log_integral.trans integral_mixedZeroLogKernel

open MeasureTheory Set Real Polynomial
open scoped Interval

theorem integral_s_reciprocal_affine {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1)
    (ht0 : t ≠ 0) :
    (∫ s in (0 : ℝ)..1, s / (1 - t * s)) = (-log (1 - t) - t) / t ^ 2 := by
  have hint : IntervalIntegrable (fun s : ℝ => 1 / (1 - t * s)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact continuousOn_const.div
      (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
      (fun s hs => (mixed_affine_denominator_pos ht hs).ne')
  calc
    _ = ∫ s in (0 : ℝ)..1, (1 / t) * (1 / (1 - t * s) - 1) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      have hd : 1 - t * s ≠ 0 := (mixed_affine_denominator_pos ht hs).ne'
      have hd' : 1 - s * t ≠ 0 := by simpa only [mul_comm] using hd
      field_simp [ht0, hd, hd']
      ring
    _ = (1 / t) * ((∫ s in (0 : ℝ)..1, 1 / (1 - t * s)) - 1) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub hint (continuous_const.intervalIntegrable _ _)]
      simp
    _ = _ := by
      rw [integral_reciprocal_affine ht ht0]
      field_simp

theorem mixedMoment_zero_one_eq_log_integral :
    mixedMoment (X ^ 0) (X ^ 1) =
      ∫ t in (0 : ℝ)..1, -log (1 - t ^ 2) / (t * sqrt (1 - t ^ 2)) := by
  let F : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..1,
    (|t| / sqrt (1 - t ^ 2)) * s / (1 - t * s)
  have hint : IntervalIntegrable F volume (-1) 1 := by
    simpa only [F, pow_zero, pow_one, one_mul] using intervalIntegrable_mixedMoment_outer 0 1
  have h0 : (0 : ℝ) ∈ uIcc (-1 : ℝ) 1 := by norm_num
  obtain ⟨hn, hp⟩ := (IntervalIntegrable.trans_iff h0).mp hint
  have hnr : IntervalIntegrable (fun t => F (-t)) volume 0 1 := by
    simpa only [zero_sub, sub_zero, neg_neg] using (hn.comp_sub_left 0).symm
  have hinner {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) (ht0 : t ≠ 0) :
      F t = (|t| / sqrt (1 - t ^ 2)) * ((-log (1 - t) - t) / t ^ 2) := by
    calc
      F t = (|t| / sqrt (1 - t ^ 2)) *
          (∫ s in (0 : ℝ)..1, s / (1 - t * s)) := by
        simp only [F, div_eq_mul_inv, mul_assoc, intervalIntegral.integral_const_mul]
      _ = _ := by rw [integral_s_reciprocal_affine ht ht0]
  have hpair {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
      F (-t) + F t = -log (1 - t ^ 2) / (t * sqrt (1 - t ^ 2)) := by
    have ht' : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
    have hnt : -t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have ht0 : t ≠ 0 := ht.1.ne'
    have hp0 : 1 + t ≠ 0 := by linarith [ht.1]
    have hm0 : 1 - t ≠ 0 := by linarith [ht.2]
    have hs0 : sqrt (1 - t ^ 2) ≠ 0 :=
      (sqrt_pos.mpr (by nlinarith [ht.1, ht.2])).ne'
    have hlog : log (1 - t ^ 2) = log (1 + t) + log (1 - t) := by
      rw [show 1 - t ^ 2 = (1 + t) * (1 - t) by ring, log_mul hp0 hm0]
    rw [hinner hnt (neg_ne_zero.mpr ht0), hinner ht' ht0,
      abs_neg, abs_of_pos ht.1, neg_sq, sub_neg_eq_add, hlog]
    field_simp
    ring_nf
  simp only [mixedMoment, Polynomial.eval_X, Polynomial.eval_one,
    pow_zero, pow_one, one_mul]
  change (∫ t in (-1 : ℝ)..1, F t) = _
  calc
    _ = (∫ t in (-1 : ℝ)..0, F t) + ∫ t in (0 : ℝ)..1, F t :=
      (intervalIntegral.integral_add_adjacent_intervals hn hp).symm
    _ = (∫ t in (0 : ℝ)..1, F (-t)) + ∫ t in (0 : ℝ)..1, F t := by
      rw [intervalIntegral.integral_comp_neg]
      norm_num
    _ = ∫ t in (0 : ℝ)..1, F (-t) + F t :=
      (intervalIntegral.integral_add hnr hp).symm
    _ = _ := intervalIntegral.integral_congr_Ioo_of_le (by norm_num) (fun t ht => hpair ht)

theorem mixedMoment_zero_one :
    mixedMoment (X ^ 0) (X ^ 1) = (3 / 2 : ℝ) * zetaSeries 0 0 :=
  mixedMoment_zero_one_eq_log_integral.trans integral_mixedOne_logKernel

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Estimates.MomentEvaluation
namespace OAI


noncomputable section

open Filter Polynomial
open scoped BigOperators Topology

namespace InternalCatalan

theorem momentScalar_step (n : ℕ) :
    ((n + 3 : ℕ) : ℚ) * momentScalar (n + 2) =
      ((n + 2 : ℕ) : ℚ) * momentScalar n := by
  rcases Nat.even_or_odd' n with ⟨l, rfl | rfl⟩
  · rw [show 2 * l + 2 = 2 * (l + 1) by omega,
      momentScalar_even, momentScalar_even]
    have hc := centralCoeff_step l
    have hc' := congrArg (fun x : ℚ => ((2 * l + 3 : ℕ) : ℚ) * x) hc
    have hc0 := centralCoeff_ne_zero l
    have hc1 := centralCoeff_ne_zero (l + 1)
    have hden0 : ((2 * l + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hden1 : ((2 * (l + 1) + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    push_cast at hc' ⊢
    field_simp
    nlinarith only [hc']
  · rw [show 2 * l + 1 + 2 = 2 * (l + 1) + 1 by omega,
      momentScalar_odd, momentScalar_odd]
    ring

theorem momentScalar_cast_step (n : ℕ) :
    ((n + 3 : ℕ) : ℝ) * (momentScalar (n + 2) : ℝ) =
      ((n + 2 : ℕ) : ℝ) * (momentScalar n : ℝ) := by
  exact_mod_cast momentScalar_step n

private theorem sum_range_sub_add_two (f : ℕ → ℝ) (n : ℕ) :
    (∑ u ∈ Finset.range n, (f u - f (u + 2))) =
      f 0 + f 1 - f n - f (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

private theorem hasSum_sub_add_two_value (f : ℕ → ℝ)
    (hf : Tendsto f atTop (𝓝 0)) {a : ℝ}
    (ha : HasSum (fun u => f u - f (u + 2)) a) : a = f 0 + f 1 := by
  have ht : Tendsto (fun n => f 0 + f 1 - f n - f (n + 1))
      atTop (𝓝 (f 0 + f 1)) := by
    simpa using
      ((tendsto_const_nhds.sub hf).sub (hf.comp (tendsto_add_atTop_nat 1)))
  have hs := ha.tendsto_sum_nat
  simp only [sum_range_sub_add_two] at hs
  exact tendsto_nhds_unique hs ht

theorem mixedMoment_X_pow_zero_step (d : ℕ) :
    ((d + 2 : ℕ) : ℝ) * mixedMoment (X ^ (d + 2)) (X ^ 0) =
      ((d + 1 : ℕ) : ℝ) * mixedMoment (X ^ d) (X ^ 0) +
        (momentScalar d : ℝ) + (momentScalar (d + 1) : ℝ) := by
  have hs := ((hasSum_mixedMoment_X_pow (d + 2) 0).mul_left
      ((d + 2 : ℕ) : ℝ)).sub
    ((hasSum_mixedMoment_X_pow d 0).mul_left ((d + 1 : ℕ) : ℝ))
  have hs' : HasSum
      (fun u => (momentScalar (d + u) : ℝ) - (momentScalar (d + u + 2) : ℝ))
      (((d + 2 : ℕ) : ℝ) * mixedMoment (X ^ (d + 2)) (X ^ 0) -
        ((d + 1 : ℕ) : ℝ) * mixedMoment (X ^ d) (X ^ 0)) := by
    convert hs using 1
    rfl
    ext u
    have hrec := momentScalar_cast_step (d + u)
    have he : d + 2 + u = d + u + 2 := by omega
    simp only [Nat.zero_add, he]
    have hu : (u : ℝ) + 1 ≠ 0 := by positivity
    push_cast at hrec ⊢
    field_simp [hu]
    nlinarith only [hrec]
  have hlim : Tendsto (fun u => (momentScalar (d + u) : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.add_comm d] using
      tendsto_momentScalar_zero.comp (tendsto_add_atTop_nat d)
  have hv := hasSum_sub_add_two_value _ hlim hs'
  simp only [Nat.add_zero] at hv
  linarith

theorem mixedMoment_X_one_zero : mixedMoment (X ^ 1) (X ^ 0) = 2 := by
  have hs := (hasSum_nat_add_iff' 1).mpr (hasSum_mixedMoment_X_pow 1 0)
  have hs' : HasSum
      (fun u => (momentScalar u : ℝ) - (momentScalar (u + 2) : ℝ))
      (mixedMoment (X ^ 1) (X ^ 0)) := by
    convert hs using 1
    · rfl
    · ext u
      have hrec := momentScalar_cast_step u
      have hu : (u : ℝ) + 2 ≠ 0 := by positivity
      simp only [Nat.zero_add, show 1 + (u + 1) = u + 2 by omega]
      push_cast at hrec ⊢
      field_simp [hu]
      nlinarith only [hrec]
    · simp [momentScalar_odd 0]
  have hv := hasSum_sub_add_two_value _ tendsto_momentScalar_zero hs'
  simpa [momentScalar_odd 0] using hv

theorem mixedMoment_zero_X_pow_step (d : ℕ) :
    ((d + 1 : ℕ) : ℝ) * mixedMoment (X ^ 0) (X ^ (d + 2)) =
      (d : ℝ) * mixedMoment (X ^ 0) (X ^ d) + 2 / ((d + 1 : ℕ) : ℝ) := by
  have htail := (hasSum_nat_add_iff' 2).mpr (hasSum_mixedMoment_X_pow 0 d)
  have htail' : HasSum
      (fun u => (momentScalar (u + 2) : ℝ) / ((d + u + 3 : ℕ) : ℝ))
      (mixedMoment (X ^ 0) (X ^ d) - 2 / ((d + 1 : ℕ) : ℝ)) := by
    convert htail using 1
    · rfl
    · ext u
      simp only [Nat.zero_add]
      congr 2
    · simp [Finset.sum_range_succ, momentScalar_odd 0]
  have hs := ((hasSum_mixedMoment_X_pow 0 (d + 2)).mul_left
      ((d + 1 : ℕ) : ℝ)).sub (htail'.mul_left (d : ℝ))
  have hs' : HasSum
      (fun u => (momentScalar u : ℝ) - (momentScalar (u + 2) : ℝ))
      (((d + 1 : ℕ) : ℝ) * mixedMoment (X ^ 0) (X ^ (d + 2)) -
        (d : ℝ) * (mixedMoment (X ^ 0) (X ^ d) - 2 / ((d + 1 : ℕ) : ℝ))) := by
    convert hs using 1
    rfl
    ext u
    have hrec := momentScalar_cast_step u
    have he : d + 2 + u + 1 = d + u + 3 := by omega
    simp only [Nat.zero_add, he]
    have hu : (d : ℝ) + (u : ℝ) + 3 ≠ 0 := by positivity
    push_cast at hrec ⊢
    field_simp [hu]
    nlinarith only [hrec]
  have hv := hasSum_sub_add_two_value _ tendsto_momentScalar_zero hs'
  have hd : (d : ℝ) + 1 ≠ 0 := by positivity
  simp only [momentScalar_zero, momentScalar_odd 0, Rat.cast_ofNat,
    Rat.cast_zero, add_zero] at hv
  push_cast at hv ⊢
  field_simp [hd] at hv ⊢
  nlinarith only [hv]

end InternalCatalan

end



noncomputable section

open Polynomial

namespace InternalCatalan

theorem mixedMoment_minus_decomposition (d : ℕ) :
    mixedMoment (X ^ d) (X ^ 0) = (boundaryMinus d : ℝ) +
      mixedMoment 1 1 * (centralCoeffKernel (d : ℤ) : ℝ) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    cases d with
    | zero => simp
    | succ d =>
      cases d with
      | zero =>
        simpa [centralCoeffKernel] using mixedMoment_X_one_zero
      | succ d =>
        change mixedMoment (X ^ (d + 2)) (X ^ 0) = (boundaryMinus (d + 2) : ℝ) +
          mixedMoment 1 1 * (centralCoeffKernel ((d + 2 : ℕ) : ℤ) : ℝ)
        have ha := mixedMoment_X_pow_zero_step d
        rw [ih d (by omega)] at ha
        have hr : ((d + 2 : ℕ) : ℝ) * (boundaryMinus (d + 2) : ℝ) =
            ((d + 1 : ℕ) : ℝ) * (boundaryMinus d : ℝ) +
              (momentScalar d : ℝ) + (momentScalar (d + 1) : ℝ) := by
          exact_mod_cast boundaryMinus_step d
        have hc : ((d + 2 : ℕ) : ℝ) *
              (centralCoeffKernel ((d + 2 : ℕ) : ℤ) : ℝ) =
            ((d + 1 : ℕ) : ℝ) * (centralCoeffKernel (d : ℤ) : ℝ) := by
          exact_mod_cast centralCoeffKernel_nat_step d
        have hstart := congrArg (fun x : ℝ => mixedMoment 1 1 * x) hc
        have hd : ((d + 2 : ℕ) : ℝ) ≠ 0 := by positivity
        apply mul_left_cancel₀ hd
        nlinarith only [ha, hr, hstart]

theorem mixedMoment_plus_succ_decomposition (u : ℕ) :
    mixedMoment (X ^ 0) (X ^ (u + 1)) = (boundaryPlus (u + 1) : ℝ) +
      mixedMoment 1 X * (centralCoeffKernel (u : ℤ) : ℝ) := by
  induction u using Nat.strong_induction_on with
  | h u ih =>
    cases u with
    | zero => simp
    | succ u =>
      cases u with
      | zero =>
        have ha := mixedMoment_zero_X_pow_step 0
        norm_num at ha
        simpa [boundaryPlus, centralCoeffKernel] using ha
      | succ u =>
        change mixedMoment (X ^ 0) (X ^ (u + 2 + 1)) =
          (boundaryPlus (u + 2 + 1) : ℝ) +
            mixedMoment 1 X * (centralCoeffKernel ((u + 2 : ℕ) : ℤ) : ℝ)
        have ha := mixedMoment_zero_X_pow_step (u + 1)
        rw [ih u (by omega)] at ha
        have hr : ((u + 1 + 1 : ℕ) : ℝ) * (boundaryPlus (u + 1 + 2) : ℝ) =
            ((u + 1 : ℕ) : ℝ) * (boundaryPlus (u + 1) : ℝ) +
              2 / ((u + 1 + 1 : ℕ) : ℝ) := by
          have hr0 := congrArg (fun x : ℚ => (x : ℝ)) (boundaryPlus_step (u + 1))
          push_cast at hr0 ⊢
          exact hr0
        have hc : ((u + 2 : ℕ) : ℝ) *
              (centralCoeffKernel ((u + 2 : ℕ) : ℤ) : ℝ) =
            ((u + 1 : ℕ) : ℝ) * (centralCoeffKernel (u : ℤ) : ℝ) := by
          exact_mod_cast centralCoeffKernel_nat_step u
        have hstart := congrArg (fun x : ℝ => mixedMoment 1 X * x) hc
        have hu : ((u + 2 : ℕ) : ℝ) ≠ 0 := by positivity
        apply mul_left_cancel₀ hu
        nlinarith only [ha, hr, hstart]

theorem mixedMoment_X_pow_decomposition (i j : ℕ) :
    mixedMoment (X ^ i) (X ^ j) = (momentRat i j : ℝ) +
      mixedMoment 1 1 * (centralCoeffKernel ((i : ℤ) - (j : ℤ)) : ℝ) +
      mixedMoment 1 X * (centralCoeffKernel ((j : ℤ) - (i : ℤ) - 1) : ℝ) := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero => norm_num [centralCoeffKernel]
    | succ j =>
      have hn : centralCoeffKernel ((0 : ℤ) - ((j + 1 : ℕ) : ℤ)) = 0 :=
        centralCoeffKernel_of_neg (by omega)
      have he : ((j + 1 : ℕ) : ℤ) - (0 : ℤ) - 1 = (j : ℤ) := by omega
      simp only [Nat.cast_zero]
      rw [momentRat_zero_left, hn, he]
      simpa using mixedMoment_plus_succ_decomposition j
  | succ i ih =>
    cases j with
    | zero =>
      have hn : centralCoeffKernel ((0 : ℤ) - ((i + 1 : ℕ) : ℤ) - 1) = 0 :=
        centralCoeffKernel_of_neg (by omega)
      simp only [Nat.cast_zero]
      rw [momentRat_zero_right, hn]
      simpa using mixedMoment_minus_decomposition (i + 1)
    | succ j =>
      have ha := mixedMoment_X_pow_step i j
      have hr : (momentRat i j : ℝ) - (momentRat (i + 1) (j + 1) : ℝ) =
          (momentScalar i : ℝ) / ((j + 1 : ℕ) : ℝ) := by
        exact_mod_cast momentRat_step i j
      have hd : ((i + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ) =
          (i : ℤ) - (j : ℤ) := by omega
      have he : ((j + 1 : ℕ) : ℤ) - ((i + 1 : ℕ) : ℤ) - 1 =
          (j : ℤ) - (i : ℤ) - 1 := by omega
      change mixedMoment (X ^ (i + 1)) (X ^ (j + 1)) =
        (momentRat (i + 1) (j + 1) : ℝ) +
          mixedMoment 1 1 * (centralCoeffKernel (((i + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ)) : ℝ) +
          mixedMoment 1 X *
            (centralCoeffKernel (((j + 1 : ℕ) : ℤ) - ((i + 1 : ℕ) : ℤ) - 1) : ℝ)
      rw [hd, he]
      rw [ih j] at ha
      linarith only [ha, hr]

end InternalCatalan

end



noncomputable section

open Polynomial

namespace InternalCatalan

theorem mixedMoment_X_pow_evaluation (i j : ℕ) :
    mixedMoment (X ^ i) (X ^ j) = (momentRat i j : ℝ) +
      4 * catalan * (centralCoeffKernel ((i : ℤ) - (j : ℤ)) : ℝ) +
      (3 / 2 : ℝ) * zetaSeries 0 0 *
        (centralCoeffKernel ((j : ℤ) - (i : ℤ) - 1) : ℝ) := by
  have hzero : mixedMoment 1 1 = 4 * catalan := by
    simpa only [pow_zero] using mixedMoment_zero_zero
  have hone : mixedMoment 1 X = (3 / 2 : ℝ) * zetaSeries 0 0 := by
    simpa only [pow_zero, pow_one] using mixedMoment_zero_one
  rw [mixedMoment_X_pow_decomposition, hzero, hone]

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Polynomial.Rationality
namespace OAI


noncomputable section

open Polynomial
open scoped BigOperators

namespace InternalCatalan

theorem row_contact_real {N r j : ℕ} (hN : 0 < N)
    (hr : r < n N) (hj : j < L N) :
    (∑ i ∈ Finset.range (H N),
      ((rowP N r).coeff i : ℝ) *
        (centralCoeffKernel ((j : ℤ) - i - 1) : ℝ)) =
      ((rowD N r).coeff j : ℝ) := by
  exact_mod_cast row_contact hN hr hj

theorem mixedMoment_rowP_evaluation {N r j : ℕ} (hN : 0 < N)
    (hr : r < n N) (hj : j < L N) :
    mixedMoment (realPoly (rowP N r)) (X ^ j) =
      (∑ i ∈ Finset.range (H N), ((rowP N r).coeff i : ℝ) *
        ((momentRat i j : ℝ) +
          4 * catalan * (centralCoeffKernel ((i : ℤ) - j) : ℝ))) +
      (3 / 2 : ℝ) * zetaSeries 0 0 * ((rowD N r).coeff j : ℝ) := by
  rw [mixedMoment_rowP_X_pow_eq_sum_range hN r j]
  simp_rw [mixedMoment_X_pow_evaluation]
  calc
    _ = ∑ i ∈ Finset.range (H N),
        ((((rowP N r).coeff i : ℝ) *
          ((momentRat i j : ℝ) +
            4 * catalan * (centralCoeffKernel ((i : ℤ) - j) : ℝ))) +
        ((3 / 2 : ℝ) * zetaSeries 0 0) *
          (((rowP N r).coeff i : ℝ) *
            (centralCoeffKernel ((j : ℤ) - i - 1) : ℝ))) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, row_contact_real hN hr hj]

theorem zetaMoment_rowD_evaluation {N r j : ℕ} (hN : 0 < N)
    (hj : j < L N) :
    zetaMoment (realPoly (rowD N r)) (X ^ j) =
      (∑ i ∈ Finset.range (H N),
        ((rowD N r).coeff i : ℝ) * (zetaRat i j : ℝ)) +
      ((rowD N r).coeff j : ℝ) * zetaSeries 0 0 := by
  have hjH : j < H N := by
    unfold L H at *
    omega
  rw [zetaMoment_rowD_X_pow_eq_sum_range hN r j]
  have hterms :
      (∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℝ) * zetaSeries i j) =
        ∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℝ) *
          ((zetaRat i j : ℝ) + if i = j then zetaSeries 0 0 else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [zetaSeries_eq_zetaRat_add i j]
  rw [hterms]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [hij]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr hjH))

theorem rawEntryRat_cast {z : ℚ} {N r j : ℕ} (hz : (z : ℝ) = catalan)
    (hN : 0 < N) (hr : r < n N) (hj : j < L N) :
    (rawEntryRat z N r j : ℝ) =
      mixedMoment (realPoly (rowP N r)) (X ^ j) -
        (3 / 2 : ℝ) * zetaMoment (realPoly (rowD N r)) (X ^ j) := by
  rw [mixedMoment_rowP_evaluation hN hr hj, zetaMoment_rowD_evaluation hN hj]
  unfold rawEntryRat
  push_cast
  rw [hz]
  ring

theorem filteredEntryRat_cast {z : ℚ} {N r k : ℕ} (hz : (z : ℝ) = catalan)
    (hN : 0 < N) (hr : r < n N) (hk : k < n N) :
    (filteredEntryRat z N r k : ℝ) = determinantEntry N r k := by
  unfold filteredEntryRat determinantEntry
  push_cast
  rw [mixedMoment_filteredColumn, zetaMoment_filteredColumn,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  have hvq : v ≤ q N := by
    have hv' := Finset.mem_range.mp hv
    omega
  rw [rawEntryRat_cast hz hN hr (rawColumn_lt_L hk hvq)]
  ring

theorem determinantRat_cast {z : ℚ} {N : ℕ} (hz : (z : ℝ) = catalan)
    (hN : 0 < N) : (determinantRat z N : ℝ) = determinant N := by
  let Rmat : Matrix (Fin (n N)) (Fin (n N)) ℚ :=
    fun r k => filteredEntryRat z N r.val k.val
  let Amat : Matrix (Fin (n N)) (Fin (n N)) ℝ :=
    fun r k => determinantEntry N r.val k.val
  have hm : Rmat.map (fun x : ℚ => (x : ℝ)) = Amat := by
    ext r k
    exact filteredEntryRat_cast hz hN r.isLt k.isLt
  change (Rmat.det : ℝ) = Amat.det
  exact (Rat.cast_det (F := ℝ) Rmat).trans (congrArg Matrix.det hm)

theorem determinantRat_ne_zero_iff {z : ℚ} {N : ℕ}
    (hz : (z : ℝ) = catalan) (hN : 0 < N) :
    determinantRat z N ≠ 0 ↔ determinant N ≠ 0 := by
  rw [← determinantRat_cast hz hN]
  norm_cast

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Arithmetic.PrimeNonvanishing
namespace OAI

section

noncomputable section

namespace InternalCatalan

open scoped BigOperators



end InternalCatalan

end

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

section

noncomputable section

namespace InternalCatalan




def nonzeroPrimeScale (z : ℚ) (k : ℕ) : ℕ :=
  Classical.choose (Nat.exists_infinite_primes (palindromicPrimeCutoff z + k + 1))

theorem nonzeroPrimeScale_bound (z : ℚ) (k : ℕ) :
    palindromicPrimeCutoff z + k + 1 ≤ nonzeroPrimeScale z k :=
  (Classical.choose_spec
    (Nat.exists_infinite_primes (palindromicPrimeCutoff z + k + 1))).1

theorem nonzeroPrimeScale_prime (z : ℚ) (k : ℕ) : (nonzeroPrimeScale z k).Prime :=
  (Classical.choose_spec
    (Nat.exists_infinite_primes (palindromicPrimeCutoff z + k + 1))).2

theorem nonzeroPrimeScale_tendsto (z : ℚ) :
    Filter.Tendsto (nonzeroPrimeScale z) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro b
  refine ⟨b, ?_⟩
  intro k hk
  have hbound := nonzeroPrimeScale_bound z k
  omega

theorem determinantRat_nonzeroPrimeScale_ne_zero (z : ℚ) (k : ℕ) :
    determinantRat z (nonzeroPrimeScale z k) ≠ 0 := by
  let : Fact (nonzeroPrimeScale z k).Prime := ⟨nonzeroPrimeScale_prime z k⟩
  apply determinantRat_prime_ne_zero
  have hbound := nonzeroPrimeScale_bound z k
  omega

theorem determinant_nonzeroPrimeScale_ne_zero {z : ℚ}
    (hz : (z : ℝ) = catalan) (k : ℕ) : determinant (nonzeroPrimeScale z k) ≠ 0 :=
  (determinantRat_ne_zero_iff hz (nonzeroPrimeScale_prime z k).pos).mp
    (determinantRat_nonzeroPrimeScale_ne_zero z k)


end InternalCatalan

end

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Results.Conclusions
namespace OAI

section

namespace InternalCatalan

theorem catalan_irrational :
    Irrational (∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) := by
  change Irrational catalan
  rintro ⟨z, hz⟩
  have hfinite := (nonzeroPrimeScale_tendsto z).eventually
    (determinantRat_finite_place_threshold z)
  have hreal := (nonzeroPrimeScale_tendsto z).eventually
    eventually_realDeterminant_log_upper
  obtain ⟨k, hkfinite, hkreal⟩ := (hfinite.and hreal).exists
  have hf := hkfinite (determinantRat_nonzeroPrimeScale_ne_zero z k)
  have hr := hkreal (determinant_nonzeroPrimeScale_ne_zero hz k)
  rw [determinantRat_cast hz (nonzeroPrimeScale_prime z k).pos] at hf
  linarith [finitePlace_realPlace_threshold_gap]

end InternalCatalan

end

end OAI

end

theorem solution :
    Irrational (∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) :=
  OAI.InternalCatalan.catalan_irrational
