-- Prove2me | solution 1 for OAI.Erdos970.NumberTheoryLean.SourceSuccessfulTail.source_successful_tail_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:08:35.469254+00:00
-- url     : https://prove2.me/submissions/7e63e345-5be4-4633-b0da-fa8e8e065564

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Definitions.Def_OAIQ247J010
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_RegenerationBandBounds_regeneration_uniform_band_jb247

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FiniteHistorySupport
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.FinitePathGeometry

open Set
open DerivativeWeights TransitionKernels

theorem cost_pos {t : ℝ} (ht : 0 < t) : 0 < cost t := by
  unfold cost
  exact Real.log_pos (by have h : 0 < 1 / t := one_div_pos.mpr ht; linarith)

theorem nextGap_eq_cost {r t : ℝ} (ht : 0 < t) : nextGap r t = r * Real.exp (-cost t) := by
  have hx : 0 < 1 + 1 / t := by positivity
  unfold cost nextGap
  rw [Real.exp_neg, Real.exp_log hx]
  field_simp

end NumberTheoryLean.FinitePathGeometry



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_WeightIntegrals
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.TwoStepDensityBounds

open Set
open DerivativeWeights WeightFutureIntegrals FinitePathGeometry

theorem weight_antitone {i : Side} {s t : ℝ} (hs : Valid i s) (ht : Valid i t) (hst : s ≤ t) :
    weight i t ≤ weight i s := by
  cases i with
  | even =>
    exact phiEven_strictAntiOn.antitoneOn
      (by change 1 < s; dsimp [Valid] at hs <;> linarith)
      (by change 1 < t; dsimp [Valid] at ht <;> linarith) hst
  | odd => exact phiOdd_antitone hst

end NumberTheoryLean.TwoStepDensityBounds

end

section

open Set MeasureTheory
namespace Erdos970Dependency.WeightIntegrals
open NumberTheoryLean.DerivativeWeights NumberTheoryLean.WeightFutureIntegrals

theorem W_continuousAt {t : ℝ} (ht : t ≠ 0) : ContinuousAt W t := by
  unfold W
  fun_prop (disch := simp [ht])

theorem wPrimitive_deriv {t : ℝ} (ht : 0 < t) : HasDerivAt wPrimitive (W t) t := by
  have h := (Real.hasDerivAt_log (ne_of_gt ht)).sub
    ((hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) (ne_of_gt ht))
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [W, id_eq, zero_mul, zero_sub, mul_one]
  field_simp
  ring

theorem wMass_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    wMass a b = wPrimitive b - wPrimitive a := by
  have hp (t : ℝ) (ht : t ∈ uIcc a b) : 0 < t :=
    lt_of_lt_of_le (lt_min ha hb) ht.1
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    exact wPrimitive_deriv (hp t ht)
  · apply ContinuousOn.intervalIntegrable
    intro t ht
    exact (W_continuousAt (ne_of_gt (hp t ht))).continuousWithinAt

theorem wMass_nonneg {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : 0 ≤ wMass a b := by
  apply intervalIntegral.integral_nonneg hab
  intro t ht
  exact (W_pos (ha.trans_le ht.1)).le

theorem wMass_mono_right {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    wMass a b ≤ wMass a c := by
  have hsplit : wMass a c = wMass a b + wMass b c := by
    rw [wMass_eq ha (ha.trans_le (hab.trans hbc)), wMass_eq ha (ha.trans_le hab),
      wMass_eq (ha.trans_le hab) (ha.trans_le (hab.trans hbc))]
    ring
  rw [hsplit]
  linarith [wMass_nonneg (ha.trans_le hab) hbc]

theorem wMass_two_three_lower : (1 : ℝ) / 3 ≤ wMass 2 3 := by
  have hW : ∀ t ∈ Icc (2 : ℝ) 3, (1 : ℝ) / 3 ≤ W t := by
    intro t ht
    exact NumberTheoryLean.TwoStepDensityBounds.W_lower (by linarith [ht.1]) ht.2
  have hI : IntervalIntegrable W volume 2 3 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] at ht
    exact (W_continuousAt (by linarith [ht.1])).continuousWithinAt
  have h := intervalIntegral.integral_mono_on (by norm_num : (2 : ℝ) ≤ 3)
    (by simp : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ) / 3) volume 2 3) hI hW
  norm_num only [intervalIntegral.integral_const, smul_eq_mul] at h
  exact h

theorem wMass_initial_upper {a : ℝ} (ha : 99 / 100 ≤ a) (ha2 : a ≤ 2) : wMass a 2 ≤ 5 := by
  have ha0 : 0 < a := by linarith
  have hW : ∀ t ∈ Icc a (2 : ℝ), W t ≤ 4 := by
    intro t ht
    have ht0 : 0 < t := ha0.trans_le ht.1
    unfold W
    apply (div_le_iff₀ (sq_pos_of_pos ht0)).mpr
    nlinarith [sq_nonneg (t - 99 / 100), ht.1, ht.2]
  have hI : IntervalIntegrable W volume a 2 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le ha2] at ht
    exact (W_continuousAt (ne_of_gt (ha0.trans_le ht.1))).continuousWithinAt
  have h := intervalIntegral.integral_mono_on ha2 hI
    (by simp : IntervalIntegrable (fun _ : ℝ ↦ (4 : ℝ)) volume a 2) hW
  simp only [intervalIntegral.integral_const, smul_eq_mul] at h
  exact h.trans (by linarith)

theorem tailW_measurable : Measurable tailW := by
  unfold tailW wPrimitive
  fun_prop

theorem tailW_eq_mass {u : ℝ} (hu : 1 ≤ u) : tailW u = wMass 2 (u + 1) := by
  rw [wMass_eq (by norm_num) (by linarith : 0 < u + 1)]
  rfl

theorem tailW_nonneg {u : ℝ} (hu : 1 ≤ u) : 0 ≤ tailW u := by
  rw [tailW_eq_mass hu]
  exact wMass_nonneg (by norm_num) (by linarith)

theorem tailW_continuousAt {u : ℝ} (hu : 0 < u) : ContinuousAt tailW u := by
  have hc := (wPrimitive_deriv (by linarith : 0 < u + 1)).continuousAt
  exact (hc.comp (f := fun x : ℝ ↦ x + 1) (x := u)
    (continuousAt_id.add continuousAt_const)).sub continuousAt_const

theorem regKernel_continuousOn {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun u ↦ W u * tailW u) (Icc a b) := by
  intro u hu
  have hu0 : 0 < u := ha.trans_le hu.1
  exact ((W_continuousAt (ne_of_gt hu0)).mul (tailW_continuousAt hu0)).continuousWithinAt

theorem wKernel_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable W volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro u hu
  rw [uIcc_of_le hab] at hu
  exact (W_continuousAt (ne_of_gt (ha.trans_le hu.1))).continuousWithinAt

theorem regIntegral_lower {t : ℝ} (ht : 2 ≤ t) :
    (1 : ℝ) / 3 * wMass 2 (t + 1) ≤ regIntegral t := by
  have h12 : IntervalIntegrable (fun u ↦ W u * tailW u) volume 1 2 :=
    (regKernel_continuousOn (b := 2) (by norm_num : (0 : ℝ) < 1)).intervalIntegrable_of_Icc (by norm_num)
  have h2T : IntervalIntegrable (fun u ↦ W u * tailW u) volume 2 (t + 1) :=
    (regKernel_continuousOn (b := t + 1) (by norm_num : (0 : ℝ) < 2)).intervalIntegrable_of_Icc (by linarith)
  have hfirst : 0 ≤ ∫ u in (1 : ℝ)..2, W u * tailW u := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u hu
    exact mul_nonneg (W_pos (by linarith [hu.1])).le (tailW_nonneg hu.1)
  have hbound : (1 : ℝ) / 3 * wMass 2 (t + 1) ≤ ∫ u in (2 : ℝ)..t + 1, W u * tailW u := by
    unfold wMass
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by linarith)
      ((wKernel_intervalIntegrable (by norm_num) (by linarith : (2 : ℝ) ≤ t + 1)).const_mul _) h2T
    intro u hu
    have htail : (1 : ℝ) / 3 ≤ tailW u := by
      rw [tailW_eq_mass (by linarith [hu.1])]
      exact wMass_two_three_lower.trans (wMass_mono_right (by norm_num) (by norm_num) (by linarith [hu.1]))
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left htail (W_pos (by linarith [hu.1])).le
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h12 h2T
  unfold regIntegral
  linarith

theorem regIntegral_nonneg {t : ℝ} (ht : 2 ≤ t) : 0 ≤ regIntegral t :=
  le_trans (mul_nonneg (by norm_num) (wMass_nonneg (by norm_num) (by linarith))) (regIntegral_lower ht)

theorem initial_integral_le {s t : ℝ} (hs : 199 / 100 ≤ s) (hsup : s ≤ 23 / 10) (ht : 2 ≤ t) :
    wMass (s - 1) (t + 1) ≤ 48 * regIntegral t := by
  have ha : 0 < s - 1 := by linarith
  have hsplit : wMass (s - 1) (t + 1) = wMass (s - 1) 2 + wMass 2 (t + 1) := by
    rw [wMass_eq ha (by linarith), wMass_eq ha (by norm_num), wMass_eq (by norm_num) (by linarith)]
    ring
  have hsmall := wMass_initial_upper (a := s - 1) (by linarith) (by linarith)
  have hbig : (1 : ℝ) / 3 ≤ wMass 2 (t + 1) :=
    wMass_two_three_lower.trans (wMass_mono_right (by norm_num) (by norm_num) (by linarith))
  have hreg := regIntegral_lower ht
  rw [hsplit]
  linarith

end Erdos970Dependency.WeightIntegrals

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_InverseWeightGrowth
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.WeightGlobalBounds

open Filter Set
open scoped Topology
open LinearSieveFunctions BuchstabBridge DerivativeWeights WeightTailBounds

theorem weights_global_logDeriv_bound : ∃ C : ℝ, 0 < C ∧
    (∀ s : ℝ, 198 / 100 ≤ s →
      |deriv phiEven s / phiEven s| ≤ C * (1 + s) ^ 3) ∧
    (∀ s : ℝ, 3 < s → |deriv phiOdd s / phiOdd s| ≤ C * (1 + s) ^ 3) := by
  obtain ⟨C, hC, he, ho⟩ := weights_global_ratio_bound
  refine ⟨4 * C, by positivity, ?_, ?_⟩
  · intro s hs
    have hs1 : 1 < s := by linarith
    have hcoeff : s / (s - 1) ^ 2 ≤ 4 * (1 + s) := by
      apply (div_le_iff₀ (sq_pos_of_pos (by linarith))).mpr
      have hsq : (1 : ℝ) / 4 ≤ (s - 1) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4 * (1 + s) by linarith)]
    have hr0 : 0 ≤ phiOdd (s - 1) / phiEven s :=
      (div_pos (phiOdd_pos _) (phiEven_pos hs1)).le
    have hn : 0 ≤ -deriv phiEven s / phiEven s := by rw [even_logDeriv_eq hs1]; positivity
    have habs : |deriv phiEven s / phiEven s| = -deriv phiEven s / phiEven s := by
      rw [abs_of_nonpos (by rw [neg_div] at hn; linarith)]
      ring
    rw [habs, even_logDeriv_eq hs1]
    calc
      _ ≤ (4 * (1 + s)) * (C * (1 + s) ^ 2) := mul_le_mul hcoeff (he s hs) hr0 (by linarith)
      _ = _ := by ring
  · intro s hs
    have hcoeff : s / (s - 1) ^ 2 ≤ 4 * (1 + s) := by
      apply (div_le_iff₀ (sq_pos_of_pos (by linarith))).mpr
      have hsq : 1 ≤ (s - 1) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4 * (1 + s) by linarith)]
    have hr : phiEven (s - 1) / phiOdd s ≤ C * (1 + s) ^ 2 := by
      have h := ho s (by linarith)
      rwa [max_eq_right (show 2 ≤ s - 1 by linarith)] at h
    have hr0 : 0 ≤ phiEven (s - 1) / phiOdd s :=
      (div_pos (phiEven_pos (by linarith)) (phiOdd_pos s)).le
    have hn : 0 ≤ -deriv phiOdd s / phiOdd s := by rw [odd_logDeriv_eq hs]; positivity
    have habs : |deriv phiOdd s / phiOdd s| = -deriv phiOdd s / phiOdd s := by
      rw [abs_of_nonpos (by rw [neg_div] at hn; linarith)]
      ring
    rw [habs, odd_logDeriv_eq hs]
    calc
      _ ≤ (4 * (1 + s)) * (C * (1 + s) ^ 2) := mul_le_mul hcoeff hr hr0 (by linarith)
      _ = _ := by ring

theorem interval_abs_bound {H d : ℝ → ℝ} {a b B : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn H (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt H (d t) t)
    (hb : ∀ t ∈ Ioo a b, |d t| ≤ B) : |H b - H a| ≤ B * (b - a) := by
  rcases eq_or_lt_of_le hab with h | h
  · subst b
    simp
  · obtain ⟨t, ht, heq⟩ := exists_deriv_eq_slope H h hc
      (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    rw [(hd t ht).deriv] at heq
    have hbound := hb t ht
    rw [heq, abs_div, abs_of_pos (sub_pos.mpr h)] at hbound
    exact (div_le_iff₀ (sub_pos.mpr h)).mp hbound

theorem phiOdd_max_three (s : ℝ) : phiOdd (max 3 s) = phiOdd s := by
  by_cases hs : s ≤ 3
  · rw [max_eq_left hs, phiOdd_initial le_rfl, phiOdd_initial hs]
  · rw [max_eq_right (le_of_not_ge hs)]

theorem weights_log_lipschitz : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 3 ≤ S →
    (∀ u v : ℝ, 198 / 100 ≤ u → 198 / 100 ≤ v → u ≤ S → v ≤ S →
      |Real.log (phiEven u) - Real.log (phiEven v)| ≤ C * (1 + S) ^ 3 * |u - v|) ∧
    (∀ u v : ℝ, 95 / 100 ≤ u → 95 / 100 ≤ v → u ≤ S → v ≤ S →
      |Real.log (phiOdd u) - Real.log (phiOdd v)| ≤ C * (1 + S) ^ 3 * |u - v|) := by
  obtain ⟨C, hC, he, ho⟩ := weights_global_logDeriv_bound
  refine ⟨C, hC, ?_⟩
  intro S hS
  have he_ordered : ∀ u v : ℝ, 198 / 100 ≤ u → u ≤ v → v ≤ S →
      |Real.log (phiEven v) - Real.log (phiEven u)| ≤ C * (1 + S) ^ 3 * (v - u) := by
    intro u v hu huv hv
    apply interval_abs_bound huv
    · intro t ht
      have ht1 : 1 < t := by linarith [ht.1]
      exact ((phiEven_continuousAt ht1).log (ne_of_gt (phiEven_pos ht1))).continuousWithinAt
    · intro t ht
      exact ((phiEven_hasDerivAt (by linarith [ht.1])).differentiableAt.hasDerivAt.log
        (ne_of_gt (phiEven_pos (by linarith [ht.1]))))
    · intro t ht
      have h := he t (by linarith [ht.1])
      apply le_trans h
      apply mul_le_mul_of_nonneg_left _ hC.le
      gcongr <;> linarith [ht.1, ht.2]
  have ho_ordered : ∀ u v : ℝ, 3 ≤ u → u ≤ v → v ≤ S →
      |Real.log (phiOdd v) - Real.log (phiOdd u)| ≤ C * (1 + S) ^ 3 * (v - u) := by
    intro u v hu huv hv
    apply interval_abs_bound huv
    · intro t _
      exact (phiOdd_continuous.continuousAt.log (ne_of_gt (phiOdd_pos t))).continuousWithinAt
    · intro t ht
      exact ((phiOdd_hasDerivAt (by linarith [ht.1])).differentiableAt.hasDerivAt.log
        (ne_of_gt (phiOdd_pos t)))
    · intro t ht
      have h := ho t (by linarith [ht.1])
      apply le_trans h
      apply mul_le_mul_of_nonneg_left _ hC.le
      gcongr <;> linarith [ht.1, ht.2]
  constructor
  · intro u v hu hv huS hvS
    rcases le_total u v with huv | hvu
    · rw [abs_sub_comm (Real.log (phiEven u)), abs_sub_comm u, abs_of_nonneg (sub_nonneg.mpr huv)]
      exact he_ordered u v hu huv hvS
    · rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
      exact he_ordered v u hv hvu huS
  · have ho_clamped : ∀ u v : ℝ, u ≤ v → v ≤ S →
        |Real.log (phiOdd v) - Real.log (phiOdd u)| ≤ C * (1 + S) ^ 3 * (v - u) := by
      intro u v huv hvS
      have hmax : max 3 u ≤ max 3 v := max_le_max_left 3 huv
      have hdiff : max 3 v - max 3 u ≤ v - u := by
        by_cases hu : u ≤ 3
        · rw [max_eq_left hu]
          by_cases hv : v ≤ 3
          · rw [max_eq_left hv]
            linarith
          · rw [max_eq_right (le_of_not_ge hv)]
            linarith
        · rw [max_eq_right (le_of_not_ge hu), max_eq_right (show 3 ≤ v by linarith)]
      have h := ho_ordered (max 3 u) (max 3 v) (le_max_left _ _) hmax (max_le hS hvS)
      rw [phiOdd_max_three, phiOdd_max_three] at h
      exact le_trans h (mul_le_mul_of_nonneg_left hdiff (by positivity))
    intro u v _ _ huS hvS
    rcases le_total u v with huv | hvu
    · rw [abs_sub_comm (Real.log (phiOdd u)), abs_sub_comm u, abs_of_nonneg (sub_nonneg.mpr huv)]
      exact ho_clamped u v huv hvS
    · rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
      exact ho_clamped v u hvu huS

end NumberTheoryLean.WeightGlobalBounds

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_InvariantFiniteness
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace Erdos970Dependency.InvariantDensities
open NumberTheoryLean NumberTheoryLean.BuchstabBridge NumberTheoryLean.DerivativeWeights
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathGeometry

theorem oddFactor_bounds {s : ℝ} (hs : 1 ≤ s) : 0 ≤ oddFactor s ∧ oddFactor s ≤ 1 := by
  have hs0 : 0 < s := by linarith
  have hsq : 1 ≤ s ^ 2 := by nlinarith
  have hinv : 1 / s ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hs0)).mpr hsq
  have hnonneg : 0 ≤ 1 / s ^ 2 := by positivity
  unfold oddFactor
  constructor <;> linarith

theorem oddFactor_measurable : Measurable oddFactor := by
  unfold oddFactor
  fun_prop

theorem evenDensity_measurable : Measurable evenDensity :=
  phiEven_measurable.indicator measurableSet_Ici

theorem oddDensity_measurable : Measurable oddDensity :=
  (oddFactor_measurable.mul phiOdd_continuous.measurable).indicator measurableSet_Ici

end Erdos970Dependency.InvariantDensities

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_DensityConservation
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.DensityConservation

theorem kernel_density_conservation (K : Kernel ℝ ℝ) (d e : ℝ → ℝ) (k : ℝ → ℝ → ℝ)
    (hd : Measurable d) (hd0 : ∀ s, 0 ≤ d s)
    (hprod : Measurable (fun z : ℝ × ℝ ↦ d z.1 * k z.1 z.2))
    (hkernel : ∀ s (B : Set ℝ), MeasurableSet B → K s B = ∫⁻ t in B, ENNReal.ofReal (k s t))
    (hint : ∀ t, Integrable (fun s ↦ d s * k s t))
    (hpos : ∀ s t, 0 ≤ d s * k s t)
    (hconserve : ∀ t, (∫ s, d s * k s t) = e t) :
    K ∘ₘ (volume.withDensity (fun s ↦ ENNReal.ofReal (d s))) =
      volume.withDensity (fun t ↦ ENNReal.ofReal (e t)) := by
  apply Measure.ext
  intro B hB
  rw [Measure.bind_apply hB K.aemeasurable]
  have hdensity := lintegral_withDensity_eq_lintegral_mul volume (ENNReal.measurable_ofReal.comp hd)
    (K.measurable_coe hB)
  simp only [Function.comp_def, Pi.mul_apply] at hdensity
  rw [hdensity]
  simp_rw [hkernel _ _ hB]
  have hrewrite (s : ℝ) : ENNReal.ofReal (d s) * (∫⁻ t in B, ENNReal.ofReal (k s t)) =
      ∫⁻ t in B, ENNReal.ofReal (d s * k s t) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro t
    exact (ENNReal.ofReal_mul (hd0 s)).symm
  simp_rw [hrewrite]
  have hm : Measurable (Function.uncurry (fun s t : ℝ ↦ ENNReal.ofReal (d s * k s t))) := by
    change Measurable (fun z : ℝ × ℝ ↦ ENNReal.ofReal (d z.1 * k z.1 z.2))
    simpa only [Function.comp_def] using ENNReal.measurable_ofReal.comp hprod
  rw [lintegral_lintegral_swap (μ := volume) (ν := volume.restrict B) hm.aemeasurable]
  simp_rw [← ofReal_integral_eq_lintegral_ofReal (hint _) (Eventually.of_forall (fun s ↦ hpos s _)),
    hconserve]
  exact (withDensity_apply _ hB).symm

end Erdos970Dependency.DensityConservation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_StateKernelInvariance
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedPairKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.RegenerativeOddOccupation.ratioVisits_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.costCaptured_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.costKilled_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.costKilled_pow_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.firstReturn_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.returnLaw_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleConvolutionLaw.returnLaw_pow_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleOccupation.pairSampling_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleRegeneration.cycleJointLaw_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.InitialRegeneration.hitOrReturn_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedCostKernel_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedDraws_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedHitting.pairedKilled_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedHitting.pairedKilled_pow_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedHitting.pairedOdd_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.StateKernelInvariance
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathMeasures NumberTheoryLean.KernelDensityBridge
open Erdos970Dependency.InvariantFiniteness Erdos970Dependency.OrdinaryKernelInvariance

theorem comp_map_input {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (K : Kernel β γ) (mu : Measure α) (f : α → β) (hf : Measurable f) :
    K ∘ₘ mu.map f = K.comap f hf ∘ₘ mu := by
  ext B hB
  rw [Measure.bind_apply hB K.aemeasurable, lintegral_map (K.measurable_coe hB) hf,
    Measure.bind_apply hB (K.comap f hf).aemeasurable]
  rfl

theorem oddLift_ratio (s : OddState) : oddLift s.1 = s := by
  apply Subtype.ext
  exact max_eq_right s.2

theorem evenLift_ratio (s : EvenState) : evenLift s.1 = s := by
  apply Subtype.ext
  exact max_eq_right s.2

theorem evenKernel_map_lift (s : EvenState) : (evenKernel s).map oddLift = evenToOdd s := by
  rw [← evenToOdd_map_ratio s, Measure.map_map oddLift_measurable measurable_subtype_coe]
  rw [show oddLift ∘ (Subtype.val : OddState → ℝ) = id from funext oddLift_ratio, Measure.map_id]

theorem oddKernel_map_lift (s : OddState) : (oddKernel s).map evenLift = oddToEven s := by
  rw [← oddToEven_map_ratio s, Measure.map_map evenLift_measurable measurable_subtype_coe]
  rw [show evenLift ∘ (Subtype.val : EvenState → ℝ) = id from funext evenLift_ratio, Measure.map_id]

end Erdos970Dependency.StateKernelInvariance

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_DensityComparison
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedPairKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.RegenerativeOddOccupation.ratioVisits_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.costCaptured_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.costKilled_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.costKilled_pow_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.firstReturn_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostReturnLaw.returnLaw_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleConvolutionLaw.returnLaw_pow_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleOccupation.pairSampling_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.CycleRegeneration.cycleJointLaw_isProbabilityMeasure _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.InitialRegeneration.hitOrReturn_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedCostKernel_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedDraws_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedHitting.pairedKilled_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedHitting.pairedKilled_pow_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedHitting.pairedOdd_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.NumberTheoryLean.ReferenceBenchmarkDecay.benchmark_even_below_two
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory
namespace Erdos970Dependency.InitialDensityFormulas
open NumberTheoryLean NumberTheoryLean.BuchstabBridge NumberTheoryLean.DerivativeWeights
open NumberTheoryLean.WeightFutureIntegrals NumberTheoryLean.TransitionKernels
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.RegenerationTails NumberTheoryLean.TwoStepDensityBounds
open Erdos970Dependency.WeightIntegrals Erdos970Dependency.OrdinaryKernelInvariance

theorem regTwoDensity_measurable : Measurable regTwoDensity :=
  (((W_measurable.mul phiOdd_continuous.measurable).div_const sieveA).mul tailW_measurable).indicator measurableSet_Ici

theorem regTwoDensity_nonneg (u : ℝ) : 0 ≤ regTwoDensity u := by
  by_cases hu : 1 ≤ u
  · rw [regTwoDensity, indicator_of_mem (show u ∈ Ici (1 : ℝ) from hu)]
    exact mul_nonneg (div_nonneg (mul_nonneg (W_pos (by linarith)).le (phiOdd_pos u).le) sieveA_pos.le)
      (tailW_nonneg hu)
  · rw [regTwoDensity, indicator_of_notMem (show u ∉ Ici (1 : ℝ) from hu)]

theorem initialIncoming_formula (s : EvenState) {t : ℝ} (ht : 2 ≤ t) (u : ℝ) :
    initialIncoming s t u = (Icc (s.1 - 1) (t + 1)).indicator
      (fun u ↦ (W t * phiEven t / phiEven s.1) * W u) u := by
  classical
  by_cases hu : s.1 - 1 ≤ u
  · have hlift : (oddLift u).1 = u := max_eq_right (by linarith [s.2])
    by_cases hut : u ≤ t + 1
    · rw [initialIncoming, hlift, indicator_of_mem (show u ∈ Icc (s.1 - 1) (t + 1) from ⟨hu, hut⟩)]
      change transitionDensity .even s.1 u * transitionDensity .odd u t = _
      have htwo := two_step_density_eq (i := .even) (s := s.1) (t := u) (u := t) s.2 hu
        (show max 2 (u - 1) ≤ t from max_le ht (by linarith))
      simp only [Side.flip, weight] at htwo
      exact htwo.trans (by ring)
    · have hn : t ∉ Ici (max 2 (u - 1)) := by
        intro h
        have := le_trans (le_max_right (2 : ℝ) (u - 1)) h
        linarith
      rw [initialIncoming, hlift, transitionDensity, minRatio, weight, Side.flip, weight,
        TransitionKernels.tailDensity, indicator_of_notMem hn, mul_zero,
        indicator_of_notMem (show u ∉ Icc (s.1 - 1) (t + 1) from fun h ↦ hut h.2)]
  · rw [initialIncoming, TransitionKernels.evenDensity, TransitionKernels.tailDensity,
      indicator_of_notMem (show u ∉ Ici (s.1 - 1) from hu), zero_mul,
      indicator_of_notMem (show u ∉ Icc (s.1 - 1) (t + 1) from fun h ↦ hu h.1)]

theorem initialIncoming_zero (s : EvenState) {t : ℝ} (ht : t < 2) (u : ℝ) : initialIncoming s t u = 0 := by
  unfold initialIncoming transitionDensity
  simp only [minRatio, weight, Side.flip, TransitionKernels.tailDensity]
  rw [indicator_of_notMem (show t ∉ Ici (max 2 ((oddLift u).1 - 1)) from fun h ↦
    (not_le_of_gt ht) (le_trans (le_max_left _ _) h)), mul_zero]

theorem regTwoIncoming_formula (u y : ℝ) :
    regTwoIncoming u y = (Icc (2 : ℝ) (u + 1)).indicator
      (fun y ↦ (W u * phiOdd u / sieveA) * W y) y := by
  classical
  have hmin : max 2 (regenerationState.1 - 1) = 2 := by norm_num [regenerationState]
  by_cases hy : 2 ≤ y
  · have hlift : (evenLift y).1 = y := max_eq_right (by linarith)
    by_cases hyu : y ≤ u + 1
    · rw [regTwoIncoming, hlift, indicator_of_mem (show y ∈ Icc (2 : ℝ) (u + 1) from ⟨hy, hyu⟩)]
      change transitionDensity .odd regenerationState.1 y * transitionDensity .even y u = _
      have htwo := two_step_density_eq (i := .odd) (s := regenerationState.1) (t := y) (u := u)
        regenerationState.2 (by simpa only [minRatio, hmin] using hy) (by change y - 1 ≤ u; linarith)
      simp only [Side.flip, weight] at htwo
      rw [phiOdd_initial (s := regenerationState.1) (by norm_num [regenerationState])] at htwo
      exact htwo.trans (by ring)
    · rw [regTwoIncoming, hlift, transitionDensity, minRatio, weight, Side.flip, weight,
        TransitionKernels.tailDensity,
        indicator_of_notMem (show u ∉ Ici (y - 1) by change ¬y - 1 ≤ u; linarith), mul_zero,
        indicator_of_notMem (show y ∉ Icc (2 : ℝ) (u + 1) from fun h ↦ hyu h.2)]
  · rw [regTwoIncoming, TransitionKernels.oddDensity, TransitionKernels.tailDensity, hmin,
      indicator_of_notMem (show y ∉ Ici (2 : ℝ) from hy), zero_mul,
      indicator_of_notMem (show y ∉ Icc (2 : ℝ) (u + 1) from fun h ↦ hy h.1)]

theorem regTwoIncoming_zero {u : ℝ} (hu : u < 1) (y : ℝ) : regTwoIncoming u y = 0 := by
  have hmin : max 2 (regenerationState.1 - 1) = 2 := by norm_num [regenerationState]
  by_cases hy : 2 ≤ y
  · have hlift : (evenLift y).1 = y := max_eq_right (by linarith)
    rw [regTwoIncoming, hlift, transitionDensity, minRatio, weight, Side.flip, weight,
      TransitionKernels.tailDensity,
      indicator_of_notMem (show u ∉ Ici (y - 1) by change ¬y - 1 ≤ u; linarith), mul_zero]
  · rw [regTwoIncoming, TransitionKernels.oddDensity, TransitionKernels.tailDensity, hmin,
      indicator_of_notMem (show y ∉ Ici (2 : ℝ) from hy), zero_mul]

theorem regThreeIncoming_formula {t : ℝ} (ht : 2 ≤ t) (u : ℝ) :
    regThreeIncoming t u = (Icc (1 : ℝ) (t + 1)).indicator
      (fun u ↦ (W t * phiEven t / sieveA) * (W u * tailW u)) u := by
  classical
  by_cases hu : 1 ≤ u
  · have hlift : (oddLift u).1 = u := max_eq_right (by linarith)
    by_cases hut : u ≤ t + 1
    · rw [regThreeIncoming, regTwoDensity, indicator_of_mem (show u ∈ Ici (1 : ℝ) from hu), hlift,
        transitionDensity, minRatio, weight, Side.flip, weight, TransitionKernels.tailDensity,
        indicator_of_mem (show t ∈ Ici (max 2 (u - 1)) from max_le ht (by linarith)),
        indicator_of_mem (show u ∈ Icc (1 : ℝ) (t + 1) from ⟨hu, hut⟩)]
      field_simp [(phiOdd_pos u).ne', sieveA_pos.ne']
    · have hn : t ∉ Ici (max 2 (u - 1)) := by
        intro h
        have := le_trans (le_max_right (2 : ℝ) (u - 1)) h
        linarith
      rw [regThreeIncoming, hlift, transitionDensity, minRatio, weight, Side.flip, weight,
        TransitionKernels.tailDensity, indicator_of_notMem hn, mul_zero,
        indicator_of_notMem (show u ∉ Icc (1 : ℝ) (t + 1) from fun h ↦ hut h.2)]
  · rw [regThreeIncoming, regTwoDensity, indicator_of_notMem (show u ∉ Ici (1 : ℝ) from hu), zero_mul,
      indicator_of_notMem (show u ∉ Icc (1 : ℝ) (t + 1) from fun h ↦ hu h.1)]

theorem regThreeIncoming_zero {t : ℝ} (ht : t < 2) (u : ℝ) : regThreeIncoming t u = 0 := by
  unfold regThreeIncoming transitionDensity
  simp only [minRatio, weight, Side.flip, TransitionKernels.tailDensity]
  rw [indicator_of_notMem (show t ∉ Ici (max 2 ((oddLift u).1 - 1)) from fun h ↦
    (not_le_of_gt ht) (le_trans (le_max_left _ _) h)), mul_zero]

end Erdos970Dependency.InitialDensityFormulas

end

section

open Set MeasureTheory
namespace Erdos970Dependency.CompactIncomingIntegrals
open NumberTheoryLean.DerivativeWeights NumberTheoryLean.TransitionKernels
open Erdos970Dependency.WeightIntegrals Erdos970Dependency.InitialDensityFormulas

theorem initialIncoming_integrable (s : EvenState) (t : ℝ) : Integrable (initialIncoming s t) := by
  by_cases ht : 2 ≤ t
  · rw [show initialIncoming s t = (Icc (s.1 - 1) (t + 1)).indicator
      (fun u ↦ (W t * phiEven t / phiEven s.1) * W u) from funext (initialIncoming_formula s ht)]
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    apply ContinuousOn.integrableOn_Icc
    intro u hu
    have hu0 : 0 < u := by linarith [s.2, hu.1]
    exact (continuousAt_const.mul (W_continuousAt (ne_of_gt hu0))).continuousWithinAt
  · rw [show initialIncoming s t = 0 from funext (initialIncoming_zero s (lt_of_not_ge ht))]
    exact integrable_zero _ _ _

theorem regTwoIncoming_integrable (u : ℝ) : Integrable (regTwoIncoming u) := by
  by_cases hu : 1 ≤ u
  · rw [show regTwoIncoming u = (Icc (2 : ℝ) (u + 1)).indicator
      (fun y ↦ (W u * phiOdd u / NumberTheoryLean.BuchstabBridge.sieveA) * W y)
      from funext (regTwoIncoming_formula u)]
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    apply ContinuousOn.integrableOn_Icc
    intro y hy
    exact (continuousAt_const.mul (W_continuousAt (by linarith [hy.1]))).continuousWithinAt
  · rw [show regTwoIncoming u = 0 from funext (regTwoIncoming_zero (lt_of_not_ge hu))]
    exact integrable_zero _ _ _

theorem regThreeIncoming_integrable (t : ℝ) : Integrable (regThreeIncoming t) := by
  by_cases ht : 2 ≤ t
  · rw [show regThreeIncoming t = (Icc (1 : ℝ) (t + 1)).indicator
      (fun u ↦ (W t * phiEven t / NumberTheoryLean.BuchstabBridge.sieveA) * (W u * tailW u))
      from funext (regThreeIncoming_formula ht)]
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact ((regKernel_continuousOn (b := t + 1) (by norm_num : (0 : ℝ) < 1)).const_mul _).integrableOn_Icc
  · rw [show regThreeIncoming t = 0 from funext (regThreeIncoming_zero (lt_of_not_ge ht))]
    exact integrable_zero _ _ _

theorem initialIncoming_integral (s : EvenState) (hsup : s.1 ≤ 23 / 10) (t : ℝ) :
    (∫ u, initialIncoming s t u) = initialTwoDensity s t := by
  by_cases ht : 2 ≤ t
  · simp_rw [initialIncoming_formula s ht]
    rw [integral_indicator measurableSet_Icc, integral_const_mul, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show s.1 - 1 ≤ t + 1 by linarith),
      initialTwoDensity, indicator_of_mem (show t ∈ Ici (2 : ℝ) from ht)]
    rfl
  · simp only [initialIncoming_zero s (lt_of_not_ge ht), integral_zero]
    rw [initialTwoDensity, indicator_of_notMem (show t ∉ Ici (2 : ℝ) from ht)]

theorem regTwoIncoming_integral (u : ℝ) : (∫ y, regTwoIncoming u y) = regTwoDensity u := by
  by_cases hu : 1 ≤ u
  · simp_rw [regTwoIncoming_formula]
    rw [integral_indicator measurableSet_Icc, integral_const_mul, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show (2 : ℝ) ≤ u + 1 by linarith),
      regTwoDensity, indicator_of_mem (show u ∈ Ici (1 : ℝ) from hu), tailW_eq_mass hu]
    rfl
  · simp only [regTwoIncoming_zero (lt_of_not_ge hu), integral_zero]
    rw [regTwoDensity, indicator_of_notMem (show u ∉ Ici (1 : ℝ) from hu)]

theorem regThreeIncoming_integral (t : ℝ) : (∫ u, regThreeIncoming t u) = regThreeDensity t := by
  by_cases ht : 2 ≤ t
  · simp_rw [regThreeIncoming_formula ht]
    rw [integral_indicator measurableSet_Icc, integral_const_mul, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show (1 : ℝ) ≤ t + 1 by linarith),
      regThreeDensity, indicator_of_mem (show t ∈ Ici (2 : ℝ) from ht)]
    rfl
  · simp only [regThreeIncoming_zero (lt_of_not_ge ht), integral_zero]
    rw [regThreeDensity, indicator_of_notMem (show t ∉ Ici (2 : ℝ) from ht)]

end Erdos970Dependency.CompactIncomingIntegrals

end

section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.MarginalDensityMeasures
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.KernelDensityBridge NumberTheoryLean.RegenerationTails
open Erdos970Dependency.OrdinaryKernelInvariance Erdos970Dependency.DensityConservation
open Erdos970Dependency.InitialDensityFormulas Erdos970Dependency.CompactIncomingIntegrals

theorem even_input_measurable (s : EvenState) : Measurable (evenDensity s) :=
  evenDensity_measurable.comp (measurable_const.prodMk measurable_id)

theorem odd_input_measurable (s : OddState) : Measurable (oddDensity s) :=
  oddDensity_measurable.comp (measurable_const.prodMk measurable_id)

theorem evenKernel_eq_density (s : EvenState) :
    evenKernel s = volume.withDensity (fun u ↦ ENNReal.ofReal (evenDensity s u)) := by
  ext B hB
  rw [evenKernel_apply, withDensity_apply _ hB]

theorem oddKernel_eq_density (s : OddState) :
    oddKernel s = volume.withDensity (fun u ↦ ENNReal.ofReal (oddDensity s u)) := by
  ext B hB
  rw [oddKernel_apply, withDensity_apply _ hB]

theorem odd_lifted_density_measurable :
    Measurable (fun z : ℝ × ℝ ↦ transitionDensity .odd (oddLift z.1).1 z.2) :=
  (transitionDensity_joint_measurable .odd).comp
    (((measurable_subtype_coe.comp oddLift_measurable).comp measurable_fst).prodMk measurable_snd)

theorem even_lifted_density_measurable :
    Measurable (fun z : ℝ × ℝ ↦ transitionDensity .even (evenLift z.1).1 z.2) :=
  (transitionDensity_joint_measurable .even).comp
    (((measurable_subtype_coe.comp evenLift_measurable).comp measurable_fst).prodMk measurable_snd)

theorem initialTwoMeasure_eq_density (s : EvenState) (hsup : s.1 ≤ 23 / 10) :
    initialTwoMeasure s = volume.withDensity (fun t ↦ ENNReal.ofReal (initialTwoDensity s t)) := by
  rw [initialTwoMeasure, evenKernel_eq_density]
  apply kernel_density_conservation oddRealKernel (evenDensity s) (initialTwoDensity s)
    (fun u t ↦ transitionDensity .odd (oddLift u).1 t) (even_input_measurable s) (evenDensity_nonneg s)
  · exact ((even_input_measurable s).comp measurable_fst).mul odd_lifted_density_measurable
  · intro u B _
    exact oddKernel_apply (oddLift u) B
  · intro t
    exact initialIncoming_integrable s t
  · intro u t
    exact mul_nonneg (evenDensity_nonneg s u) (oddDensity_nonneg (oddLift u) t)
  · intro t
    exact initialIncoming_integral s hsup t

theorem regTwoMeasure_eq_density :
    regTwoMeasure = volume.withDensity (fun u ↦ ENNReal.ofReal (regTwoDensity u)) := by
  rw [regTwoMeasure, oddKernel_eq_density]
  apply kernel_density_conservation evenRealKernel (oddDensity regenerationState) regTwoDensity
    (fun y u ↦ transitionDensity .even (evenLift y).1 u)
    (odd_input_measurable regenerationState) (oddDensity_nonneg regenerationState)
  · exact ((odd_input_measurable regenerationState).comp measurable_fst).mul even_lifted_density_measurable
  · intro y B _
    exact evenKernel_apply (evenLift y) B
  · intro u
    exact regTwoIncoming_integrable u
  · intro y u
    exact mul_nonneg (oddDensity_nonneg regenerationState y) (evenDensity_nonneg (evenLift y) u)
  · intro u
    exact regTwoIncoming_integral u

theorem regThreeMeasure_eq_density :
    regThreeMeasure = volume.withDensity (fun t ↦ ENNReal.ofReal (regThreeDensity t)) := by
  rw [regThreeMeasure, regTwoMeasure_eq_density]
  apply kernel_density_conservation oddRealKernel regTwoDensity regThreeDensity
    (fun u t ↦ transitionDensity .odd (oddLift u).1 t) regTwoDensity_measurable regTwoDensity_nonneg
  · exact (regTwoDensity_measurable.comp measurable_fst).mul odd_lifted_density_measurable
  · intro u B _
    exact oddKernel_apply (oddLift u) B
  · intro t
    exact regThreeIncoming_integrable t
  · intro u t
    exact mul_nonneg (regTwoDensity_nonneg u) (oddDensity_nonneg (oddLift u) t)
  · intro t
    exact regThreeIncoming_integral t

end Erdos970Dependency.MarginalDensityMeasures

end

section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.DensityComparison
open NumberTheoryLean.BuchstabBridge NumberTheoryLean.DerivativeWeights NumberTheoryLean.WeightFutureIntegrals
open NumberTheoryLean.TransitionKernels
open Erdos970Dependency.WeightIntegrals Erdos970Dependency.InitialDensityFormulas
open Erdos970Dependency.MarginalDensityMeasures

theorem dominationConstant_pos : 0 < dominationConstant :=
  div_pos (mul_pos (by norm_num) sieveA_pos) (phiEven_pos (by norm_num))

theorem initial_density_le (s : EvenState) (hs : 199 / 100 ≤ s.1) (hsup : s.1 ≤ 23 / 10) (t : ℝ) :
    initialTwoDensity s t ≤ dominationConstant * regThreeDensity t := by
  by_cases ht : 2 ≤ t
  · rw [initialTwoDensity, regThreeDensity,
      indicator_of_mem (show t ∈ Ici (2 : ℝ) from ht), indicator_of_mem (show t ∈ Ici (2 : ℝ) from ht)]
    have hnum : 0 < W t * phiEven t := mul_pos (W_pos (by linarith)) (phiEven_pos (by linarith))
    have hden : 0 < phiEven s.1 := phiEven_pos (by linarith)
    have hmin : 0 < phiEven (23 / 10) := phiEven_pos (by norm_num)
    have hdenle : phiEven (23 / 10) ≤ phiEven s.1 :=
      phiEven_strictAntiOn.antitoneOn (by linarith : 1 < s.1) (by norm_num) hsup
    calc
      _ ≤ (W t * phiEven t / phiEven s.1) * (48 * regIntegral t) :=
        mul_le_mul_of_nonneg_left (initial_integral_le hs hsup ht) (div_pos hnum hden).le
      _ ≤ (W t * phiEven t / phiEven (23 / 10)) * (48 * regIntegral t) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hnum.le hmin hdenle)
          (mul_nonneg (by norm_num) (regIntegral_nonneg ht))
      _ = dominationConstant * ((W t * phiEven t / sieveA) * regIntegral t) := by
        unfold dominationConstant
        field_simp [sieveA_pos.ne', hmin.ne']
  · rw [initialTwoDensity, regThreeDensity,
      indicator_of_notMem (show t ∉ Ici (2 : ℝ) from ht),
      indicator_of_notMem (show t ∉ Ici (2 : ℝ) from ht), mul_zero]

theorem initial_real_measure_le (s : EvenState) (hs : 199 / 100 ≤ s.1) (hsup : s.1 ≤ 23 / 10) :
    initialTwoMeasure s ≤ ENNReal.ofReal dominationConstant • regThreeMeasure := by
  rw [initialTwoMeasure_eq_density s hsup, regThreeMeasure_eq_density,
    ← withDensity_smul' (ENNReal.ofReal dominationConstant) (fun t ↦ ENNReal.ofReal (regThreeDensity t)) ENNReal.ofReal_ne_top]
  apply withDensity_mono
  apply Filter.Eventually.of_forall
  intro t
  change ENNReal.ofReal (initialTwoDensity s t) ≤ ENNReal.ofReal dominationConstant * ENNReal.ofReal (regThreeDensity t)
  rw [← ENNReal.ofReal_mul dominationConstant_pos.le]
  exact ENNReal.ofReal_le_ofReal (initial_density_le s hs hsup t)

end Erdos970Dependency.DensityComparison

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_KernelPotential
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.KernelPotential

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

theorem compose_mono_left {B C : Kernel α β} (h : B ≤ C) (K : Kernel γ α) :
    B ∘ₖ K ≤ C ∘ₖ K := by
  intro a
  apply Measure.le_iff.mpr
  intro s hs
  rw [Kernel.comp_apply' _ _ _ hs, Kernel.comp_apply' _ _ _ hs]
  exact lintegral_mono (fun x => h x s)

theorem power_comp_succ (B : Kernel α β) (K : Kernel α α) (n : ℕ) :
    B ∘ₖ (K ^ (n + 1)) = (B ∘ₖ (K ^ n)) ∘ₖ K := by
  rw [pow_succ]
  exact (Kernel.comp_assoc B (K ^ n) K).symm

theorem potential_unfold (B : Kernel α β) (K : Kernel α α) :
    potential B K = B + (potential B K) ∘ₖ K := by
  unfold potential
  rw [Kernel.comp_sum_left]
  ext a s hs
  rw [Kernel.sum_apply' _ _ hs, add_apply, Measure.add_apply, Kernel.sum_apply' _ _ hs,
    tsum_eq_zero_add' ENNReal.summable]
  have hz : B ∘ₖ (K ^ 0) = B := Kernel.comp_id B
  simp only [hz, power_comp_succ]

end NumberTheoryLean.KernelPotential

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_OccupationAge
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.CycleConvolutionLaw.returnLaw_pow_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.InitialRegeneration.hitOrReturn_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.CycleCostMoments

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess CostReturnLaw
open MarkedCycleLaw CycleDurationMoments

theorem draw_cost_le_log_three {s : ℝ} (hs : 1 / 2 ≤ s) : cost s ≤ Real.log 3 := by
  have hs0 : 0 < s := by linarith
  have hi : 1 / s ≤ 2 := (div_le_iff₀ hs0).mpr (by linarith)
  unfold cost
  exact Real.log_le_log (by positivity) (by linarith)

end NumberTheoryLean.CycleCostMoments

end

section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.ActualCycleOccupation
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathGeometry NumberTheoryLean.FinitePathMeasures
open NumberTheoryLean.PairedHitting NumberTheoryLean.PairedCostProcess NumberTheoryLean.PairedCostGrouping
open NumberTheoryLean.CostReturnLaw NumberTheoryLean.CycleOccupation NumberTheoryLean.KernelPotential
open Erdos970Dependency.InvariantDensities Erdos970Dependency.StateKernelInvariance
open Erdos970Dependency.RegenerativeOddOccupation

theorem costKernel_map_state (z : CostState) : (costKernel z).map Prod.fst = stateKernel z.1 := by
  have hm : Measurable (fun s : State ↦ (s, z.2 + cost (stateRatio s))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  rw [costKernel_eq_map, Measure.map_map measurable_fst hm]
  change (stateKernel z.1).map id = stateKernel z.1
  exact Measure.map_id

end Erdos970Dependency.ActualCycleOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_UniformCycleMoments
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.InitialRegeneration.hitOrReturn_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.OccupationBoundaries

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures KernelDensityBridge
open PairedCostProcess CostReturnLaw CycleOccupation

 theorem stateRatio_pos (s : State) : 0 < stateRatio s := by
  cases s with
  | inl s => change 0 < s.1; linarith [s.2]
  | inr s => change 0 < s.1; linarith [s.2]

theorem cost_add_log {t : ℝ} (ht : 0 < t) : cost t + Real.log t = Real.log (t + 1) := by
  rw [cost, ← Real.log_mul (by positivity : (1 + 1 / t : ℝ) ≠ 0) ht.ne']
  congr 1
  field_simp

end NumberTheoryLean.OccupationBoundaries



namespace NumberTheoryLean.OccupationRegeneration

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess PairedCostGrouping
open RegenerationTails CostReturnLaw CycleRegeneration CycleOccupation
open OccupationDecomposition CycleResponse CycleConvolutionLaw

theorem costKernel_translation (z : CostState) (a : ℝ) :
    (costKernel z).map (shiftFullCost a) = costKernel (shiftFullCost a z) := by
  ext B hB
  rw [Measure.map_apply (shiftFullCost_measurable a) hB,
    costKernel_apply _ ((shiftFullCost_measurable a) hB), costKernel_apply _ hB]
  congr 1
  ext s
  change (s, (z.2 + cost (stateRatio s)) + a) ∈ B ↔
    (s, (z.2 + a) + cost (stateRatio s)) ∈ B
  rw [show z.2 + cost (stateRatio s) + a = z.2 + a + cost (stateRatio s) by ring]

theorem shiftFull_commutes (a : ℝ) : Commute (shiftFullKernel a) costKernel := by
  change shiftFullKernel a ∘ₖ costKernel = costKernel ∘ₖ shiftFullKernel a
  rw [shiftFullKernel, Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
  ext z : 1
  rw [Kernel.map_apply _ (shiftFullCost_measurable a), Kernel.comap_apply]
  exact costKernel_translation z a

end NumberTheoryLean.OccupationRegeneration



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_RegenerationBandBounds
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.InitialOccupation

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathMeasures PairedCostProcess PairedCostGrouping
open CostReturnLaw CycleOccupation OccupationDecomposition KernelPotential
open InitialOddDraw InitialRegeneration

theorem fullOccupation_eq_potential : fullOccupation = potential costKernel costKernel := by
  unfold fullOccupation potential
  apply congrArg Kernel.sum
  funext n
  exact pow_succ' costKernel n

theorem fullOccupation_unfold : fullOccupation = costKernel + fullOccupation ∘ₖ costKernel := by
  rw [fullOccupation_eq_potential]
  exact potential_unfold _ _

end NumberTheoryLean.InitialOccupation

end

section

namespace NumberTheoryLean.FullOccupationCovariance

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open TransitionKernels FinitePathMeasures PairedCostProcess PairedCostGrouping
open RegenerationTails CostReturnLaw CycleResponse AdmissibleCycleTests
open OccupationDecomposition OccupationRegeneration InitialOccupation

instance fullOccupation_isSFiniteKernel : IsSFiniteKernel fullOccupation := by
  rw [fullOccupation_eq_potential]
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem shifts_commute_fullOccupation (a : ℝ) :
    shiftFullKernel a ∘ₖ fullOccupation = fullOccupation ∘ₖ shiftFullKernel a := by
  rw [fullOccupation, Kernel.comp_sum_right, Kernel.comp_sum_left]
  apply congrArg Kernel.sum
  funext n
  exact ((shiftFull_commutes a).pow_right (n + 1)).eq

theorem fullOccupation_translation (z : CostState) (a : ℝ) :
    (fullOccupation z).map (shiftFullCost a) = fullOccupation (shiftFullCost a z) := by
  have h := shifts_commute_fullOccupation a
  rw [shiftFullKernel, Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap] at h
  have hz := congrArg (fun K : Kernel CostState CostState => K z) h
  rwa [Kernel.map_apply _ (shiftFullCost_measurable a), Kernel.comap_apply] at hz

end NumberTheoryLean.FullOccupationCovariance

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_CostPrefixTransport
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.CostPrefixTransport

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostGrouping
open OccupationBoundaries CycleCostMoments OccupationDecomposition OccupationRegeneration
open InitialOccupation FullOccupationCovariance KernelPotential

theorem projection_intertwines : stateProjection ∘ₖ costKernel = stateKernel ∘ₖ stateProjection := by
  rw [stateProjection, Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
  ext z : 1
  rw [Kernel.map_apply _ measurable_fst, Kernel.comap_apply]
  exact Erdos970Dependency.ActualCycleOccupation.costKernel_map_state z

theorem projection_intertwines_pow (n : ℕ) :
    stateProjection ∘ₖ (costKernel ^ n) = (stateKernel ^ n) ∘ₖ stateProjection := by
  induction n with
  | zero =>
    change stateProjection ∘ₖ (Kernel.id : Kernel CostState CostState) = Kernel.id ∘ₖ stateProjection
    rw [Kernel.comp_id, Kernel.id_comp]
  | succ n ih =>
    have hp : costKernel ^ (n + 1) = (costKernel ^ n) ∘ₖ costKernel := pow_succ _ _
    have hq : stateKernel ^ (n + 1) = (stateKernel ^ n) ∘ₖ stateKernel := pow_succ _ _
    rw [hp, hq, ← Kernel.comp_assoc, ih, Kernel.comp_assoc, projection_intertwines, ← Kernel.comp_assoc]

theorem costKernel_pow_map_state (n : ℕ) (z : CostState) :
    ((costKernel ^ n) z).map Prod.fst = (stateKernel ^ n) z.1 := by
  have h := projection_intertwines_pow n
  rw [stateProjection, Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap] at h
  have hz := congrArg (fun K : Kernel CostState State => K z) h
  rwa [Kernel.map_apply _ measurable_fst, Kernel.comap_apply] at hz

theorem stateRatio_ge_half (s : State) : (1 / 2 : ℝ) ≤ stateRatio s := by
  cases s with
  | inl s => change (1 / 2 : ℝ) ≤ s.1; linarith [s.2]
  | inr s => change (1 / 2 : ℝ) ≤ s.1; linarith [s.2]

theorem costKernel_cost_bounds (z : CostState) :
    ∀ᵐ y ∂costKernel z, z.2 ≤ y.2 ∧ y.2 ≤ z.2 + Real.log 3 := by
  have hm : Measurable (fun s : State => (s, z.2 + cost (stateRatio s))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  rw [costKernel_eq_map]
  apply (ae_map_iff hm.aemeasurable
    ((measurableSet_le measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_const))).mpr
  apply Eventually.of_forall
  intro s
  have hp := cost_pos (stateRatio_pos s)
  have hu := draw_cost_le_log_three (stateRatio_ge_half s)
  change z.2 ≤ z.2 + cost (stateRatio s) ∧ z.2 + cost (stateRatio s) ≤ z.2 + Real.log 3
  constructor <;> linarith

theorem costKernel_pow_cost_bounds (n : ℕ) (z : CostState) :
    ∀ᵐ y ∂(costKernel ^ n) z, z.2 ≤ y.2 ∧ y.2 ≤ z.2 + (n : ℝ) * Real.log 3 := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero]
    change ∀ᵐ y ∂Measure.dirac z, z.2 ≤ y.2 ∧ y.2 ≤ z.2 + (0 : ℝ) * Real.log 3
    have hpred : MeasurableSet {y : CostState | z.2 ≤ y.2 ∧ y.2 ≤ z.2 + (0 : ℝ) * Real.log 3} :=
      (measurableSet_le measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_const)
    exact (ae_dirac_iff (p := fun y : CostState => z.2 ≤ y.2 ∧ y.2 ≤ z.2 + (0 : ℝ) * Real.log 3) hpred).mpr
      ⟨le_rfl, by simp⟩
  | succ n ih =>
    have hp : costKernel ^ (n + 1) = costKernel ∘ₖ (costKernel ^ n) := pow_succ' _ _
    rw [hp]
    apply Kernel.ae_comp_of_ae_ae
      ((measurableSet_le measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_const))
    filter_upwards [ih] with y hy
    filter_upwards [costKernel_cost_bounds y] with w hw
    refine ⟨le_trans hy.1 hw.1, ?_⟩
    calc
      w.2 ≤ y.2 + Real.log 3 := hw.2
      _ ≤ (z.2 + (n : ℝ) * Real.log 3) + Real.log 3 := add_le_add hy.2 le_rfl
      _ = _ := by push_cast <;> ring

instance inclusiveOccupation_isSFiniteKernel : IsSFiniteKernel inclusiveOccupation := by
  unfold inclusiveOccupation
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem inclusiveOccupation_translation (z : CostState) (a : ℝ) :
    (inclusiveOccupation z).map (shiftFullCost a) = inclusiveOccupation (shiftFullCost a z) := by
  rw [inclusiveOccupation, _root_.add_apply, Measure.map_add _ _ (shiftFullCost_measurable a),
    Kernel.id_apply, Measure.map_dirac' (shiftFullCost_measurable a), fullOccupation_translation,
    _root_.add_apply, Kernel.id_apply]

theorem inclusive_comp_step : inclusiveOccupation ∘ₖ costKernel = fullOccupation := by
  rw [inclusiveOccupation, Kernel.comp_add_left, Kernel.id_comp]
  exact fullOccupation_unfold.symm

instance prefixOccupation_isSFiniteKernel (n : ℕ) : IsSFiniteKernel (prefixOccupation n) := by
  unfold prefixOccupation
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem full_comp_step_le : fullOccupation ∘ₖ costKernel ≤ fullOccupation := by
  calc
    _ ≤ costKernel + fullOccupation ∘ₖ costKernel := le_add_of_nonneg_left bot_le
    _ = _ := fullOccupation_unfold.symm

theorem full_comp_pow_le (n : ℕ) : fullOccupation ∘ₖ (costKernel ^ n) ≤ fullOccupation := by
  induction n with
  | zero => change fullOccupation ∘ₖ Kernel.id ≤ fullOccupation; rw [Kernel.comp_id]
  | succ n ih =>
    have hp : costKernel ^ (n + 1) = (costKernel ^ n) ∘ₖ costKernel := pow_succ _ _
    rw [hp, ← Kernel.comp_assoc]
    exact le_trans (compose_mono_left ih costKernel) full_comp_step_le

theorem prefixOccupation_le_full (n : ℕ) (hn : 0 < n) : prefixOccupation n ≤ fullOccupation := by
  cases n with
  | zero => omega
  | succ n =>
    have hp : costKernel ^ (n + 1) = costKernel ∘ₖ (costKernel ^ n) := pow_succ' _ _
    rw [prefixOccupation, hp, ← Kernel.comp_assoc, inclusive_comp_step]
    exact full_comp_pow_le n

end NumberTheoryLean.CostPrefixTransport

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_BandShiftTransport
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.BandShiftTransport

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open FinitePathMeasures OccupationRegeneration RegenerationBandBounds CostPrefixTransport

theorem stateBandReward_measurable {Q : State → ℝ≥0∞} (hQ : Measurable Q) (v h : ℝ) :
    Measurable (stateBandReward Q v h) :=
  (hQ.comp measurable_fst).indicator (measurable_snd measurableSet_Icc)

theorem bandExpectation_measurable {Q : State → ℝ≥0∞} (hQ : Measurable Q) (v h : ℝ) :
    Measurable (bandExpectation Q v h) := (stateBandReward_measurable hQ v h).lintegral_kernel

theorem zeroBandExpectation_measurable {Q : State → ℝ≥0∞} (hQ : Measurable Q) (v h : ℝ) :
    Measurable (zeroBandExpectation Q v h) :=
  (bandExpectation_measurable hQ v h).comp (measurable_id.prodMk measurable_const)

theorem stateBandReward_shift (Q : State → ℝ≥0∞) (v h a : ℝ) (y : CostState) :
    stateBandReward Q v h (shiftFullCost a y) = stateBandReward Q (v - a) h y := by
  classical
  have heq : y.2 + a ∈ Icc v (v + h) ↔ y.2 ∈ Icc (v - a) (v - a + h) := by
    simp only [mem_Icc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  simp only [stateBandReward, indicator_apply, mem_preimage, shiftFullCost]
  simp only [heq]

theorem bandExpectation_translation {Q : State → ℝ≥0∞} (hQ : Measurable Q)
    (v h : ℝ) (z : CostState) :
    bandExpectation Q v h z = zeroBandExpectation Q (v - z.2) h z.1 := by
  have hshift := inclusiveOccupation_translation (z.1, 0) z.2
  have hz : shiftFullCost z.2 (z.1, 0) = z := by simp [shiftFullCost]
  rw [hz] at hshift
  rw [bandExpectation, ← hshift, lintegral_map (stateBandReward_measurable hQ v h) (shiftFullCost_measurable z.2)]
  apply lintegral_congr
  intro y
  exact stateBandReward_shift Q v h z.2 y

theorem stateBandReward_mono (Q : State → ℝ≥0∞) {v h v' h' : ℝ}
    (hsub : Icc v (v + h) ⊆ Icc v' (v' + h')) (y : CostState) :
    stateBandReward Q v h y ≤ stateBandReward Q v' h' y := by
  classical
  unfold stateBandReward
  by_cases hy : y.2 ∈ Icc v (v + h)
  · rw [indicator_of_mem (show y ∈ Prod.snd ⁻¹' Icc v (v + h) from hy),
      indicator_of_mem (show y ∈ Prod.snd ⁻¹' Icc v' (v' + h') from hsub hy)]
  · rw [indicator_of_notMem (show y ∉ Prod.snd ⁻¹' Icc v (v + h) from hy)]
    exact zero_le

theorem bandExpectation_mono (Q : State → ℝ≥0∞) {v h v' h' : ℝ}
    (hsub : Icc v (v + h) ⊆ Icc v' (v' + h')) (z : CostState) :
    bandExpectation Q v h z ≤ bandExpectation Q v' h' z :=
  lintegral_mono (stateBandReward_mono Q hsub)

theorem remove_prefix_cost {Q : State → ℝ≥0∞} (hQ : Measurable Q)
    (v h C : ℝ) (z : CostState) (hz : 0 ≤ z.2 ∧ z.2 ≤ C) :
    bandExpectation Q v h z ≤ zeroBandExpectation Q (v - C) (h + C) z.1 := by
  rw [bandExpectation_translation hQ]
  apply bandExpectation_mono
  intro t ht
  change v - z.2 ≤ t ∧ t ≤ v - z.2 + h at ht
  change v - C ≤ t ∧ t ≤ v - C + (h + C)
  constructor <;> linarith [ht.1, ht.2, hz.1, hz.2]

theorem restore_prefix_cost {Q : State → ℝ≥0∞} (hQ : Measurable Q)
    (v h C : ℝ) (z : CostState) (hz : 0 ≤ z.2 ∧ z.2 ≤ C) :
    zeroBandExpectation Q v h z.1 ≤ bandExpectation Q v (h + C) z := by
  rw [bandExpectation_translation hQ]
  apply bandExpectation_mono
  intro t ht
  change v ≤ t ∧ t ≤ v + h at ht
  change v - z.2 ≤ t ∧ t ≤ v - z.2 + (h + C)
  constructor <;> linarith [ht.1, ht.2, hz.1, hz.2]

theorem prefix_band_domination {Q : State → ℝ≥0∞} (hQ : Measurable Q)
    (m n : ℕ) (x y : State) {C : ℝ≥0∞}
    (hdom : (stateKernel ^ m) x ≤ C • (stateKernel ^ n) y) (v h : ℝ) :
    (∫⁻ z, stateBandReward Q v h z ∂prefixOccupation m (x, 0)) ≤
      C * ∫⁻ z, stateBandReward Q (v - (m : ℝ) * Real.log 3)
        (h + (m : ℝ) * Real.log 3 + (n : ℝ) * Real.log 3) z ∂prefixOccupation n (y, 0) := by
  let v' := v - (m : ℝ) * Real.log 3
  let h' := h + (m : ℝ) * Real.log 3
  have hM := zeroBandExpectation_measurable hQ v' h'
  have hmCost : ∀ᵐ z ∂(costKernel ^ m) (x, 0), 0 ≤ z.2 ∧ z.2 ≤ (m : ℝ) * Real.log 3 := by
    simpa only [zero_add] using costKernel_pow_cost_bounds m (x, 0)
  have hnCost : ∀ᵐ z ∂(costKernel ^ n) (y, 0), 0 ≤ z.2 ∧ z.2 ≤ (n : ℝ) * Real.log 3 := by
    simpa only [zero_add] using costKernel_pow_cost_bounds n (y, 0)
  rw [prefixOccupation, Kernel.lintegral_comp _ _ _ (stateBandReward_measurable hQ v h),
    prefixOccupation, Kernel.lintegral_comp _ _ _ (stateBandReward_measurable hQ v' (h' + (n : ℝ) * Real.log 3))]
  change (∫⁻ z, bandExpectation Q v h z ∂(costKernel ^ m) (x, 0)) ≤
    C * ∫⁻ z, bandExpectation Q v' (h' + (n : ℝ) * Real.log 3) z ∂(costKernel ^ n) (y, 0)
  calc
    _ ≤ ∫⁻ z, zeroBandExpectation Q v' h' z.1 ∂(costKernel ^ m) (x, 0) := by
      apply lintegral_mono_ae
      filter_upwards [hmCost] with z hz
      exact remove_prefix_cost hQ v h ((m : ℝ) * Real.log 3) z hz
    _ = ∫⁻ s, zeroBandExpectation Q v' h' s ∂(stateKernel ^ m) x := by
      rw [← costKernel_pow_map_state m (x, 0), lintegral_map hM measurable_fst]
    _ ≤ ∫⁻ s, zeroBandExpectation Q v' h' s ∂C • (stateKernel ^ n) y := lintegral_mono' hdom le_rfl
    _ = C * ∫⁻ s, zeroBandExpectation Q v' h' s ∂(stateKernel ^ n) y := by rw [lintegral_smul_measure, smul_eq_mul]
    _ = C * ∫⁻ z, zeroBandExpectation Q v' h' z.1 ∂(costKernel ^ n) (y, 0) := by
      rw [← costKernel_pow_map_state n (y, 0), lintegral_map hM measurable_fst]
    _ ≤ _ := by
      apply mul_le_mul le_rfl _ zero_le zero_le
      apply lintegral_mono_ae
      filter_upwards [hnCost] with z hz
      exact restore_prefix_cost hQ v' h' ((n : ℝ) * Real.log 3) z hz

end NumberTheoryLean.BandShiftTransport

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_EvenInverseBands
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.StateMarginalBridge
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathMeasures
open NumberTheoryLean.RegenerationTails
open Erdos970Dependency.OrdinaryKernelInvariance Erdos970Dependency.StateKernelInvariance
open Erdos970Dependency.MarginalDensityMeasures

theorem evenReal_map_lift : evenRealKernel.map oddLift = evenToOdd.comap evenLift evenLift_measurable := by
  ext s B hB
  rw [Kernel.map_apply _ oddLift_measurable]
  change (evenKernel (evenLift s)).map oddLift B = evenToOdd (evenLift s) B
  rw [evenKernel_map_lift]

theorem oddReal_map_lift : oddRealKernel.map evenLift = oddToEven.comap oddLift oddLift_measurable := by
  ext s B hB
  rw [Kernel.map_apply _ evenLift_measurable]
  change (oddKernel (oddLift s)).map evenLift B = oddToEven (oddLift s) B
  rw [oddKernel_map_lift]

theorem propagate_even (mu : Measure ℝ) :
    stateKernel ∘ₘ (mu.map evenLift).map Sum.inl = ((evenRealKernel ∘ₘ mu).map oddLift).map Sum.inr := by
  rw [comp_map_input _ _ _ measurable_inl]
  change evenBranch ∘ₘ mu.map evenLift = _
  rw [evenBranch, ← Measure.map_comp _ _ measurable_inr,
    comp_map_input _ _ _ evenLift_measurable, ← evenReal_map_lift,
    ← Measure.map_comp _ _ oddLift_measurable]

theorem propagate_odd (mu : Measure ℝ) :
    stateKernel ∘ₘ (mu.map oddLift).map Sum.inr = ((oddRealKernel ∘ₘ mu).map evenLift).map Sum.inl := by
  rw [comp_map_input _ _ _ measurable_inr]
  change oddBranch ∘ₘ mu.map oddLift = _
  rw [oddBranch, ← Measure.map_comp _ _ measurable_inl,
    comp_map_input _ _ _ oddLift_measurable, ← oddReal_map_lift,
    ← Measure.map_comp _ _ evenLift_measurable]

theorem state_even_first (s : EvenState) :
    stateKernel (Sum.inl s) = ((evenKernel s).map oddLift).map Sum.inr := by
  change evenBranch s = _
  rw [evenBranch, Kernel.map_apply _ measurable_inr, evenKernel_map_lift]

theorem state_odd_first (s : OddState) :
    stateKernel (Sum.inr s) = ((oddKernel s).map evenLift).map Sum.inl := by
  change oddBranch s = _
  rw [oddBranch, Kernel.map_apply _ measurable_inl, oddKernel_map_lift]

theorem state_even_two (s : EvenState) :
    (stateKernel ^ 2) (Sum.inl s) = ((initialTwoMeasure s).map evenLift).map Sum.inl := by
  rw [pow_two]
  change (stateKernel ∘ₖ stateKernel) (Sum.inl s) = _
  rw [Kernel.comp_apply, state_even_first]
  exact propagate_odd (evenKernel s)

theorem state_odd_two (s : OddState) :
    (stateKernel ^ 2) (Sum.inr s) = ((evenRealKernel ∘ₘ oddKernel s).map oddLift).map Sum.inr := by
  rw [pow_two]
  change (stateKernel ∘ₖ stateKernel) (Sum.inr s) = _
  rw [Kernel.comp_apply, state_odd_first]
  exact propagate_even (oddKernel s)

theorem state_reg_three :
    (stateKernel ^ 3) (Sum.inr regenerationState) = (regThreeMeasure.map evenLift).map Sum.inl := by
  have hp : stateKernel ^ 3 = stateKernel ∘ₖ (stateKernel ^ 2) := pow_succ' stateKernel 2
  rw [hp, Kernel.comp_apply, state_odd_two]
  exact propagate_odd (evenRealKernel ∘ₘ oddKernel regenerationState)

end Erdos970Dependency.StateMarginalBridge

end

section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.InitialStateDomination
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathMeasures NumberTheoryLean.RegenerationTails
open Erdos970Dependency.OrdinaryKernelInvariance Erdos970Dependency.DensityComparison
open Erdos970Dependency.MarginalDensityMeasures Erdos970Dependency.StateMarginalBridge

theorem initial_state_measure_le (s : EvenState) (hs : 199 / 100 ≤ s.1) (hsup : s.1 ≤ 23 / 10) :
    (stateKernel ^ 2) (Sum.inl s) ≤ ENNReal.ofReal dominationConstant •
      (stateKernel ^ 3) (Sum.inr regenerationState) := by
  rw [state_even_two, state_reg_three]
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.map_apply measurable_inl hB,
    Measure.map_apply evenLift_measurable (measurable_inl hB),
    Measure.smul_apply, smul_eq_mul,
    Measure.map_apply measurable_inl hB,
    Measure.map_apply evenLift_measurable (measurable_inl hB)]
  have h := Measure.le_iff.mp (initial_real_measure_le s hs hsup)
    (evenLift ⁻¹' (Sum.inl ⁻¹' B)) (evenLift_measurable (measurable_inl hB))
  rw [Measure.smul_apply, smul_eq_mul] at h
  exact h

theorem initial_two_step_domination : ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ s : EvenState, 199 / 100 ≤ s.1 → s.1 ≤ 23 / 10 →
      (stateKernel ^ 2) (Sum.inl s) ≤ C • (stateKernel ^ 3) (Sum.inr regenerationState) := by
  exact ⟨ENNReal.ofReal dominationConstant, ENNReal.ofReal_lt_top, initial_state_measure_le⟩

end Erdos970Dependency.InitialStateDomination

end

section

namespace NumberTheoryLean.InvariantInverseWeights

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open DerivativeWeights TransitionKernels FinitePathMeasures
open Erdos970Dependency.InvariantDensities Erdos970Dependency.InvariantFiniteness
open Erdos970Dependency.OrdinaryKernelInvariance Erdos970Dependency.StateKernelInvariance

theorem inverseWeightCutoff_measurable (L : ℝ) : Measurable (inverseWeightCutoff L) :=
  (ENNReal.measurable_ofReal.comp stateWeight_measurable).inv.indicator
    (measurableSet_lt stateRatio_measurable measurable_const)

theorem even_inverse_density_le (L t : ℝ) :
    ENNReal.ofReal (Erdos970Dependency.InvariantDensities.evenDensity t) * inverseWeightCutoff L (.inl (evenLift t)) ≤
      (Icc (0 : ℝ) L).indicator (fun _ => (1 : ℝ≥0∞)) t := by
  by_cases ht : 2 ≤ t
  · have hl : (evenLift t).1 = t := max_eq_right (by linarith)
    have hw : stateWeight (.inl (evenLift t)) = phiEven t := by change phiEven (evenLift t).1 = _; rw [hl]
    have hr : stateRatio (.inl (evenLift t)) = t := hl
    rw [Erdos970Dependency.InvariantDensities.evenDensity, indicator_of_mem (show t ∈ Ici (2 : ℝ) from ht)]
    unfold inverseWeightCutoff
    by_cases hL : t < L
    · rw [indicator_of_mem (show (.inl (evenLift t) : State) ∈ {s | stateRatio s < L} by simpa only [mem_ofPred_eq, hr] using hL), hw,
        ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr (phiEven_pos (by linarith))).ne' ENNReal.ofReal_ne_top,
        indicator_of_mem (show t ∈ Icc (0 : ℝ) L from ⟨by linarith, hL.le⟩)]
    · rw [indicator_of_notMem (show (.inl (evenLift t) : State) ∉ {s | stateRatio s < L} by simpa only [mem_ofPred_eq, hr] using hL), mul_zero]
      exact zero_le
  · rw [Erdos970Dependency.InvariantDensities.evenDensity, indicator_of_notMem (show t ∉ Ici (2 : ℝ) from ht), ENNReal.ofReal_zero, zero_mul]
    exact zero_le

theorem odd_inverse_density_le (L t : ℝ) :
    ENNReal.ofReal (Erdos970Dependency.InvariantDensities.oddDensity t) * inverseWeightCutoff L (.inr (oddLift t)) ≤
      (Icc (0 : ℝ) L).indicator (fun _ => (1 : ℝ≥0∞)) t := by
  by_cases ht : 1 ≤ t
  · have hl : (oddLift t).1 = t := max_eq_right (by linarith)
    have hw : stateWeight (.inr (oddLift t)) = phiOdd t := by change phiOdd (oddLift t).1 = _; rw [hl]
    have hr : stateRatio (.inr (oddLift t)) = t := hl
    have hf := oddFactor_bounds ht
    rw [Erdos970Dependency.InvariantDensities.oddDensity, indicator_of_mem (show t ∈ Ici (1 : ℝ) from ht), ENNReal.ofReal_mul hf.1]
    unfold inverseWeightCutoff
    by_cases hL : t < L
    · rw [indicator_of_mem (show (.inr (oddLift t) : State) ∈ {s | stateRatio s < L} by simpa only [mem_ofPred_eq, hr] using hL), hw,
        mul_assoc, ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr (phiOdd_pos t)).ne' ENNReal.ofReal_ne_top, mul_one,
        indicator_of_mem (show t ∈ Icc (0 : ℝ) L from ⟨by linarith, hL.le⟩)]
      exact (ENNReal.ofReal_le_ofReal hf.2).trans_eq ENNReal.ofReal_one
    · rw [indicator_of_notMem (show (.inr (oddLift t) : State) ∉ {s | stateRatio s < L} by simpa only [mem_ofPred_eq, hr] using hL), mul_zero]
      exact zero_le
  · rw [Erdos970Dependency.InvariantDensities.oddDensity, indicator_of_notMem (show t ∉ Ici (1 : ℝ) from ht), ENNReal.ofReal_zero, zero_mul]
    exact zero_le

theorem inverseWeightCutoff_mass_le {L : ℝ} (hL : 0 ≤ L) :
    (∫⁻ s : State, inverseWeightCutoff L s ∂stateMeasure) ≤ ENNReal.ofReal (2 * L) := by
  have hQ := inverseWeightCutoff_measurable L
  rw [stateMeasure, lintegral_add_measure,
    lintegral_map hQ measurable_inl, lintegral_map hQ measurable_inr,
    evenStateMeasure, oddStateMeasure,
    lintegral_map (f := fun s : EvenState => inverseWeightCutoff L (.inl s)) (hQ.comp measurable_inl) evenLift_measurable,
    lintegral_map (f := fun s : OddState => inverseWeightCutoff L (.inr s)) (hQ.comp measurable_inr) oddLift_measurable,
    evenMeasure, oddMeasure,
    lintegral_withDensity_eq_lintegral_mul volume
      (f := fun t : ℝ => ENNReal.ofReal (Erdos970Dependency.InvariantDensities.evenDensity t))
      (g := fun t : ℝ => inverseWeightCutoff L (.inl (evenLift t)))
      (ENNReal.measurable_ofReal.comp Erdos970Dependency.InvariantDensities.evenDensity_measurable)
      (hQ.comp (measurable_inl.comp evenLift_measurable)),
    lintegral_withDensity_eq_lintegral_mul volume
      (f := fun t : ℝ => ENNReal.ofReal (Erdos970Dependency.InvariantDensities.oddDensity t))
      (g := fun t : ℝ => inverseWeightCutoff L (.inr (oddLift t)))
      (ENNReal.measurable_ofReal.comp Erdos970Dependency.InvariantDensities.oddDensity_measurable)
      (hQ.comp (measurable_inr.comp oddLift_measurable))]
  calc
    _ ≤ (∫⁻ t : ℝ, (Icc (0 : ℝ) L).indicator (fun _ => (1 : ℝ≥0∞)) t) +
        (∫⁻ t : ℝ, (Icc (0 : ℝ) L).indicator (fun _ => (1 : ℝ≥0∞)) t) :=
      add_le_add (lintegral_mono (even_inverse_density_le L)) (lintegral_mono (odd_inverse_density_le L))
    _ = ENNReal.ofReal L + ENNReal.ofReal L := by
      have hI : (∫⁻ t : ℝ, (Icc (0 : ℝ) L).indicator (fun _ => (1 : ℝ≥0∞)) t) = ENNReal.ofReal L := by
        change (∫⁻ t : ℝ, (Icc (0 : ℝ) L).indicator 1 t) = _
        rw [lintegral_indicator_one measurableSet_Icc, Real.volume_Icc, sub_zero]
      rw [hI]
    _ = _ := by rw [← ENNReal.ofReal_add hL hL]; congr 1; ring

end NumberTheoryLean.InvariantInverseWeights

end

section

namespace NumberTheoryLean.FirstStepInverseWeight

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open DerivativeWeights WeightFutureIntegrals TransitionKernels FinitePathMeasures
open KernelDensityBridge InvariantInverseWeights

theorem firstDensityConstant_pos : 0 < firstDensityConstant := div_pos (by norm_num) (phiEven_pos (by norm_num))

theorem W_le_three {t : ℝ} (ht : (49 / 50 : ℝ) ≤ t) : W t ≤ 3 := by
  have ht0 : 0 < t := by linarith
  rw [W]
  apply (div_le_iff₀ (sq_pos_of_pos ht0)).mpr
  nlinarith [sq_nonneg (t - 49 / 50)]

theorem first_odd_density_bound (s : EvenState) (hs : s.1 ≤ 23 / 10) (t : ℝ) :
    evenDensity s t ≤ firstDensityConstant * (Ici (49 / 50 : ℝ)).indicator phiOdd t := by
  have hφ := phiEven_pos (s := s.1) (by linarith [s.2])
  have hm := phiEven_pos (s := (23 / 10 : ℝ)) (by norm_num)
  have hmin : phiEven (23 / 10) ≤ phiEven s.1 :=
    phiEven_strictAntiOn.antitoneOn (by change 1 < s.1; linarith [s.2]) (by norm_num) hs
  unfold evenDensity tailDensity
  by_cases ht : s.1 - 1 ≤ t
  · have ht98 : (49 / 50 : ℝ) ≤ t := by linarith [s.2]
    rw [indicator_of_mem (show t ∈ Ici (s.1 - 1) from ht),
      indicator_of_mem (show t ∈ Ici (49 / 50 : ℝ) from ht98)]
    apply (div_le_iff₀ hφ).mpr
    calc
      W t * phiOdd t ≤ 3 * phiOdd t := mul_le_mul_of_nonneg_right (W_le_three ht98) (phiOdd_pos t).le
      _ = (firstDensityConstant * phiOdd t) * phiEven (23 / 10) := by
        dsimp [firstDensityConstant]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hmin (mul_nonneg firstDensityConstant_pos.le (phiOdd_pos t).le)
  · rw [indicator_of_notMem (show t ∉ Ici (s.1 - 1) from ht)]
    by_cases h98 : (49 / 50 : ℝ) ≤ t
    · rw [indicator_of_mem (show t ∈ Ici (49 / 50 : ℝ) from h98)]
      exact mul_nonneg firstDensityConstant_pos.le (phiOdd_pos t).le
    · rw [indicator_of_notMem (show t ∉ Ici (49 / 50 : ℝ) from h98), mul_zero]

theorem first_odd_inverse_mass (s : EvenState) (hs : s.1 ≤ 23 / 10) {L : ℝ} (_hL : 0 ≤ L) :
    (∫⁻ t : State, inverseWeightCutoff L t ∂stateKernel (.inl s)) ≤
      ENNReal.ofReal (firstDensityConstant * L) := by
  classical
  let G : ℝ → ℝ≥0∞ := (Iio L).indicator (fun t => (ENNReal.ofReal (phiOdd t))⁻¹)
  have hG : Measurable G := (ENNReal.measurable_ofReal.comp phiOdd_continuous.measurable).inv.indicator measurableSet_Iio
  have hQ := inverseWeightCutoff_measurable L
  change (∫⁻ t : State, inverseWeightCutoff L t ∂evenBranch s) ≤ _
  rw [evenBranch, Kernel.map_apply _ measurable_inr, lintegral_map hQ measurable_inr]
  change (∫⁻ t : OddState, G t.1 ∂evenToOdd s) ≤ _
  rw [evenToOdd_lintegral_ratio s hG, evenKernel_lintegral_density s hG]
  change (∫⁻ t : ℝ, ENNReal.ofReal (evenDensity s t) * G t) ≤ _
  have hb : ∀ t : ℝ, ENNReal.ofReal (evenDensity s t) * G t ≤
      ENNReal.ofReal firstDensityConstant * (Icc (0 : ℝ) L).indicator (fun _ => (1 : ℝ≥0∞)) t := by
    intro t
    have hd := first_odd_density_bound s hs t
    by_cases h98 : (49 / 50 : ℝ) ≤ t
    · rw [indicator_of_mem (show t ∈ Ici (49 / 50 : ℝ) from h98)] at hd
      by_cases htL : t < L
      · rw [show G t = (ENNReal.ofReal (phiOdd t))⁻¹ by
          exact indicator_of_mem (show t ∈ Iio L from htL) _,
          indicator_of_mem (show t ∈ Icc (0 : ℝ) L from ⟨by linarith, htL.le⟩), mul_one]
        calc
          _ ≤ ENNReal.ofReal (firstDensityConstant * phiOdd t) * (ENNReal.ofReal (phiOdd t))⁻¹ :=
            mul_le_mul (ENNReal.ofReal_le_ofReal hd) le_rfl zero_le zero_le
          _ = _ := by
            rw [ENNReal.ofReal_mul firstDensityConstant_pos.le, mul_assoc,
              ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr (phiOdd_pos t)).ne' ENNReal.ofReal_ne_top, mul_one]
      · rw [show G t = 0 from indicator_of_notMem (show t ∉ Iio L from htL) _, mul_zero]
        exact zero_le
    · rw [indicator_of_notMem (show t ∉ Ici (49 / 50 : ℝ) from h98), mul_zero] at hd
      rw [ENNReal.ofReal_eq_zero.mpr hd, zero_mul]
      exact zero_le
  calc
    _ ≤ ∫⁻ t : ℝ, ENNReal.ofReal firstDensityConstant * (Icc (0 : ℝ) L).indicator (fun _ => (1 : ℝ≥0∞)) t := lintegral_mono hb
    _ = ENNReal.ofReal firstDensityConstant * ENNReal.ofReal L := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      change (∫⁻ t : ℝ, (Icc (0 : ℝ) L).indicator 1 t) = _
      rw [lintegral_indicator_one measurableSet_Icc, Real.volume_Icc, sub_zero]
    _ = _ := (ENNReal.ofReal_mul firstDensityConstant_pos.le).symm

end NumberTheoryLean.FirstStepInverseWeight

end

section

namespace NumberTheoryLean.RegeneratingInverseBands

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures PairedCostGrouping RegenerationTails OccupationDecomposition
open RegenerationBandBounds InvariantInverseWeights FirstStepInverseWeight

theorem inverseArrivalBand_measurable (v R ell : ℝ) : Measurable (inverseArrivalBand v R ell) := by
  have hg : Measurable (gapValue v) := Real.measurable_exp.comp (measurable_const.sub measurable_snd)
  exact ((ENNReal.measurable_ofReal.comp (stateWeight_measurable.comp measurable_fst)).inv).indicator
    ((measurableSet_le measurable_const hg).inter
      ((measurableSet_le hg measurable_const).inter
        (measurableSet_lt (stateRatio_measurable.comp measurable_fst) (hg.div_const ell))))

theorem stateBandReward_le (Q : State → ℝ≥0∞) (v h : ℝ) (z : CostState) :
    stateBandReward Q v h z ≤ Q z.1 := by
  classical
  unfold stateBandReward
  by_cases hz : z.2 ∈ Icc v (v + h)
  · rw [indicator_of_mem (show z ∈ Prod.snd ⁻¹' Icc v (v + h) from hz)]
  · rw [indicator_of_notMem (show z ∉ Prod.snd ⁻¹' Icc v (v + h) from hz)]
    exact zero_le

theorem inverseArrivalBand_le_costBand (v : ℝ) {R ell : ℝ} (hR : 0 < R) (hell : 1 ≤ ell)
    (z : CostState) :
    inverseArrivalBand v R ell z ≤
      stateBandReward (inverseWeightCutoff (Real.exp 1 * R)) (v - Real.log R - 1) 1 z := by
  classical
  by_cases hz : R ≤ gapValue v z ∧ gapValue v z ≤ Real.exp 1 * R ∧ stateRatio z.1 < gapValue v z / ell
  · have hg : 0 < gapValue v z := Real.exp_pos _
    have hl : Real.log R ≤ v - z.2 := by
      have h := Real.log_le_log hR hz.1
      rwa [gapValue, Real.log_exp] at h
    have hu : v - z.2 ≤ 1 + Real.log R := by
      have h := Real.log_le_log hg hz.2.1
      rwa [gapValue, Real.log_exp, Real.log_mul (Real.exp_pos 1).ne' hR.ne', Real.log_exp] at h
    have ht : stateRatio z.1 < Real.exp 1 * R :=
      lt_of_lt_of_le hz.2.2 (le_trans (div_le_self hg.le hell) hz.2.1)
    have hband : z.2 ∈ Icc (v - Real.log R - 1) (v - Real.log R - 1 + 1) := by
      constructor <;> linarith
    unfold inverseArrivalBand stateBandReward inverseWeightCutoff
    rw [indicator_of_mem (show z ∈ {z | R ≤ gapValue v z ∧ gapValue v z ≤ Real.exp 1 * R ∧ stateRatio z.1 < gapValue v z / ell} from hz),
      indicator_of_mem (show z ∈ Prod.snd ⁻¹' Icc (v - Real.log R - 1) (v - Real.log R - 1 + 1) from hband),
      indicator_of_mem (show z.1 ∈ {s | stateRatio s < Real.exp 1 * R} from ht)]
  · unfold inverseArrivalBand
    rw [indicator_of_notMem (show z ∉ {z | R ≤ gapValue v z ∧ gapValue v z ≤ Real.exp 1 * R ∧ stateRatio z.1 < gapValue v z / ell} from hz)]
    exact zero_le

theorem first_odd_inverse_arrival_band (s : TransitionKernels.EvenState) (hs : s.1 ≤ 23 / 10)
    (v : ℝ) {R ell : ℝ} (hR : 0 < R) (hell : 1 ≤ ell) :
    (∫⁻ z, inverseArrivalBand v R ell z ∂costKernel (.inl s, 0)) ≤
      ENNReal.ofReal (firstDensityConstant * Real.exp 1) * ENNReal.ofReal R := by
  have hQ := inverseWeightCutoff_measurable (Real.exp 1 * R)
  calc
    _ ≤ ∫⁻ z, inverseWeightCutoff (Real.exp 1 * R) z.1 ∂costKernel (.inl s, 0) :=
      lintegral_mono (fun z => le_trans (inverseArrivalBand_le_costBand v hR hell z) (stateBandReward_le _ _ _ z))
    _ = ∫⁻ t : State, inverseWeightCutoff (Real.exp 1 * R) t ∂stateKernel (.inl s) := by
      rw [← Erdos970Dependency.ActualCycleOccupation.costKernel_map_state (.inl s, 0), lintegral_map hQ measurable_fst]
    _ ≤ ENNReal.ofReal (firstDensityConstant * (Real.exp 1 * R)) := first_odd_inverse_mass s hs (by positivity)
    _ = _ := by rw [← ENNReal.ofReal_mul (mul_pos firstDensityConstant_pos (Real.exp_pos 1)).le]; congr 1; ring

end NumberTheoryLean.RegeneratingInverseBands

end

section

namespace NumberTheoryLean.EvenBandBounds

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathMeasures RegenerationTails PairedCostGrouping
open OccupationDecomposition InitialOccupation CostPrefixTransport
open BandShiftTransport RegenerationBandBounds RegeneratingInverseBands
open Erdos970Dependency.StateKernelInvariance
open Erdos970Dependency.InitialStateDomination

theorem even_uniform_band (h : ℝ) : ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ Q : State → ℝ≥0∞, Measurable Q → ∀ v : ℝ, ∀ s : EvenState,
      (199 / 100 : ℝ) ≤ s.1 → s.1 ≤ 23 / 10 →
      (∫⁻ z, stateBandReward Q v h z ∂prefixOccupation 2 (.inl s, 0)) ≤
        C * ∫⁻ t : State, Q t ∂stateMeasure := by
  obtain ⟨D, hD, hdom⟩ := initial_two_step_domination
  obtain ⟨B, hB, hb⟩ := regeneration_uniform_band_jb247 (h + 5 * Real.log 3)
  refine ⟨D * B, ENNReal.mul_lt_top hD hB, ?_⟩
  intro Q hQ v s hsL hsU
  have ht := prefix_band_domination hQ 2 3 (.inl s) (.inr regenerationState) (hdom s hsL hsU) v h
  norm_num only [Nat.cast_ofNat] at ht
  rw [show h + 2 * Real.log 3 + 3 * Real.log 3 = h + 5 * Real.log 3 by ring] at ht
  calc
    _ ≤ D * ∫⁻ z, stateBandReward Q (v - 2 * Real.log 3) (h + 5 * Real.log 3) z
        ∂prefixOccupation 3 (.inr regenerationState, 0) := ht
    _ ≤ D * ∫⁻ z, stateBandReward Q (v - 2 * Real.log 3) (h + 5 * Real.log 3) z
        ∂fullOccupation (.inr regenerationState, 0) :=
      mul_le_mul le_rfl (lintegral_mono' (prefixOccupation_le_full 3 (by norm_num) (.inr regenerationState, 0)) le_rfl) zero_le zero_le
    _ ≤ D * (B * ∫⁻ t : State, Q t ∂stateMeasure) := mul_le_mul le_rfl (hb Q hQ _) zero_le zero_le
    _ = _ := (mul_assoc _ _ _).symm

theorem prefixOccupation_two : prefixOccupation 2 = fullOccupation ∘ₖ costKernel := by
  rw [prefixOccupation, pow_two]
  change inclusiveOccupation ∘ₖ (costKernel ∘ₖ costKernel) = _
  rw [← Kernel.comp_assoc, inclusive_comp_step]

theorem fullOccupation_first_and_later : fullOccupation = costKernel + prefixOccupation 2 := by
  rw [prefixOccupation_two]
  exact fullOccupation_unfold

end NumberTheoryLean.EvenBandBounds

end

section

namespace NumberTheoryLean.WeightedGapTail

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathMeasures PairedCostGrouping RegenerationTails OccupationDecomposition
open InvariantInverseWeights RegeneratingInverseBands

theorem tailSeries_summable {c : ℝ} (hc : 0 < c) : Summable (tailSeries c) := by
  have h := (summable_nat_add_iff 2).mpr (Real.summable_pow_mul_exp_neg_nat_mul 3 hc)
  have h' := h.mul_left (Real.exp c)
  convert! h' using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  simp only [tailSeries, Nat.cast_add, Nat.cast_ofNat]
  rw [mul_comm (Real.exp c), mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem tailBudget_tendsto_zero {C : ℝ≥0∞} (hC : C ≠ ∞) {c : ℝ} (hc : 0 < c) :
    Tendsto (tailBudget C c) atTop (𝓝 0) := by
  have hs : (∑' n : ℕ, ENNReal.ofReal (tailSeries c n)) ≠ ∞ := (tailSeries_summable hc).tsum_ofReal_lt_top.ne
  have h := ENNReal.tendsto_sum_nat_add (fun n => ENNReal.ofReal (tailSeries c n)) hs
  change Tendsto (fun N : ℕ => C * ∑' k : ℕ, ENNReal.ofReal (tailSeries c (k + N))) atTop (𝓝 0)
  simpa only [mul_zero] using (ENNReal.Tendsto.const_mul (a := C) h (Or.inr hC))

theorem tailReward_measurable (c v ell : ℝ) (N : ℕ) : Measurable (tailReward c v ell N) := by
  have hg : Measurable (gapValue v) := Real.measurable_exp.comp (measurable_const.sub measurable_snd)
  exact ((ENNReal.measurable_ofReal.comp ((hg.pow_const 2).mul (Real.measurable_exp.comp (measurable_const.mul hg)))).mul
    (ENNReal.measurable_ofReal.comp (stateWeight_measurable.comp measurable_fst)).inv).indicator
      ((measurableSet_le measurable_const hg).inter
        (measurableSet_lt (stateRatio_measurable.comp measurable_fst) (hg.div_const ell)))

theorem tailReward_le_band_sum {c : ℝ} (hc : 0 < c) (v ell : ℝ) (N : ℕ) (z : CostState) :
    tailReward c v ell N z ≤ ∑' k : ℕ,
      ENNReal.ofReal (binCoefficient c (k + N)) * inverseArrivalBand v ((k + N : ℕ) + 1) ell z := by
  classical
  by_cases hz : (N : ℝ) + 1 ≤ gapValue v z ∧ stateRatio z.1 < gapValue v z / ell
  · let r := gapValue v z
    have hr : 0 < r := Real.exp_pos _
    have hn : N + 1 ≤ ⌊r⌋₊ := (Nat.le_floor_iff hr.le).mpr (by exact_mod_cast hz.1)
    let k := ⌊r⌋₊ - (N + 1)
    have hk : k + N + 1 = ⌊r⌋₊ := by dsimp [k]; omega
    have hkR : ((k + N : ℕ) : ℝ) + 1 = (⌊r⌋₊ : ℝ) := by exact_mod_cast hk
    let R : ℝ := ((k + N : ℕ) : ℝ) + 1
    have hR1 : 1 ≤ R := by dsimp [R]; have hh := Nat.cast_nonneg' (α := ℝ) (k + N); linarith
    have hlow : R ≤ r := by rw [show R = (⌊r⌋₊ : ℝ) from hkR]; exact Nat.floor_le hr.le
    have hhigh : r < R + 1 := by rw [show R = (⌊r⌋₊ : ℝ) from hkR]; exact Nat.lt_floor_add_one r
    have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hupper : r ≤ Real.exp 1 * R := by nlinarith [mul_le_mul_of_nonneg_right he (by linarith : 0 ≤ R)]
    have hsq : r ^ 2 ≤ (R + 1) ^ 2 := by nlinarith
    have hexp : Real.exp (-c * r) ≤ Real.exp (-c * R) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hlow (by linarith))
    have hweight : r ^ 2 * Real.exp (-c * r) ≤ (R + 1) ^ 2 * Real.exp (-c * R) :=
      mul_le_mul hsq hexp (Real.exp_pos _).le (sq_nonneg _)
    have hA : R ≤ gapValue v z ∧ gapValue v z ≤ Real.exp 1 * R ∧ stateRatio z.1 < gapValue v z / ell :=
      ⟨hlow, hupper, hz.2⟩
    calc
      _ = ENNReal.ofReal (r ^ 2 * Real.exp (-c * r)) * (ENNReal.ofReal (stateWeight z.1))⁻¹ :=
        by rw [tailReward, indicator_of_mem (show z ∈ {z : CostState | (N : ℝ) + 1 ≤ gapValue v z ∧ stateRatio z.1 < gapValue v z / ell} from hz)]
      _ ≤ ENNReal.ofReal ((R + 1) ^ 2 * Real.exp (-c * R)) * (ENNReal.ofReal (stateWeight z.1))⁻¹ :=
        mul_le_mul (ENNReal.ofReal_le_ofReal hweight) le_rfl zero_le zero_le
      _ = ENNReal.ofReal (binCoefficient c (k + N)) * inverseArrivalBand v ((k + N : ℕ) + 1) ell z := by
        rw [inverseArrivalBand, indicator_of_mem (show z ∈ {z : CostState | R ≤ gapValue v z ∧ gapValue v z ≤ Real.exp 1 * R ∧ stateRatio z.1 < gapValue v z / ell} from hA)]
        have hcoef : (R + 1) ^ 2 * Real.exp (-c * R) = binCoefficient c (k + N) := by
          dsimp [R, binCoefficient]
          ring
        rw [hcoef]
      _ ≤ _ := by
        simpa only [Nat.cast_add,Nat.cast_one] using
          (ENNReal.le_tsum (f := fun k : ℕ => ENNReal.ofReal (binCoefficient c (k+N)) *
            inverseArrivalBand v ((k+N : ℕ)+1) ell z) k)
  · rw [tailReward, indicator_of_notMem (show z ∉ {z : CostState | (N : ℝ) + 1 ≤ gapValue v z ∧ stateRatio z.1 < gapValue v z / ell} from hz)]
    exact zero_le

theorem weighted_tail_of_inverse_bands (μ : Measure CostState) (v ell : ℝ) {C : ℝ≥0∞}
    (hband : ∀ R : ℝ, 0 < R → (∫⁻ z, inverseArrivalBand v R ell z ∂μ) ≤ C * ENNReal.ofReal (R + 1))
    {c : ℝ} (hc : 0 < c) (N : ℕ) :
    (∫⁻ z, tailReward c v ell N z ∂μ) ≤ tailBudget C c N := by
  calc
    _ ≤ ∫⁻ z, ∑' k : ℕ, ENNReal.ofReal (binCoefficient c (k + N)) *
        inverseArrivalBand v ((k + N : ℕ) + 1) ell z ∂μ := lintegral_mono (tailReward_le_band_sum hc v ell N)
    _ = ∑' k : ℕ, ENNReal.ofReal (binCoefficient c (k + N)) *
        (∫⁻ z, inverseArrivalBand v ((k + N : ℕ) + 1) ell z ∂μ) := by
      rw [lintegral_tsum (f := fun (k : ℕ) (z : CostState) => ENNReal.ofReal (binCoefficient c (k + N)) * inverseArrivalBand v (((k + N : ℕ) : ℝ) + 1) ell z) (fun k => (measurable_const.mul (inverseArrivalBand_measurable _ _ _)).aemeasurable)]
      apply tsum_congr
      intro k
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (binCoefficient c (k + N)) *
        (C * ENNReal.ofReal (((k + N : ℕ) : ℝ) + 1 + 1)) := by
      apply ENNReal.tsum_le_tsum
      intro k
      exact mul_le_mul le_rfl (hband _ (by positivity)) zero_le zero_le
    _ = tailBudget C c N := by
      rw [tailBudget, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro k
      have hA : 0 ≤ binCoefficient c (k + N) := by unfold binCoefficient; positivity
      rw [mul_left_comm, ← ENNReal.ofReal_mul hA]
      congr 2
      dsimp [binCoefficient, tailSeries]
      ring

end NumberTheoryLean.WeightedGapTail

end

section

namespace NumberTheoryLean.EvenInverseBands

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open DerivativeWeights TransitionKernels FinitePathMeasures OccupationDecomposition
open CostPrefixTransport RegenerationBandBounds InvariantInverseWeights
open RegeneratingInverseBands FirstStepInverseWeight EvenBandBounds WeightedGapTail

theorem even_inverse_arrival_from_two : ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ s : EvenState, (199 / 100 : ℝ) ≤ s.1 → s.1 ≤ 23 / 10 →
    ∀ v R ell : ℝ, 0 < R → 1 ≤ ell →
      (∫⁻ z, inverseArrivalBand v R ell z ∂prefixOccupation 2 (.inl s, 0)) ≤ C * ENNReal.ofReal R := by
  obtain ⟨B, hB, hb⟩ := even_uniform_band 1
  refine ⟨B * ENNReal.ofReal (2 * Real.exp 1), ENNReal.mul_lt_top hB ENNReal.ofReal_lt_top, ?_⟩
  intro s hsL hsU v R ell hR hell
  calc
    _ ≤ ∫⁻ z, stateBandReward (inverseWeightCutoff (Real.exp 1 * R)) (v - Real.log R - 1) 1 z
        ∂prefixOccupation 2 (.inl s, 0) := lintegral_mono (inverseArrivalBand_le_costBand v hR hell)
    _ ≤ B * ∫⁻ t : State, inverseWeightCutoff (Real.exp 1 * R) t
        ∂Erdos970Dependency.StateKernelInvariance.stateMeasure :=
      hb _ (inverseWeightCutoff_measurable _) _ s hsL hsU
    _ ≤ B * ENNReal.ofReal (2 * (Real.exp 1 * R)) :=
      mul_le_mul le_rfl (inverseWeightCutoff_mass_le (by positivity)) zero_le zero_le
    _ = _ := by
      rw [show 2 * (Real.exp 1 * R) = (2 * Real.exp 1) * R by ring,
        ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.exp 1), mul_assoc]

theorem even_future_inverse_arrival_band : ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ s : EvenState, (199 / 100 : ℝ) ≤ s.1 → s.1 ≤ 23 / 10 →
    ∀ v R ell : ℝ, 0 < R → 1 ≤ ell →
      (∫⁻ z, inverseArrivalBand v R ell z ∂fullOccupation (.inl s, 0)) ≤ C * ENNReal.ofReal R := by
  obtain ⟨B, hB, hb⟩ := even_inverse_arrival_from_two
  refine ⟨ENNReal.ofReal (firstDensityConstant * Real.exp 1) + B,
    ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, hB⟩, ?_⟩
  intro s hsL hsU v R ell hR hell
  rw [fullOccupation_first_and_later, _root_.add_apply, lintegral_add_measure]
  calc
    _ ≤ ENNReal.ofReal (firstDensityConstant * Real.exp 1) * ENNReal.ofReal R + B * ENNReal.ofReal R :=
      add_le_add (first_odd_inverse_arrival_band s hsU v hR hell) (hb s hsL hsU v R ell hR hell)
    _ = _ := (add_mul _ _ _).symm

theorem inverseArrivalBand_le_weight (v R ell : ℝ) (z : CostState) :
    inverseArrivalBand v R ell z ≤ (ENNReal.ofReal (stateWeight z.1))⁻¹ := by
  classical
  unfold inverseArrivalBand
  by_cases hz : R ≤ gapValue v z ∧ gapValue v z ≤ Real.exp 1 * R ∧ stateRatio z.1 < gapValue v z / ell
  · rw [indicator_of_mem (show z ∈ {z | R ≤ gapValue v z ∧ gapValue v z ≤ Real.exp 1 * R ∧ stateRatio z.1 < gapValue v z / ell} from hz)]
  · rw [indicator_of_notMem (show z ∉ {z | R ≤ gapValue v z ∧ gapValue v z ≤ Real.exp 1 * R ∧ stateRatio z.1 < gapValue v z / ell} from hz)]
    exact zero_le

theorem starting_inverse_weight_le (s : EvenState) (hs : s.1 ≤ 23 / 10) :
    (ENNReal.ofReal (stateWeight (.inl s)))⁻¹ ≤ (ENNReal.ofReal (phiEven (23 / 10)))⁻¹ := by
  apply ENNReal.inv_le_inv.mpr
  apply ENNReal.ofReal_le_ofReal
  exact phiEven_strictAntiOn.antitoneOn (by change 1 < s.1; linarith [s.2]) (by norm_num) hs

theorem source_inverse_phi_band : ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ s : EvenState, (199 / 100 : ℝ) ≤ s.1 → s.1 ≤ 23 / 10 →
    ∀ v R ell : ℝ, 0 < R → 1 ≤ ell →
      (∫⁻ z, inverseArrivalBand v R ell z ∂inclusiveOccupation (.inl s, 0)) ≤ C * ENNReal.ofReal (R + 1) := by
  obtain ⟨B, hB, hb⟩ := even_future_inverse_arrival_band
  let D := (ENNReal.ofReal (phiEven (23 / 10)))⁻¹
  have hD : D < ∞ := lt_top_iff_ne_top.mpr
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (phiEven_pos (by norm_num))).ne')
  refine ⟨D + B, ENNReal.add_lt_top.mpr ⟨hD, hB⟩, ?_⟩
  intro s hsL hsU v R ell hR hell
  rw [inclusiveOccupation, _root_.add_apply, lintegral_add_measure, Kernel.id_apply,
    lintegral_dirac' (.inl s, 0) (inverseArrivalBand_measurable v R ell)]
  calc
    _ ≤ D + B * ENNReal.ofReal R := add_le_add
      (le_trans (inverseArrivalBand_le_weight v R ell (.inl s, 0)) (starting_inverse_weight_le s hsU))
      (hb s hsL hsU v R ell hR hell)
    _ ≤ (D + B * ENNReal.ofReal R) + (D * ENNReal.ofReal R + B) := le_add_of_nonneg_right zero_le
    _ = (D + B) * ENNReal.ofReal (R + 1) := by
      rw [ENNReal.ofReal_add hR.le (by norm_num : (0 : ℝ) ≤ 1), ENNReal.ofReal_one]
      ring

theorem source_exponential_reward_tail {c : ℝ} (hc : 0 < c) :
    ∃ b : ℕ → ℝ≥0∞, Tendsto b atTop (𝓝 0) ∧ ∀ N : ℕ, ∀ s : EvenState,
      (199 / 100 : ℝ) ≤ s.1 → s.1 ≤ 23 / 10 → ∀ v ell : ℝ, 1 ≤ ell →
      (∫⁻ z, tailReward c v ell N z ∂inclusiveOccupation (.inl s, 0)) ≤ b N := by
  obtain ⟨C, hC, hb⟩ := source_inverse_phi_band
  refine ⟨tailBudget C c, tailBudget_tendsto_zero hC.ne hc, ?_⟩
  intro N s hsL hsU v ell hell
  exact weighted_tail_of_inverse_bands _ v ell (fun R hR => hb s hsL hsU v R ell hR hell) hc N

end NumberTheoryLean.EvenInverseBands

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_ArrivalKernelGeometry
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.ArrivalKernelGeometry

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostGrouping
open OccupationBoundaries RegeneratingInverseBands KernelDensityBridge
open HarmonicWeightKernel KernelWeightTransform

theorem arrivalSet_eq_cutoff (v : ℝ) {ell : ℝ} (hell : 0 < ell) :
    arrivalSet v ell = {z | stateRatio z.1 < gapValue v z / ell} := by
  ext z
  change ell < gapValue v z / stateRatio z.1 ↔ stateRatio z.1 < gapValue v z / ell
  rw [lt_div_iff₀ (stateRatio_pos z.1), lt_div_iff₀ hell, mul_comm ell (stateRatio z.1)]

theorem gapValue_update (v : ℝ) (z : CostState) (s : State) :
    gapValue v (s, z.2 + cost (stateRatio s)) = nextGap (gapValue v z) (stateRatio s) := by
  rw [nextGap_eq_cost (stateRatio_pos s)]
  change Real.exp (v - (z.2 + cost (stateRatio s))) = Real.exp (v - z.2) * Real.exp (-cost (stateRatio s))
  rw [show v - (z.2 + cost (stateRatio s)) = (v - z.2) + (-cost (stateRatio s)) by ring, Real.exp_add]

end NumberTheoryLean.ArrivalKernelGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_LowStateHorizon
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.LowStateHorizon

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostGrouping
open OccupationBoundaries ArrivalKernelGeometry RegeneratingInverseBands HarmonicWeightKernel

theorem source_horizon_log_cube {B : ℝ} (hB : 2 ≤ Real.log B) :
    ((sourceHorizon ((Real.log B) ^ 2) B : ℕ) : ℝ) ≤ 5 * (Real.log B) ^ 3 := by
  let x := Real.log B
  have hx : 2 ≤ x := hB
  have hpos : 0 ≤ (x ^ 2 + 1) * (x + 2) := by positivity
  have hc := (Nat.ceil_lt_add_one hpos).le
  change ((⌈(x ^ 2 + 1) * (x + 2)⌉₊ + 1 : ℕ) : ℝ) ≤ 5 * x ^ 3
  push_cast
  have h2 : 0 ≤ (x - 2) * x := mul_nonneg (by linarith) (by linarith)
  have h3 : 0 ≤ (x - 2) * x ^ 2 := mul_nonneg (by linarith) (sq_nonneg x)
  nlinarith

end NumberTheoryLean.LowStateHorizon

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeRatioBins
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.chain_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSingletonClassChainState _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeHistories

open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem terminal_append (w : ℝ) (z : Node) (ps qs : List ℕ) :
    terminal w z (ps++qs) = terminal w (terminal w z ps) qs := by
  exact List.foldl_append

namespace History

variable {w ell S : ℝ} {start : Node}

theorem append_node (h : History w ell S start) (p : ℕ) (hp : p ∈ nodeChildren w ell S h.node) :
    (h.append p hp).node = step w h.node p := by
  change terminal w start (h.primes ++ [p]) = _
  rw [terminal_append, terminal_cons, terminal_nil]
  rfl

end History
end NumberTheoryLean.PrimeHistories

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeGridGeometry
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.PrimeKilledChain

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeHistories PrimeRowNormalization

theorem normalizationThreshold_gt_one : 1 < normalizationThreshold :=
  (Classical.choose_spec (Classical.choose_spec retained_row_mass_one_add)).2.1

end NumberTheoryLean.PrimeKilledChain



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_CemeteryHistoryLaw
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.CemeteryKernel

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

theorem complete_isMarkov (K : Kernel α α) (hK : ∀ x, K x univ ≤ 1) : IsMarkovKernel (complete K) := by
  constructor
  intro z
  constructor
  cases z with
  | inl x =>
    rw [complete_live, liveRow_apply, Measure.add_apply, Measure.map_apply measurable_inl MeasurableSet.univ,
      Set.preimage_univ, Measure.smul_apply]
    simp only [measure_univ, smul_eq_mul, mul_one]
    exact add_tsub_cancel_of_le (hK x)
  | inr u =>
    cases u
    change Measure.dirac (dead : Space α) univ = 1
    exact measure_univ

end NumberTheoryLean.CemeteryKernel

end

section

namespace NumberTheoryLean.CemeteryPowers

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open CemeteryKernel

variable {α : Type*} [MeasurableSpace α]

theorem liftReward_measurable {F : α → ℝ≥0∞} (hF : Measurable F) : Measurable (liftReward F) :=
  hF.sumElim measurable_const

theorem row_lift (K : Kernel α α) {F : α → ℝ≥0∞} (hF : Measurable F) (q : Space α) :
    (∫⁻ y,liftReward F y ∂complete K q) = liftReward (fun z => ∫⁻ y,F y ∂K z) q := by
  cases q with
  | inl z =>
    rw [complete_live,liveRow_apply,lintegral_add_measure,
      lintegral_map (liftReward_measurable hF) measurable_inl,
      lintegral_smul_measure,lintegral_dirac' _ (liftReward_measurable hF)]
    simp only [liftReward,Sum.elim_inl,dead,Sum.elim_inr,smul_eq_mul,mul_zero,add_zero]
  | inr u =>
    cases u
    change (∫⁻ y,liftReward F y ∂Measure.dirac dead) = 0
    rw [lintegral_dirac' _ (liftReward_measurable hF)]
    rfl

theorem power_lift (K : Kernel α α) {F : α → ℝ≥0∞} (hF : Measurable F) (n : ℕ) (q : Space α) :
    (∫⁻ y,liftReward F y ∂((complete K)^n) q) = liftReward (fun z => ∫⁻ y,F y ∂(K^n) z) q := by
  induction n generalizing q with
  | zero =>
    change (∫⁻ y,liftReward F y ∂Measure.dirac q) = _
    rw [lintegral_dirac' _ (liftReward_measurable hF)]
    cases q with
    | inl z =>
      change F z = ∫⁻ y,F y ∂Measure.dirac z
      rw [lintegral_dirac' _ hF]
    | inr u => rfl
  | succ n ih =>
    have hp : (complete K)^(n+1) = ((complete K)^n) ∘ₖ complete K := pow_succ _ _
    have hl : K^(n+1) = (K^n) ∘ₖ K := pow_succ _ _
    rw [hp,Kernel.lintegral_comp _ _ _ (liftReward_measurable hF)]
    calc
      _ = ∫⁻ y,liftReward (fun z => ∫⁻ a,F a ∂(K^n) z) y ∂complete K q := lintegral_congr ih
      _ = liftReward (fun y => ∫⁻ z,∫⁻ a,F a ∂(K^n) z ∂K y) q := row_lift K hF.lintegral_kernel q
      _ = _ := by
        cases q with
        | inl z =>
          change _ = ∫⁻ y,F y ∂(K^(n+1)) z
          rw [hl,Kernel.lintegral_comp _ _ _ hF]
          rfl
        | inr u => rfl

end NumberTheoryLean.CemeteryPowers

end

section

namespace NumberTheoryLean.CemeteryHistoryMap

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open CemeteryKernel FiniteHistoryTransport

variable {X : Type*} [MeasurableSpace X]
variable (K : Kernel X X) [IsMarkovKernel K] {E : Set X} (hE : MeasurableSet E)

instance restricted_complete_markov : IsMarkovKernel (complete (K.restrict hE)) := by
  apply complete_isMarkov
  intro x
  rw [Kernel.restrict_apply,Measure.restrict_apply_univ]
  exact (measure_mono (subset_univ E)).trans_eq (measure_univ (μ := K x))

end NumberTheoryLean.CemeteryHistoryMap

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CompletedParentInterval
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ContinuousKilledBins

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PairedCostGrouping ArrivalKernelGeometry
open LowStateHorizon RegeneratingInverseBands KernelDensityBridge ContinuousRatioBins

instance continuousChain_isMarkov (v ell S : ℝ) : IsMarkovKernel (continuousChain v ell S) := by
  apply CemeteryKernel.complete_isMarkov
  intro z
  rw [lowKernel, Kernel.restrict_apply, Measure.restrict_apply_univ]
  calc
    _ ≤ costKernel z univ := measure_mono (subset_univ _)
    _ = 1 := measure_univ

end NumberTheoryLean.ContinuousKilledBins

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CrossingBandGeometry
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.NearbyParentGeometry

open FinitePathGeometry OccupationBoundaries

theorem log_stability {m x y : ℝ} (hm : 0 < m) (hx : m ≤ x) (hy : m ≤ y) :
    |Real.log x-Real.log y| ≤ |x-y|/m := by
  wlog hxy : y ≤ x generalizing x y
  · simpa only [abs_sub_comm] using this hy hx (le_of_not_ge hxy)
  have hx0 := hm.trans_le hx
  have hy0 := hm.trans_le hy
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hy0 hxy)), abs_of_nonneg (sub_nonneg.mpr hxy)]
  have h := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
  rw [Real.log_div hx0.ne' hy0.ne'] at h
  calc
    Real.log x-Real.log y ≤ (x-y)/y := by
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      field_simp
    _ ≤ (x-y)/m := div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hm hy

theorem cost_stability {s t : ℝ} (hs : (1/2:ℝ) ≤ s) (ht : (1/2:ℝ) ≤ t) :
    |cost s-cost t| ≤ 4*|s-t| := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have h1 := log_stability (m:=1/2) (by norm_num) hs ht
  have h2 := log_stability (m:=1/2) (x:=s+1) (y:=t+1) (by norm_num) (by linarith) (by linarith)
  have heq : cost s-cost t = (Real.log (s+1)-Real.log (t+1))-(Real.log s-Real.log t) := by
    linarith [cost_add_log hs0, cost_add_log ht0]
  rw [heq]
  calc
    _ ≤ |Real.log (s+1)-Real.log (t+1)|+|Real.log s-Real.log t| := abs_sub _ _
    _ ≤ 4*|s-t| := by
      simp only [add_sub_add_right_eq_sub] at h2
      linarith

theorem log_gap_relative {r q d : ℝ} (hr : 0 < r) (hq : 0 < q)
    (hd : |Real.log r-Real.log q| ≤ d) : r ≤ Real.exp d*q ∧ q ≤ Real.exp d*r := by
  have h1 := Real.exp_le_exp.mpr (abs_le.mp hd).2
  have h2 := Real.exp_le_exp.mpr (show Real.log q-Real.log r ≤ d by linarith [(abs_le.mp hd).1])
  rw [Real.exp_sub,Real.exp_log hr,Real.exp_log hq] at h1
  rw [Real.exp_sub,Real.exp_log hq,Real.exp_log hr] at h2
  exact ⟨(div_le_iff₀ hq).mp h1,(div_le_iff₀ hr).mp h2⟩

theorem log_gap_step {r q s t d e : ℝ} (hr : 0 < r) (hq : 0 < q)
    (hs : (1/2:ℝ) ≤ s) (ht : (1/2:ℝ) ≤ t)
    (hd : |Real.log r-Real.log q| ≤ d) (he : |s-t| ≤ e) :
    |Real.log (nextGap r s)-Real.log (nextGap q t)| ≤ d+4*e := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  rw [nextGap_eq_cost hs0,nextGap_eq_cost ht0,Real.log_mul hr.ne' (Real.exp_pos _).ne',
    Real.log_mul hq.ne' (Real.exp_pos _).ne',Real.log_exp,Real.log_exp]
  have ha := abs_sub (Real.log r-Real.log q) (cost s-cost t)
  have hc := cost_stability hs ht
  have heq : Real.log r + -cost s-(Real.log q + -cost t) =
      (Real.log r-Real.log q)-(cost s-cost t) := by ring
  rw [heq]
  linarith

end NumberTheoryLean.NearbyParentGeometry



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_MeshBoundaryGeometry
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.MeshRatioLabels

open Set MeasureTheory

theorem ratioLabel_val {S h t : ℝ} (hh : 0 < h) (ht : t ≤ S) :
    (ratioLabel S h t).val = ⌊t/h⌋₊ := by
  rw [ratioLabel,ite_eq_left ht,Fin.val_ofNat]
  apply Nat.mod_eq_of_lt
  have hb : ⌊t/h⌋₊ ≤ binCount S h := Nat.floor_mono (div_le_div_of_nonneg_right ht hh.le)
  omega

theorem ratioLabel_ne_cemetery {S h t : ℝ} (hh : 0 < h) (ht : t ≤ S) :
    ratioLabel S h t ≠ cemeteryLabel S h := by
  intro heq
  have he := congrArg Fin.val heq
  rw [ratioLabel_val hh ht] at he
  change ⌊t/h⌋₊ = binCount S h+1 at he
  have hb : ⌊t/h⌋₊ ≤ binCount S h := Nat.floor_mono (div_le_div_of_nonneg_right ht hh.le)
  omega

theorem ratioLabel_eq_iff {S h t : ℝ} (hh : 0 < h) (ht0 : 0 ≤ t) (htS : t ≤ S) (j : Label S h) :
    ratioLabel S h t = j ↔ (j.val : ℝ)*h ≤ t ∧ t < ((j.val : ℝ)+1)*h := by
  rw [Fin.ext_iff,ratioLabel_val hh htS,Nat.floor_eq_iff (div_nonneg ht0 hh.le),le_div_iff₀ hh,div_lt_iff₀ hh]

theorem matching_ratios_close {S h u v : ℝ} (hh : 0 < h) (hu0 : 0 ≤ u) (hv0 : 0 ≤ v)
    (huS : u ≤ S) (hvS : v ≤ S) (heq : ratioLabel S h u = ratioLabel S h v) : |u-v| < h := by
  have hu := (ratioLabel_eq_iff hh hu0 huS (ratioLabel S h v)).mp heq
  have hv := (ratioLabel_eq_iff hh hv0 hvS (ratioLabel S h v)).mp rfl
  rw [abs_lt]
  constructor <;> nlinarith [hu.1,hu.2,hv.1,hv.2]

end NumberTheoryLean.MeshRatioLabels

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_ActualCouplingUpdates
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Finset
open scoped BigOperators
namespace Erdos970Dependency.MaximalCoupling

variable {ι : Type*} [Fintype ι]
attribute [local instance] Classical.propDecidable

omit [Fintype ι] in
theorem common_nonneg {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (i : ι) :
    0 ≤ common a b i := le_min (ha i) (hb i)

omit [Fintype ι] in
theorem leftRemainder_nonneg (a b : ι → ℝ) (i : ι) : 0 ≤ leftRemainder a b i :=
  sub_nonneg.mpr (min_le_left _ _)
omit [Fintype ι] in
theorem rightRemainder_nonneg (a b : ι → ℝ) (i : ι) : 0 ≤ rightRemainder a b i :=
  sub_nonneg.mpr (min_le_right _ _)

theorem sum_leftRemainder {a b : ι → ℝ} (ha : ∑ i, a i = 1) :
    ∑ i, leftRemainder a b i = residual a b := by simp only [leftRemainder, sum_sub_distrib, ha, residual]
theorem sum_rightRemainder {a b : ι → ℝ} (hb : ∑ i, b i = 1) :
    ∑ i, rightRemainder a b i = residual a b := by simp only [rightRemainder, sum_sub_distrib, hb, residual]

theorem residual_nonneg {a b : ι → ℝ} (ha : ∑ i, a i = 1) : 0 ≤ residual a b := by
  rw [← sum_leftRemainder ha]
  exact sum_nonneg (fun i _ => leftRemainder_nonneg a b i)

theorem leftRemainder_zero {a b : ι → ℝ} (ha : ∑ i, a i = 1) (hr : residual a b = 0) (i : ι) :
    leftRemainder a b i = 0 := by
  have h := single_le_sum (fun j _ => leftRemainder_nonneg a b j) (mem_univ i)
  rw [sum_leftRemainder ha, hr] at h
  exact le_antisymm h (leftRemainder_nonneg a b i)
theorem rightRemainder_zero {a b : ι → ℝ} (hb : ∑ i, b i = 1) (hr : residual a b = 0) (i : ι) :
    rightRemainder a b i = 0 := by
  have h := single_le_sum (fun j _ => rightRemainder_nonneg a b j) (mem_univ i)
  rw [sum_rightRemainder hb, hr] at h
  exact le_antisymm h (rightRemainder_nonneg a b i)

theorem matrix_nonneg {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hsa : ∑ i, a i = 1) (i j : ι) : 0 ≤ matrix a b i j := by
  unfold matrix
  apply add_nonneg
  · split_ifs <;> first | exact common_nonneg ha hb i | exact le_rfl
  · split_ifs
    · exact le_rfl
    · exact div_nonneg (mul_nonneg (leftRemainder_nonneg a b i) (rightRemainder_nonneg a b j)) (residual_nonneg hsa)

theorem row_sum {a b : ι → ℝ} (ha : ∑ i, a i = 1) (hb : ∑ i, b i = 1) (i : ι) :
    ∑ j, matrix a b i j = a i := by
  classical
  by_cases hr : residual a b = 0
  · have hz := leftRemainder_zero ha hr i
    simp only [matrix, ite_eq_left hr, add_zero]
    simp only [sum_ite_eq, mem_univ, ite_true, if_true]
    unfold leftRemainder at hz
    linarith
  · simp only [matrix, ite_eq_right hr, sum_add_distrib]
    rw [sum_ite_eq]
    simp only [mem_univ, ite_true, if_true]
    rw [← sum_div, ← mul_sum, sum_rightRemainder hb]
    rw [mul_div_cancel_right₀ _ hr]
    unfold leftRemainder
    ring

theorem column_sum {a b : ι → ℝ} (ha : ∑ i, a i = 1) (hb : ∑ i, b i = 1) (j : ι) :
    ∑ i, matrix a b i j = b j := by
  classical
  by_cases hr : residual a b = 0
  · have hz := rightRemainder_zero hb hr j
    simp only [matrix, ite_eq_left hr, add_zero]
    simp only [sum_ite_eq', mem_univ, ite_true, if_true]
    unfold rightRemainder at hz
    linarith
  · simp only [matrix, ite_eq_right hr, sum_add_distrib]
    rw [sum_ite_eq']
    simp only [mem_univ, ite_true, if_true]
    rw [← sum_div, ← sum_mul, sum_leftRemainder ha]
    rw [mul_div_cancel_left₀ _ hr]
    unfold rightRemainder
    ring

end Erdos970Dependency.MaximalCoupling

end

section

namespace NumberTheoryLean.KernelBinConditioning

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem conditional_apply (K : Kernel α β) {B : Set β} (hB : MeasurableSet B) (default : β) (x : α) :
    conditional K hB default x = if K x B = 0 then Measure.dirac default else (K x B)⁻¹ • (K x).restrict B := rfl

instance conditional_isMarkov (K : Kernel α β) [IsMarkovKernel K] {B : Set β}
    (hB : MeasurableSet B) (default : β) : IsMarkovKernel (conditional K hB default) := by
  constructor
  intro x
  constructor
  classical
  rw [conditional_apply]
  by_cases hx : K x B = 0
  · rw [ite_eq_left hx]
    exact measure_univ
  · rw [ite_eq_right hx, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hx (measure_ne_top _ _)

theorem weighted_conditional (K : Kernel α β) [IsMarkovKernel K] {B : Set β}
    (hB : MeasurableSet B) (default : β) (x : α) :
    (K x B) • conditional K hB default x = (K x).restrict B := by
  classical
  rw [conditional_apply]
  by_cases hx : K x B = 0
  · rw [ite_eq_left hx, hx, zero_smul]
    exact (Measure.restrict_eq_zero.mpr hx).symm
  · rw [ite_eq_right hx, smul_smul, ENNReal.mul_inv_cancel hx (measure_ne_top _ _), one_smul]

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem labelMass_measurable (K : Kernel α β) {label : β → ι} (hl : Measurable label) (i : ι) :
    Measurable (fun x => labelMass K label x i) :=
  ENNReal.measurable_toReal.comp (K.measurable_coe (hl (measurableSet_singleton i)))

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
theorem labelMass_nonneg (K : Kernel α β) (label : β → ι) (x : α) (i : ι) :
    0 ≤ labelMass K label x i := ENNReal.toReal_nonneg

variable [Fintype ι]

theorem labelMass_sum (K : Kernel α β) [IsMarkovKernel K] {label : β → ι}
    (hl : Measurable label) (x : α) : ∑ i, labelMass K label x i = 1 := by
  have h := sum_measure_preimage_singleton (μ := K x) (Finset.univ : Finset ι)
    (fun i _ => hl (measurableSet_singleton i))
  simp only [Finset.coe_univ, Set.preimage_univ, measure_univ] at h
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _), ENNReal.toReal_one] at hr
  exact hr

theorem conditional_mixture (K : Kernel α β) [IsMarkovKernel K] {label : β → ι}
    (hl : Measurable label) (default : β) (x : α) :
    (∑ i, (K x (label ⁻¹' {i})) • conditional K (hl (measurableSet_singleton i)) default x) = K x := by
  simp_rw [weighted_conditional]
  apply Measure.ext
  intro B hB
  rw [Measure.finsetSum_apply]
  simp_rw [Measure.restrict_apply hB]
  have h := sum_measure_preimage_singleton (μ := (K x).restrict B) (Finset.univ : Finset ι)
    (fun i _ => hl (measurableSet_singleton i))
  simp only [Finset.coe_univ, Set.preimage_univ, Measure.restrict_apply_univ] at h
  have heq : ∀ i : ι, (K x).restrict B (label ⁻¹' {i}) = K x (B ∩ label ⁻¹' {i}) := by
    intro i
    rw [Measure.restrict_apply (hl (measurableSet_singleton i)), Set.inter_comm]
  simp_rw [heq] at h
  exact h

end NumberTheoryLean.KernelBinConditioning

end

section

namespace NumberTheoryLean.KernelCouplingWeights

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open KernelBinConditioning Erdos970Dependency.MaximalCoupling
attribute [local instance] Classical.propDecidable

variable {α β γ ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem weight_measurable (K : Kernel α β) (L : Kernel α γ) {f : β → ι} {g : γ → ι}
    (hf : Measurable f) (hg : Measurable g) (i j : ι) : Measurable (fun x => weight K L f g x i j) := by
  classical
  have ha := labelMass_measurable K hf
  have hb := labelMass_measurable L hg
  have hc (i : ι) : Measurable (fun x => common (labelMass K f x) (labelMass L g x) i) := (ha i).min (hb i)
  have hr : Measurable (fun x => residual (labelMass K f x) (labelMass L g x)) :=
    measurable_const.sub (Finset.measurable_sum univ (fun i _ => hc i))
  have hl : Measurable (fun x => leftRemainder (labelMass K f x) (labelMass L g x) i) := (ha i).sub (hc i)
  have hh : Measurable (fun x => rightRemainder (labelMass K f x) (labelMass L g x) j) := (hb j).sub (hc j)
  have hd : Measurable (fun x => if i = j then common (labelMass K f x) (labelMass L g x) i else 0) := by
    by_cases hij : i = j
    · simpa only [ite_eq_left hij] using hc i
    · simp only [ite_eq_right hij]
      exact measurable_const
  exact hd.add (Measurable.ite (measurableSet_eq_fun hr measurable_const) measurable_const ((hl.mul hh).div hr))

theorem weight_joint_measurable (K : Kernel α β) (L : Kernel α γ) {f : β → ι} {g : γ → ι}
    (hf : Measurable f) (hg : Measurable g) (i j : ι) :
    Measurable (Function.uncurry (fun (x : α) (_ : β × γ) => ENNReal.ofReal (weight K L f g x i j))) :=
  (ENNReal.measurable_ofReal.comp (weight_measurable K L hf hg i j)).comp measurable_fst

variable (K : Kernel α β) (L : Kernel α γ) [IsMarkovKernel K] [IsMarkovKernel L]
variable {f : β → ι} {g : γ → ι} (hf : Measurable f) (hg : Measurable g)
include hf hg

omit hg [IsMarkovKernel L] in
theorem weight_nonnegative (x : α) (i j : ι) : 0 ≤ weight K L f g x i j :=
  matrix_nonneg (labelMass_nonneg K f x) (labelMass_nonneg L g x) (labelMass_sum K hf x) i j

theorem weight_row (x : α) (i : ι) : ∑ j, weight K L f g x i j = labelMass K f x i :=
  row_sum (labelMass_sum K hf x) (labelMass_sum L hg x) i

theorem weight_column (x : α) (j : ι) : ∑ i, weight K L f g x i j = labelMass L g x j :=
  column_sum (labelMass_sum K hf x) (labelMass_sum L hg x) j

theorem weight_row_ofReal (x : α) (i : ι) :
    ∑ j, ENNReal.ofReal (weight K L f g x i j) = K x (f ⁻¹' {i}) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => weight_nonnegative K L (g := g) hf x i j), weight_row K L hf hg]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

theorem weight_column_ofReal (x : α) (j : ι) :
    ∑ i, ENNReal.ofReal (weight K L f g x i j) = L x (g ⁻¹' {j}) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => weight_nonnegative K L (g := g) hf x i j), weight_column K L hf hg]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

theorem weight_total_ofReal (x : α) : ∑ i, ∑ j, ENNReal.ofReal (weight K L f g x i j) = 1 := by
  simp_rw [weight_row_ofReal K L hf hg]
  have h := sum_measure_preimage_singleton (μ := K x) (Finset.univ : Finset ι)
    (fun i _ => hf (measurableSet_singleton i))
  simpa only [Finset.coe_univ, Set.preimage_univ, measure_univ] using h

end NumberTheoryLean.KernelCouplingWeights

end

section

namespace NumberTheoryLean.KernelCouplingLift

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open KernelBinConditioning KernelCouplingWeights

variable {α β γ ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable (K : Kernel α β) (L : Kernel α γ) [IsMarkovKernel K] [IsMarkovKernel L]
variable {f : β → ι} {g : γ → ι} (hf : Measurable f) (hg : Measurable g) (dβ : β) (dγ : γ)

theorem component_apply (i j : ι) (x : α) :
    component K L hf hg dβ dγ i j x = ENNReal.ofReal (weight K L f g x i j) •
      (conditional K (hf (measurableSet_singleton i)) dβ x).prod
        (conditional L (hg (measurableSet_singleton j)) dγ x) := by
  rw [component, Kernel.withDensity_apply _ (weight_joint_measurable K L hf hg i j) x,
    Kernel.prod_apply, withDensity_const]

theorem coupled_apply_set (x : α) {B : Set (β × γ)} (hB : MeasurableSet B) :
    coupled K L hf hg dβ dγ x B = ∑ i, ∑ j, ENNReal.ofReal (weight K L f g x i j) *
      ((conditional K (hf (measurableSet_singleton i)) dβ x).prod
        (conditional L (hg (measurableSet_singleton j)) dγ x)) B := by
  rw [coupled, Kernel.sum_apply' _ _ hB, tsum_fintype, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [component_apply, Measure.smul_apply, smul_eq_mul]

instance coupled_isMarkov : IsMarkovKernel (coupled K L hf hg dβ dγ) := by
  constructor
  intro x
  constructor
  rw [coupled_apply_set K L hf hg dβ dγ x MeasurableSet.univ]
  simp only [measure_univ, mul_one]
  exact weight_total_ofReal K L hf hg x

theorem coupled_map_fst (x : α) :
    (coupled K L hf hg dβ dγ x).map Prod.fst = K x := by
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply measurable_fst hB, coupled_apply_set K L hf hg dβ dγ x (measurable_fst hB)]
  have hpre : (Prod.fst ⁻¹' B : Set (β × γ)) = B ×ˢ univ := by ext p; simp
  rw [hpre]
  simp only [Measure.prod_prod, measure_univ, mul_one]
  simp_rw [← Finset.sum_mul, weight_row_ofReal K L hf hg]
  have h := congrArg (fun μ : Measure β => μ B) (conditional_mixture K hf dβ x)
  simpa only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul] using h

theorem coupled_map_snd (x : α) :
    (coupled K L hf hg dβ dγ x).map Prod.snd = L x := by
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply measurable_snd hB, coupled_apply_set K L hf hg dβ dγ x (measurable_snd hB)]
  have hpre : (Prod.snd ⁻¹' B : Set (β × γ)) = univ ×ˢ B := by ext p; simp
  rw [hpre]
  simp only [Measure.prod_prod, measure_univ, one_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, weight_column_ofReal K L hf hg]
  have h := congrArg (fun μ : Measure γ => μ B) (conditional_mixture L hg dγ x)
  simpa only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul] using h

end NumberTheoryLean.KernelCouplingLift

end

section

namespace NumberTheoryLean.ActualProcessCoupling

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ContinuousKilledBins MeshRatioLabels KernelCouplingLift KernelBinConditioning

instance continuousParent_isMarkov (w ell S : ℝ) (start : Node) (v : ℝ) :
    IsMarkovKernel (continuousParent w ell S start v) := by unfold continuousParent; infer_instance

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

instance jointKernel_isMarkov (v mesh : ℝ) : IsMarkovKernel (jointKernel hw hell hS0 hS hr hs hsS v mesh) := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  unfold jointKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem jointKernel_left (v mesh : ℝ) (p : ChainState w ell S start) (z : CemeteryKernel.Space CostState) :
    (jointKernel hw hell hS0 hS hr hs hsS v mesh (p,z)).map Prod.fst = chain w ell S start p := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  exact coupled_map_fst (primeParent w ell S start) (continuousParent w ell S start v)
    (primeLabel_measurable w ell S mesh start) (continuousLabel_measurable S mesh)
    none CemeteryKernel.dead (p,z)

theorem jointKernel_right (v mesh : ℝ) (p : ChainState w ell S start) (z : CemeteryKernel.Space CostState) :
    (jointKernel hw hell hS0 hS hr hs hsS v mesh (p,z)).map Prod.snd = continuousChain v ell S z := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  exact coupled_map_snd (primeParent w ell S start) (continuousParent w ell S start v)
    (primeLabel_measurable w ell S mesh start) (continuousLabel_measurable S mesh)
    none CemeteryKernel.dead (p,z)

end NumberTheoryLean.ActualProcessCoupling

end

section

namespace NumberTheoryLean.ActualCouplingSupport

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ContinuousKilledBins MeshRatioLabels ActualProcessCoupling LowStateHorizon

variable {w ell S : ℝ} {start : Node}

theorem badRatio_measurable (S : ℝ) : MeasurableSet (badRatio S) :=
  (measurableSet_le (stateRatio_measurable.comp measurable_fst) measurable_const).compl

theorem unsupported_eq (S : ℝ) :
    {q : CemeteryKernel.Space CostState | ¬continuousSupported S q} = Sum.inl '' badRatio S := by
  ext q
  cases q <;> simp [continuousSupported,badRatio]

theorem continuousSupported_measurable (S : ℝ) : MeasurableSet {q | continuousSupported S q} := by
  have h : MeasurableSet {q : CemeteryKernel.Space CostState | ¬continuousSupported S q} := by
    rw [unsupported_eq]
    exact (badRatio_measurable S).inl_image
  simpa only [Set.compl_ofPred, not_not] using h.compl

theorem continuous_supported (v ell S : ℝ) (q : CemeteryKernel.Space CostState) :
    ∀ᵐ y ∂continuousChain v ell S q, continuousSupported S y := by
  apply ae_iff.mpr
  rw [unsupported_eq]
  cases q with
  | inl z =>
    rw [continuousChain, CemeteryKernel.complete_live_mass _ _ (badRatio_measurable S),
      lowKernel, Kernel.restrict_apply, Measure.restrict_apply (badRatio_measurable S)]
    have he : badRatio S ∩ lowDomain v ell S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hy.1 hy.2.2
    rw [he,measure_empty]
  | inr u =>
    cases u
    change Measure.dirac (CemeteryKernel.dead : CemeteryKernel.Space CostState) (Sum.inl '' badRatio S) = 0
    rw [Measure.dirac_apply' _ (badRatio_measurable S).inl_image, indicator_of_notMem (by simp [CemeteryKernel.dead])]

theorem labels_match_outcomes {mesh : ℝ} (hm : 0 < mesh)
    (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)
    (p : ChainState w ell S start) (z : CemeteryKernel.Space CostState)
    (hSup : continuousSupported S z) (hlabel : primeLabel w ell S mesh start p = continuousLabel S mesh z) :
    matchedOutcome mesh (p,z) := by
  cases p with
  | none =>
    cases z with
    | inl z =>
      change cemeteryLabel S mesh = ratioLabel S mesh (stateRatio z.1) at hlabel
      exact False.elim (ratioLabel_ne_cemetery hm hSup hlabel.symm)
    | inr u => trivial
  | some h =>
    have hpos := valid_pos (terminal_valid hs h.admissible)
    have hbound := terminal_ratio_le hsS h.admissible
    cases z with
    | inl z =>
      change ratioLabel S mesh h.node.ratio = ratioLabel S mesh (stateRatio z.1) at hlabel
      exact matching_ratios_close hm hpos.le (OccupationBoundaries.stateRatio_pos z.1).le hbound hSup hlabel
    | inr u =>
      change ratioLabel S mesh h.node.ratio = cemeteryLabel S mesh at hlabel
      exact False.elim (ratioLabel_ne_cemetery hm hbound hlabel)

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem joint_continuous_supported (v mesh : ℝ) (p : ChainState w ell S start) (z : CemeteryKernel.Space CostState) :
    ∀ᵐ q ∂jointKernel hw hell hS0 hS hr hs hsS v mesh (p,z), continuousSupported S q.2 := by
  have h : ∀ᵐ q ∂(jointKernel hw hell hS0 hS hr hs hsS v mesh (p,z)).map Prod.snd, continuousSupported S q := by
    rw [jointKernel_right hw hell hS0 hS hr hs hsS]
    exact continuous_supported v ell S z
  exact (ae_map_iff measurable_snd.aemeasurable (continuousSupported_measurable S)).mp h

theorem joint_matching_control (v : ℝ) {mesh : ℝ} (hm : 0 < mesh)
    (p : ChainState w ell S start) (z : CemeteryKernel.Space CostState) :
    ∀ᵐ q ∂jointKernel hw hell hS0 hS hr hs hsS v mesh (p,z),
      primeLabel w ell S mesh start q.1 = continuousLabel S mesh q.2 → matchedOutcome mesh q := by
  filter_upwards [joint_continuous_supported hw hell hS0 hS hr hs hsS v mesh p z] with q hq
  intro heq
  exact labels_match_outcomes hm hs hsS q.1 q.2 hq heq

end NumberTheoryLean.ActualCouplingSupport

end

section

namespace NumberTheoryLean.ActualCouplingFinite

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ContinuousKilledBins PrimeChainHorizon LowStateHorizon

section Generic
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable (K : Kernel α α) (L : Kernel β β)
variable {f : α → β} (hf : Measurable f)

include hf

theorem map_power_of_step (hstep : ∀ x, (K x).map f = L (f x)) (n : ℕ) (x : α) :
    ((K^n) x).map f = (L^n) (f x) := by
  let P : Kernel α β := Kernel.deterministic f hf
  have hinter : P ∘ₖ K = L ∘ₖ P := by
    rw [show P = Kernel.deterministic f hf from rfl, Kernel.deterministic_comp_eq_map,
      Kernel.comp_deterministic_eq_comap]
    ext x : 1
    rw [Kernel.map_apply _ hf,Kernel.comap_apply]
    exact hstep x
  have hpow : ∀ n, P ∘ₖ (K^n) = (L^n) ∘ₖ P := by
    intro n
    induction n with
    | zero =>
      change P ∘ₖ (Kernel.id : Kernel α α) = Kernel.id ∘ₖ P
      rw [Kernel.comp_id,Kernel.id_comp]
    | succ n ih =>
      have hp : K^(n+1) = (K^n) ∘ₖ K := pow_succ _ _
      have hq : L^(n+1) = (L^n) ∘ₖ L := pow_succ _ _
      rw [hp,hq,← Kernel.comp_assoc,ih,Kernel.comp_assoc,hinter,← Kernel.comp_assoc]
  have h := hpow n
  rw [show P = Kernel.deterministic f hf from rfl,Kernel.deterministic_comp_eq_map,
    Kernel.comp_deterministic_eq_comap] at h
  have hx := congrArg (fun M : Kernel α β => M x) h
  rwa [Kernel.map_apply _ hf,Kernel.comap_apply] at hx
end Generic

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

instance jointKernel_pow_markov (v mesh : ℝ) (n : ℕ) :
    IsMarkovKernel ((jointKernel hw hell hS0 hS hr hs hsS v mesh)^n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.id : Kernel (JointState w ell S start) (JointState w ell S start)); infer_instance
  | succ n ih =>
    let := ih
    have hp : (jointKernel hw hell hS0 hS hr hs hsS v mesh)^(n+1) =
      (jointKernel hw hell hS0 hS hr hs hsS v mesh) ∘ₖ ((jointKernel hw hell hS0 hS hr hs hsS v mesh)^n) := pow_succ' _ _
    rw [hp]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem joint_power_right (v mesh : ℝ) (n : ℕ) (q : JointState w ell S start) :
    (((jointKernel hw hell hS0 hS hr hs hsS v mesh)^n) q).map Prod.snd =
      ((continuousChain v ell S)^n) q.2 :=
  map_power_of_step _ _ measurable_snd
    (fun x => jointKernel_right hw hell hS0 hS hr hs hsS v mesh x.1 x.2) n q

instance jointPathLaw_probability (v mesh : ℝ) (z : CostState) (n : ℕ) :
    IsProbabilityMeasure (jointPathLaw hw hell hS0 hS hr hs hsS v mesh z n) := by
  unfold jointPathLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem jointPathLaw_continuous (v mesh : ℝ) (z : CostState) (n : ℕ) :
    (jointPathLaw hw hell hS0 hS hr hs hsS v mesh z n).map Prod.snd =
      ((continuousChain v ell S)^n) (.inl z) :=
  joint_power_right hw hell hS0 hS hr hs hsS v mesh n (some History.empty,.inl z)

end NumberTheoryLean.ActualCouplingFinite

end

section

namespace NumberTheoryLean.ActualCouplingUpdates

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualCouplingSupport ContinuousKilledBins
open LowStateHorizon NearbyParentGeometry ArrivalKernelGeometry RegeneratingInverseBands
open PrimeTiltGeometry KernelDensityBridge PairedCostGrouping

variable {w ell S : ℝ} {start : Node}

theorem liftPredicate_measurable {α : Type*} [MeasurableSpace α] {P : α → Prop}
    (hP : MeasurableSet {x | P x}) : MeasurableSet {x | liftPredicate P x} := by
  exact measurableSet_sum_iff.mpr ⟨hP,MeasurableSet.univ⟩

theorem complete_ae {α : Type*} [MeasurableSpace α] (K : Kernel α α) (x : α)
    {P : α → Prop} (hP : MeasurableSet {y | P y}) (h : ∀ᵐ y ∂K x, P y) :
    ∀ᵐ y ∂CemeteryKernel.complete K (.inl x), liftPredicate P y := by
  rw [CemeteryKernel.complete_live,CemeteryKernel.liveRow_apply,ae_add_measure_iff]
  constructor
  · exact (ae_map_iff measurable_inl.aemeasurable (liftPredicate_measurable hP)).mpr h
  · apply Measure.ae_smul_measure _ _
    exact (ae_dirac_iff (liftPredicate_measurable hP)).mpr trivial

theorem prime_follows (h : History w ell S start) :
    ∀ᵐ k ∂chain w ell S start (some h), primeFollows h k := by
  classical
  apply ae_iff.mpr
  simp [chain_some,completedLaw,liveLaw,primeFollows]
  intro p hp
  exact Or.inr ⟨p,hp,rfl⟩

theorem side_set_measurable (i : Side) : MeasurableSet {s : State | stateSide s = i} := by
  cases i <;> apply measurableSet_sum_iff.mpr <;> simp [stateSide]

theorem stateKernel_side (s : State) :
    ∀ᵐ t ∂stateKernel s, stateSide t = (stateSide s).flip := by
  cases s with
  | inl s =>
    change ∀ᵐ t ∂evenBranch s, stateSide t = Side.odd
    rw [evenBranch,Kernel.map_apply _ measurable_inr]
    exact (ae_map_iff measurable_inr.aemeasurable (side_set_measurable .odd)).mpr
      (Filter.Eventually.of_forall (fun _ => rfl))
  | inr s =>
    change ∀ᵐ t ∂oddBranch s, stateSide t = Side.even
    rw [oddBranch,Kernel.map_apply _ measurable_inl]
    exact (ae_map_iff measurable_inl.aemeasurable (side_set_measurable .even)).mpr
      (Filter.Eventually.of_forall (fun _ => rfl))

theorem continuousFollows_measurable (z : CostState) : MeasurableSet {y | continuousFollows z y} :=
  (measurableSet_eq_fun measurable_snd
    (measurable_const.add (cost_measurable.comp (stateRatio_measurable.comp measurable_fst)))).inter
    (measurable_fst (side_set_measurable (stateSide z.1).flip))

theorem costKernel_follows (z : CostState) : ∀ᵐ y ∂costKernel z, continuousFollows z y := by
  have hm : Measurable (fun s : State => (s,z.2+cost (stateRatio s))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  rw [costKernel_eq_map]
  apply (ae_map_iff hm.aemeasurable (continuousFollows_measurable z)).mpr
  filter_upwards [stateKernel_side z.1] with y hy
  exact ⟨rfl,hy⟩

theorem continuous_follows (v ell S : ℝ) (z : CostState) :
    ∀ᵐ y ∂continuousChain v ell S (.inl z), liftPredicate (continuousFollows z) y := by
  apply complete_ae _ _ (continuousFollows_measurable z)
  exact ae_restrict_of_ae (costKernel_follows z)

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem joint_follows (v mesh : ℝ) (h : History w ell S start) (z : CostState) :
    ∀ᵐ q ∂jointKernel hw hell hS0 hS hr hs hsS v mesh (some h,.inl z),
      primeFollows h q.1 ∧ liftPredicate (continuousFollows z) q.2 := by
  have hL : ∀ᵐ p ∂(jointKernel hw hell hS0 hS hr hs hsS v mesh (some h,.inl z)).map Prod.fst,
      primeFollows h p := by
    rw [jointKernel_left hw hell hS0 hS hr hs hsS]
    exact prime_follows h
  have hR : ∀ᵐ y ∂(jointKernel hw hell hS0 hS hr hs hsS v mesh (some h,.inl z)).map Prod.snd,
      liftPredicate (continuousFollows z) y := by
    rw [jointKernel_right hw hell hS0 hS hr hs hsS]
    exact continuous_follows v ell S z
  exact ((ae_map_iff measurable_fst.aemeasurable (show MeasurableSet {p | primeFollows h p} from trivial)).mp hL).and
    ((ae_map_iff measurable_snd.aemeasurable (liftPredicate_measurable (continuousFollows_measurable z))).mp hR)

include hell hr hs

theorem prime_step_gap (h : History w ell S start) (p : ℕ) (hp : p ∈ nodeChildren w ell S h.node) :
    (h.append p hp).node.gap = nextGap h.node.gap (h.append p hp).node.ratio := by
  have hrg := terminal_gap_positive (show 0 ≤ ell by linarith) hr hs h.admissible
  have hvalid := terminal_valid hs h.admissible
  rw [History.append_node]
  exact (nextGap_childRatio hrg (child_exponent_positive (show 0 ≤ ell by linarith) hp)
    (valid_pos (child_valid hvalid hp))).symm

theorem matched_live_update {v mesh d : ℝ} (h k : History w ell S start) (z y : CostState)
    (hfollow : primeFollows h (some k)) (hcont : continuousFollows z y)
    (hside : h.node.side = stateSide z.1)
    (hgap : |Real.log h.node.gap-Real.log (gapValue v z)| ≤ d)
    (hmatch : |k.node.ratio-stateRatio y.1| ≤ mesh) :
    k.node.side = stateSide y.1 ∧
      |Real.log k.node.gap-Real.log (gapValue v y)| ≤ d+4*mesh := by
  obtain ⟨p,hp,rfl⟩ := hfollow
  have hrg := terminal_gap_positive (show 0 ≤ ell by linarith) hr hs h.admissible
  have hnext := terminal_valid hs (h.append p hp).admissible
  constructor
  · rw [History.append_node]
    change h.node.side.flip = stateSide y.1
    rw [hcont.2,hside]
  · have hy : y = (y.1,z.2+cost (stateRatio y.1)) := Prod.ext rfl hcont.1
    have hygap : gapValue v y = nextGap (gapValue v z) (stateRatio y.1) := by
      calc
        _ = gapValue v (y.1,z.2+cost (stateRatio y.1)) := congrArg (gapValue v) hy
        _ = _ := gapValue_update v z y.1
    rw [prime_step_gap hell hr hs, hygap]
    exact log_gap_step hrg (Real.exp_pos _) (PrimeTiltBounds.valid_ge_half hnext)
      (CostPrefixTransport.stateRatio_ge_half y.1) hgap hmatch

end NumberTheoryLean.ActualCouplingUpdates

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FlaggedSourceStart
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.PersistentFailureFlag

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open ActualCouplingFinite

variable {α : Type*} [MeasurableSpace α]

theorem badBit_measurable {Bad : α → Prop} (hBad : MeasurableSet {x | Bad x}) : Measurable (badBit Bad) := by
  classical
  exact Measurable.ite hBad measurable_const measurable_const

theorem update_measurable {Bad : α → Prop} (hBad : MeasurableSet {x | Bad x}) : Measurable (update Bad) := by
  have hor : Measurable (fun p : Bool × Bool => p.1 || p.2) := measurable_of_countable _
  exact measurable_snd.prodMk (hor.comp ((measurable_snd.comp measurable_fst).prodMk
    ((badBit_measurable hBad).comp measurable_snd)))

instance marked_isMarkov (K : Kernel α α) [IsMarkovKernel K]
    {Bad : α → Prop} (hBad : MeasurableSet {x | Bad x}) : IsMarkovKernel (marked K hBad) := by
  unfold marked
  exact Kernel.IsMarkovKernel.map _ (update_measurable hBad)

theorem marked_apply (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (z : FlagState α) {B : Set (FlagState α)} (hB : MeasurableSet B) :
    marked K hBad z B = K z.1 {y | (y,z.2 || badBit Bad y) ∈ B} := by
  rw [marked,Kernel.map_apply' _ (update_measurable hBad) _ hB,
    Kernel.prod_apply' _ _ _ ((update_measurable hBad) hB),Kernel.id_apply]
  rw [lintegral_dirac']
  · rfl
  · exact measurable_measure_prodMk_left ((update_measurable hBad) hB)

theorem row_update_measurable {Bad : α → Prop} (hBad : MeasurableSet {x | Bad x}) (b : Bool) :
    Measurable (fun y : α => (y,b || badBit Bad y)) := by
  have hor : Measurable (fun p : Bool × Bool => p.1 || p.2) := measurable_of_countable _
  exact measurable_id.prodMk (hor.comp (measurable_const.prodMk (badBit_measurable hBad)))

theorem marked_eq_map (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (z : FlagState α) :
    marked K hBad z = (K z.1).map (fun y => (y,z.2 || badBit Bad y)) := by
  apply Measure.ext
  intro B hB
  rw [marked_apply K hBad z hB,Measure.map_apply (row_update_measurable hBad z.2) hB]
  rfl

theorem marked_map (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (z : FlagState α) : (marked K hBad z).map Prod.fst = K z.1 := by
  rw [marked_eq_map K hBad z,Measure.map_map (f:=fun y => (y,z.2 || badBit Bad y))
    (g:=Prod.fst) measurable_fst (row_update_measurable hBad z.2)]
  exact Measure.map_id

instance marked_pow_markov (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (n : ℕ) : IsMarkovKernel ((marked K hBad)^n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.id : Kernel (FlagState α) (FlagState α)); infer_instance
  | succ n ih =>
    let := ih
    have hp : (marked K hBad)^(n+1) = (marked K hBad) ∘ₖ ((marked K hBad)^n) := pow_succ' _ _
    rw [hp]
    first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply update_measurable <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem marked_power_map (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (n : ℕ) (z : FlagState α) :
    (((marked K hBad)^n) z).map Prod.fst = (K^n) z.1 :=
  map_power_of_step (marked K hBad) K measurable_fst (marked_map K hBad) n z

instance law_probability (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (x : α) (n : ℕ) : IsProbabilityMeasure (law K hBad x n) := by
  unfold law
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.PersistentFailureFlag



namespace NumberTheoryLean.FailureFlagBounds

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open PersistentFailureFlag

variable {α : Type*} [MeasurableSpace α]

theorem surviving_measurable {Good : α → Prop} (hGood : MeasurableSet {x | Good x}) :
    MeasurableSet {z | surviving Good z} :=
  (measurable_snd (measurableSet_singleton false)).imp (measurable_fst hGood)

theorem surviving_step (K : Kernel α α) [IsMarkovKernel K] {Bad P Q : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (hQ : MeasurableSet {x | Q x})
    (hstep : ∀ x,P x → ∀ᵐ y ∂K x, ¬Bad y → Q y) (z : FlagState α) (hz : surviving P z) :
    ∀ᵐ y ∂marked K hBad z, surviving Q y := by
  classical
  rw [marked_eq_map K hBad z]
  apply (ae_map_iff (row_update_measurable hBad z.2).aemeasurable (surviving_measurable hQ)).mpr
  rcases z with ⟨x,b⟩
  cases b with
  | false =>
    filter_upwards [hstep x (hz rfl)] with y hy
    intro hf
    apply hy
    simpa [badBit] using hf
  | true =>
    exact Eventually.of_forall (fun y => by
      intro hf
      have hf' : (true || badBit Bad y) = false := hf
      simp at hf')

theorem law_survives (K : Kernel α α) [IsMarkovKernel K] {Bad : α → Prop}
    (hBad : MeasurableSet {x | Bad x}) (Good : ℕ → α → Prop)
    (hGood : ∀ n,MeasurableSet {x | Good n x})
    (hstep : ∀ n x,Good n x → ∀ᵐ y ∂K x, ¬Bad y → Good (n+1) y)
    (x : α) (hx : Good 0 x) (n : ℕ) :
    ∀ᵐ z ∂law K hBad x n, surviving (Good n) z := by
  induction n with
  | zero =>
    change ∀ᵐ z ∂Measure.dirac (x,false), surviving (Good 0) z
    exact (ae_dirac_iff (surviving_measurable (hGood 0))).mpr (fun _ => hx)
  | succ n ih =>
    have hp : (marked K hBad)^(n+1) = (marked K hBad) ∘ₖ ((marked K hBad)^n) := pow_succ' _ _
    change ∀ᵐ z ∂((marked K hBad)^(n+1)) (x,false), surviving (Good (n+1)) z
    rw [hp]
    apply Kernel.ae_comp_of_ae_ae (surviving_measurable (hGood (n+1)))
    filter_upwards [ih] with z hz
    exact surviving_step K hBad (hGood (n+1)) (hstep n) z hz

end NumberTheoryLean.FailureFlagBounds



namespace NumberTheoryLean.ActualFlagInvariant

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualCouplingSupport ActualCouplingUpdates ActualCouplingFinite
open PersistentFailureFlag FailureFlagBounds RegeneratingInverseBands ArrivalKernelGeometry

variable {w ell S : ℝ} {start : Node}

theorem liveGood_measurable (v mesh : ℝ) (n : ℕ) (h : History w ell S start) :
    MeasurableSet {z | liveGood v mesh n h z} := by
  have hside : MeasurableSet {z : CostState | h.node.side = stateSide z.1} := by
    have heq : {z : CostState | h.node.side = stateSide z.1} = {z : CostState | stateSide z.1 = h.node.side} := by
      ext z
      exact eq_comm
    rw [heq]
    exact measurable_fst (side_set_measurable h.node.side)
  exact (measurableSet_le (stateRatio_measurable.comp measurable_fst) measurable_const).inter
    (hside.inter ((measurableSet_le
      (measurable_const.sub (stateRatio_measurable.comp measurable_fst)).abs measurable_const).inter
      (measurableSet_le (measurable_const.sub (Real.measurable_log.comp (gapValue_measurable v))).abs measurable_const)))

theorem GoodAt_measurable (v mesh : ℝ) (n : ℕ) :
    MeasurableSet {q : JointState w ell S start | GoodAt v mesh n q} := by
  apply Measurable.setOf
  apply measurable_from_prod_countable_right
  intro p
  cases p with
  | none => exact measurable_const.sumElim measurable_const
  | some h => exact (measurableSet_setOfPred.mp (liveGood_measurable v mesh n h)).sumElim measurable_const

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem joint_dead_ae (v mesh : ℝ) :
    ∀ᵐ q ∂jointKernel hw hell hS0 hS hr hs hsS v mesh (none,CemeteryKernel.dead),
      q = (none,CemeteryKernel.dead) := by
  have hL : ∀ᵐ p ∂(jointKernel hw hell hS0 hS hr hs hsS v mesh (none,CemeteryKernel.dead)).map Prod.fst, p = none := by
    rw [jointKernel_left hw hell hS0 hS hr hs hsS,chain_none]
    exact (ae_dirac_iff (measurableSet_singleton _)).mpr rfl
  have hdead : MeasurableSet {y : CemeteryKernel.Space CostState | y = CemeteryKernel.dead} := by
    apply measurableSet_sum_iff.mpr
    constructor
    · have hp : (Sum.inl : CostState → CemeteryKernel.Space CostState) ⁻¹' {y | y = CemeteryKernel.dead} = ∅ := by
        ext x
        change ((Sum.inl x : CemeteryKernel.Space CostState) = Sum.inr ()) ↔ False
        simp
      rw [hp]
      exact MeasurableSet.empty
    · simp [CemeteryKernel.dead]
  have hR : ∀ᵐ y ∂(jointKernel hw hell hS0 hS hr hs hsS v mesh (none,CemeteryKernel.dead)).map Prod.snd,
      y = CemeteryKernel.dead := by
    rw [jointKernel_right hw hell hS0 hS hr hs hsS]
    change ∀ᵐ y ∂Measure.dirac (CemeteryKernel.dead : CemeteryKernel.Space CostState), y = CemeteryKernel.dead
    exact (ae_dirac_iff hdead).mpr rfl
  have hl := (ae_map_iff measurable_fst.aemeasurable (measurableSet_singleton _)).mp hL
  have hr' := (ae_map_iff measurable_snd.aemeasurable hdead).mp hR
  filter_upwards [hl,hr'] with q hq hq'
  exact Prod.ext hq hq'

theorem actual_good_step (v : ℝ) {mesh : ℝ} (hm : 0 < mesh) (n : ℕ)
    (q : JointState w ell S start) (hq : GoodAt v mesh n q) :
    ∀ᵐ y ∂jointKernel hw hell hS0 hS hr hs hsS v mesh q,
      ¬mismatch mesh y → GoodAt v mesh (n+1) y := by
  rcases q with ⟨p,z⟩
  cases p with
  | none =>
    cases z with
    | inl z => exact False.elim hq
    | inr u =>
      cases u
      filter_upwards [joint_dead_ae hw hell hS0 hS hr hs hsS v mesh] with y hy
      intro _
      rw [hy]
      trivial
  | some h =>
    cases z with
    | inr u => exact False.elim hq
    | inl z =>
      filter_upwards [joint_follows hw hell hS0 hS hr hs hsS v mesh h z,
        joint_matching_control hw hell hS0 hS hr hs hsS v hm (some h) (.inl z),
        joint_continuous_supported hw hell hS0 hS hr hs hsS v mesh (some h) (.inl z)] with y hy hmatch hSup
      intro hnot
      have heq : primeLabel w ell S mesh start y.1 = continuousLabel S mesh y.2 := not_ne_iff.mp hnot
      have hmout := hmatch heq
      rcases y with ⟨p,y⟩
      cases p with
      | none =>
        cases y with
        | inl y => exact False.elim hmout
        | inr u => trivial
      | some k =>
        cases y with
        | inr u => exact False.elim hmout
        | inl y =>
          have hup := matched_live_update hell hr hs h k z y hy.1 hy.2 hq.2.1 hq.2.2.2
            (show |k.node.ratio-stateRatio y.1| ≤ mesh from hmout.le)
          refine ⟨hSup,hup.1,hmout.le,?_⟩
          have he : 4*(n:ℝ)*mesh+4*mesh = 4*((n+1:ℕ):ℝ)*mesh := by push_cast <;> ring
          exact hup.2.trans_eq he

theorem actual_flagged_invariant (v : ℝ) {mesh : ℝ} (hm : 0 < mesh)
    (q : JointState w ell S start) (hq : GoodAt v mesh 0 q) (n : ℕ) :
    ∀ᵐ y ∂law (jointKernel hw hell hS0 hS hr hs hsS v mesh) (mismatch_measurable mesh) q n,
      y.2 = false → GoodAt v mesh n y.1 :=
  law_survives _ (mismatch_measurable mesh) (GoodAt v mesh) (GoodAt_measurable v mesh)
    (actual_good_step hw hell hS0 hS hr hs hsS v hm) q hq n

end NumberTheoryLean.ActualFlagInvariant



namespace NumberTheoryLean.FlaggedSourceStart

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualCouplingFinite ActualFlagInvariant PersistentFailureFlag
open RegeneratingInverseBands ContinuousKilledBins

theorem typedState_side (i : Side) (s : ℝ) (hs : Valid i s) : stateSide (typedState i s hs) = i := by
  cases i <;> rfl

theorem typedState_ratio (i : Side) (s : ℝ) (hs : Valid i s) : stateRatio (typedState i s hs) = s := by
  cases i <;> rfl

variable {w ell S : ℝ} {start : Node}

theorem source_good {mesh : ℝ} (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S) (hm : 0 ≤ mesh) :
    GoodAt (Real.log start.gap) mesh 0 (sourceJoint w ell S start hs) := by
  change liveGood (Real.log start.gap) mesh 0 History.empty (sourceCostState hs)
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [sourceCostState,typedState_ratio] using hsS
  · change start.side = stateSide (typedState start.side start.ratio hs)
    exact (typedState_side _ _ _).symm
  · change |start.ratio-stateRatio (typedState start.side start.ratio hs)| ≤ mesh
    rw [typedState_ratio,sub_self,abs_zero]
    exact hm
  · rw [Nat.cast_zero,mul_zero,zero_mul]
    change |Real.log start.gap-Real.log (gapValue (Real.log start.gap) (sourceCostState hs))| ≤ 0
    simp [gapValue,sourceCostState]

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

instance sourceLaw_probability (mesh : ℝ) (n : ℕ) :
    IsProbabilityMeasure (sourceLaw hw hell hS0 hS hr hs hsS mesh n) := by
  unfold sourceLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem sourceLaw_joint (mesh : ℝ) (n : ℕ) :
    (sourceLaw hw hell hS0 hS hr hs hsS mesh n).map Prod.fst =
      jointPathLaw hw hell hS0 hS hr hs hsS (Real.log start.gap) mesh (sourceCostState hs) n :=
  marked_power_map _ (mismatch_measurable mesh) n (sourceJoint w ell S start hs,false)

theorem sourceLaw_continuous (mesh : ℝ) (n : ℕ) :
    (sourceLaw hw hell hS0 hS hr hs hsS mesh n).map (fun q => q.1.2) =
      ((continuousChain (Real.log start.gap) ell S)^n) (.inl (sourceCostState hs)) := by
  calc
    _ = ((sourceLaw hw hell hS0 hS hr hs hsS mesh n).map Prod.fst).map Prod.snd :=
      (Measure.map_map (f:=Prod.fst) (g:=Prod.snd) measurable_snd measurable_fst).symm
    _ = _ := by rw [sourceLaw_joint,jointPathLaw_continuous]

theorem sourceLaw_good {mesh : ℝ} (hm : 0 < mesh) (n : ℕ) :
    ∀ᵐ q ∂sourceLaw hw hell hS0 hS hr hs hsS mesh n,
      q.2 = false → GoodAt (Real.log start.gap) mesh n q.1 :=
  actual_flagged_invariant hw hell hS0 hS hr hs hsS (Real.log start.gap) hm
    (sourceJoint w ell S start hs) (source_good hs hsS hm.le) n

end NumberTheoryLean.FlaggedSourceStart


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ExponentialMesh
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ExponentialMesh

open _root_.Set _root_.Filter
open scoped Topology

theorem mesh_pos (κ w : ℝ) : 0 < mesh κ w := by
  apply one_div_pos.mpr
  exact_mod_cast Nat.ceil_pos.mpr (Real.exp_pos (κ*Real.sqrt (Real.log w)))

theorem mesh_upper (κ w : ℝ) : mesh κ w ≤ Real.exp (-κ*Real.sqrt (Real.log w)) := by
  have h := one_div_le_one_div_of_le (Real.exp_pos (κ*Real.sqrt (Real.log w)))
    (Nat.le_ceil (Real.exp (κ*Real.sqrt (Real.log w))))
  have he : 1/Real.exp (κ*Real.sqrt (Real.log w)) = Real.exp (-κ*Real.sqrt (Real.log w)) := by
    rw [one_div,← Real.exp_neg]
    congr 1
    ring
  exact h.trans_eq he

theorem log_pow_sqrt (n : ℕ) {w : ℝ} (hw : 0 ≤ Real.log w) :
    (Real.sqrt (Real.log w))^(2*n) = (Real.log w)^n := by
  rw [pow_mul,Real.sq_sqrt hw]

theorem log_power_exp_tendsto (C : ℝ) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun w : ℝ => C*(Real.log w)^n*Real.exp (-c*Real.sqrt (Real.log w))) atTop (𝓝 0) := by
  have hbase : Tendsto (fun x : ℝ => C*x^(2*n)*Real.exp (-c*x)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((2*n:ℕ):ℝ) c hc).const_mul C
    simpa only [Real.rpow_natCast,mul_zero,mul_assoc] using h
  apply Tendsto.congr' _ (hbase.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop))
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0:ℝ))] with w hw
  simp only [Function.comp_apply,log_pow_sqrt n hw]

theorem log_power_exp_absorption (C : ℝ) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ w : ℝ in atTop, C*(Real.log w)^n*Real.exp (-c*Real.sqrt (Real.log w)) ≤
      Real.exp (-(c/2)*Real.sqrt (Real.log w)) := by
  have ht := log_power_exp_tendsto C n (show 0 < c/2 by positivity)
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))] with w hw
  calc
    _ = (C*(Real.log w)^n*Real.exp (-(c/2)*Real.sqrt (Real.log w)))*
        Real.exp (-(c/2)*Real.sqrt (Real.log w)) := by
      rw [show -c*Real.sqrt (Real.log w) = -(c/2)*Real.sqrt (Real.log w)+-(c/2)*Real.sqrt (Real.log w) by ring,
        Real.exp_add]
      ring
    _ ≤ 1*Real.exp (-(c/2)*Real.sqrt (Real.log w)) := mul_le_mul_of_nonneg_right hw.le (Real.exp_pos _).le
    _ = _ := one_mul _

theorem exp_increment {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : Real.exp x-1 ≤ 3*x := by
  have h := Real.abs_exp_sub_one_le (x:=x) (by rw [abs_of_nonneg hx]; exact hx1)
  rw [abs_of_nonneg hx] at h
  linarith [le_abs_self (Real.exp x-1)]

end NumberTheoryLean.ExponentialMesh

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_HorizonMeshSmallness
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.HorizonMeshSmallness

open _root_.Set _root_.Filter
open scoped Topology
open UniformFailureBudget ExponentialMesh

theorem horizon_mesh_smallness {A D κ : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hκ : 0 < κ) :
    ∀ᶠ w : ℝ in atTop, ∀ S : ℝ, 0 ≤ S → S ≤ (Real.log w)^3 → ∀ N : ℕ,
      (N:ℝ) ≤ A*(Real.log w)^3 →
      2*mesh κ w ≤ 1 ∧ 4*(N:ℝ)*mesh κ w ≤ 1 ∧ D*(1+S)^3*mesh κ w ≤ 1 ∧
        upperDisplacement S (mesh κ w) N+mesh κ w ≤ 1 := by
  filter_upwards [log_power_exp_absorption 2 0 hκ,
    log_power_exp_absorption (4*A) 3 hκ,
    log_power_exp_absorption (8*D) 9 hκ,
    log_power_exp_absorption (24*A+1) 6 hκ,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with w htwo hclockB hparentB hupperB hlog
  intro S hS hSP N hNP
  let x := Real.log w
  let e := Real.exp (-κ*Real.sqrt (Real.log w))
  let τ := mesh κ w
  have hx : 1 ≤ x := hlog
  have hx0 : 0 ≤ x := by linarith
  have hx3 : 1 ≤ x^3 := one_le_pow₀ hx
  have hx6 : 1 ≤ x^6 := one_le_pow₀ hx
  have hSp : S+1 ≤ 2*x^3 := by change S ≤ x^3 at hSP; linarith
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hτ : 0 < τ := mesh_pos κ w
  have hτe : τ ≤ e := mesh_upper κ w
  have hsmall : Real.exp (-(κ/2)*Real.sqrt (Real.log w)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [Real.sqrt_nonneg (Real.log w)]
  have htwo' : 2*τ ≤ 1 := by
    have ht : 2*e ≤ Real.exp (-(κ/2)*Real.sqrt (Real.log w)) := by
      simpa only [pow_zero,mul_one] using htwo
    exact (mul_le_mul_of_nonneg_left hτe (by norm_num)).trans (ht.trans hsmall)
  have hclock : 4*(N:ℝ)*τ ≤ 1 := by
    calc
      _ ≤ (4*(A*x^3))*e := mul_le_mul (by nlinarith : 4*(N:ℝ) ≤ 4*(A*x^3)) hτe hτ.le (by positivity)
      _ = (4*A)*x^3*e := by ring
      _ ≤ _ := hclockB.trans hsmall
  have hparent : D*(1+S)^3*τ ≤ 1 := by
    calc
      _ ≤ (D*(2*x^3)^3)*e := mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith : 1+S ≤ 2*x^3) 3) hD)
        hτe hτ.le (by positivity)
      _ = (8*D)*x^9*e := by ring
      _ ≤ _ := hparentB.trans hsmall
  have hU : upperDisplacement S τ N ≤ 24*A*x^6*e := by
    have hexp := exp_increment (show 0 ≤ 4*(N:ℝ)*τ by positivity) hclock
    have hNmul : 12*(N:ℝ)*τ ≤ 12*(A*x^3)*e :=
      mul_le_mul (by nlinarith : 12*(N:ℝ) ≤ 12*(A*x^3)) hτe hτ.le (by positivity)
    calc
      _ ≤ (S+1)*(12*(N:ℝ)*τ) := by
        unfold upperDisplacement
        apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ S+1)
        nlinarith
      _ ≤ (2*x^3)*(12*(A*x^3)*e) := mul_le_mul hSp hNmul (by positivity) (by positivity)
      _ = _ := by ring
  have he6 : e ≤ x^6*e := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hx6 he
  have hUpper : upperDisplacement S τ N+τ ≤ 1 := by
    calc
      _ ≤ (24*A+1)*x^6*e := by nlinarith
      _ ≤ _ := hupperB.trans hsmall
  exact ⟨htwo',hclock,hparent,hUpper⟩

end NumberTheoryLean.HorizonMeshSmallness

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_GridWeightComparison
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointPathLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.jointKernel_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedSourceStart.sourceLaw_probability _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.GridWeightComparison

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open WeightGlobalBounds ExponentialMesh DerivativeWeights WeightFutureIntegrals

theorem weight_local_ratio : ∃ L : ℝ, 0 < L ∧ ∀ S : ℝ, 3 ≤ S → ∀ i : Side, ∀ u s h : ℝ,
    Valid i u → Valid i s → s ≤ S → u ≤ s → s ≤ u+h →
      weight i u/weight i s ≤ Real.exp (L*(1+S)^3*h) := by
  obtain ⟨L,hL,hbound⟩ := weights_log_lipschitz
  refine ⟨L,hL,?_⟩
  intro S hS i u s h hu hs hsS hus hsu
  have hlog : |Real.log (weight i u)-Real.log (weight i s)| ≤ L*(1+S)^3*|u-s| := by
    cases i with
    | even => exact (hbound S hS).1 u s hu hs (hus.trans hsS) hsS
    | odd => exact (hbound S hS).2 u s hu hs (hus.trans hsS) hsS
  have habs : |u-s| ≤ h := by
    rw [abs_sub_comm u s,abs_of_nonneg (sub_nonneg.mpr hus)]
    linarith
  have hdiff : Real.log (weight i u)-Real.log (weight i s) ≤ L*(1+S)^3*h :=
    ((le_abs_self _).trans hlog).trans (mul_le_mul_of_nonneg_left habs (by positivity))
  have he := Real.exp_le_exp.mpr hdiff
  rwa [Real.exp_sub,Real.exp_log (weight_pos hu),Real.exp_log (weight_pos hs)] at he

end NumberTheoryLean.GridWeightComparison

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceMarginalRate
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.UniformBudgetRate

open _root_.Set _root_.Filter
open scoped Topology
open UniformFailureBudget ExponentialMesh BudgetPolynomialBound HorizonMeshSmallness PrimeKilledChain

theorem source_scale_bound {d w B : ℝ} (hW : d^2 ≤ Real.log w)
    (hB : 2 ≤ Real.log B) (hcomp : Real.log B ≤ d*Real.log w) :
    (Real.log B)^2 ≤ (Real.log w)^3 ∧
      (LowStateHorizon.sourceHorizon ((Real.log B)^2) B:ℝ) ≤ 5*d^3*(Real.log w)^3 := by
  have hlog : 0 ≤ Real.log w := (sq_nonneg d).trans hW
  have hpow₂ := pow_le_pow_left₀ (show 0 ≤ Real.log B by linarith) hcomp 2
  have hpow₃ := pow_le_pow_left₀ (show 0 ≤ Real.log B by linarith) hcomp 3
  have hmul := mul_le_mul_of_nonneg_right hW (sq_nonneg (Real.log w))
  have hN := LowStateHorizon.source_horizon_log_cube hB
  constructor <;> nlinarith

end NumberTheoryLean.UniformBudgetRate

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SuccessfulRewardComparison
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SuccessfulRewardComparison

open _root_.Set _root_.MeasureTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualFlagInvariant GridWeightComparison DerivativeWeights
open RegeneratingInverseBands InvariantInverseWeights ArrivalKernelGeometry

theorem nearby_inverse_ratio : ∃ L : ℝ,0 < L ∧ ∀ S : ℝ,3 ≤ S →
    ∀ i : Side,∀ a b h : ℝ,Valid i a → Valid i b → a ≤ S → b ≤ S →
      |a-b| ≤ h → L*(1+S)^3*h ≤ 1 → weight i b/weight i a ≤ 3 := by
  obtain ⟨L,hL,hlocal⟩ := weight_local_ratio
  refine ⟨L,hL,?_⟩
  intro S hS i a b h ha hb haS hbS hab hsmall
  by_cases hba : b ≤ a
  · have hah : a ≤ b+h := by linarith [(abs_le.mp hab).2]
    exact (hlocal S hS i b a h hb ha haS hba hah).trans
      ((Real.exp_le_exp.mpr hsmall).trans Real.exp_one_lt_three.le)
  · have hmono := TwoStepDensityBounds.weight_antitone ha hb (le_of_not_ge hba)
    have hratio : weight i b/weight i a ≤ 1 := (div_le_one (weight_pos ha)).mpr hmono
    linarith

theorem reward_factor_comparison {c r q φ ψ : ℝ} (hc : 0 < c) (hr : 0 < r) (hq : 0 < q)
    (hφ : 0 < φ) (hψ : 0 < ψ) (hrq : r ≤ 3*q) (hqr : q ≤ 3*r) (hw : ψ/φ ≤ 3) :
    r^2*Real.exp (-c*r)/φ ≤ 27*(q^2*Real.exp (-(c/3)*q)/ψ) := by
  have hsq : r^2 ≤ 9*q^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hrq) (show 0 ≤ 3*q+r by linarith)]
  have he : Real.exp (-c*r) ≤ Real.exp (-(c/3)*q) := Real.exp_le_exp.mpr (by nlinarith)
  have hInv : 1/φ ≤ 3/ψ := by
    apply (div_le_div_iff₀ hφ hψ).mpr
    have hh := (div_le_iff₀ hφ).mp hw
    simpa only [one_mul] using hh
  calc
    _ = (r^2*Real.exp (-c*r))*(1/φ) := by ring
    _ ≤ ((9*q^2)*Real.exp (-(c/3)*q))*(3/ψ) :=
      mul_le_mul (mul_le_mul hsq he (Real.exp_pos _).le (by positivity)) hInv
        (one_div_pos.mpr hφ).le (by positivity)
    _ = _ := by ring

theorem stateWeight_eq (s : State) : stateWeight s = weight (stateSide s) (stateRatio s) := by
  cases s <;> rfl

theorem actual_good_tail_comparison : ∃ L : ℝ,0 < L ∧
    ∀ w ell S : ℝ,1 ≤ ell → 3 ≤ S → ∀ start : Node,
      0 < start.gap → Valid start.side start.ratio → start.ratio ≤ S →
      ∀ v mesh : ℝ,∀ n M : ℕ,4*(n:ℝ)*mesh ≤ 1 → L*(1+S)^3*mesh ≤ 1 →
      ∀ h : History w ell S start,∀ z : CostState,
        liveGood v mesh n h z → z ∈ arrivalSet v ell → ∀ c : ℝ,0 < c →
          PrimeExponentialTail.tailReward c (3*((M:ℝ)+1)) (some h) ≤
            ENNReal.ofReal 27*WeightedGapTail.tailReward (c/3) v ell M z := by
  obtain ⟨L,hL,hnear⟩ := nearby_inverse_ratio
  refine ⟨L,hL,?_⟩
  intro w ell S hell hS start hr hs hsS v mesh n M hclock hsmall h z hgood harr c hc
  have hrg : 0 < h.node.gap := terminal_gap_positive (by linarith) hr hs h.admissible
  have hqg : 0 < gapValue v z := Real.exp_pos _
  have hv : Valid h.node.side h.node.ratio := terminal_valid hs h.admissible
  have hnv : Valid h.node.side (stateRatio z.1) := by rw [hgood.2.1]; exact stateRatio_valid z.1
  have hsbound : h.node.ratio ≤ S := terminal_ratio_le hsS h.admissible
  have hweight := hnear S hS h.node.side h.node.ratio (stateRatio z.1) mesh hv hnv hsbound hgood.1 hgood.2.2.1 hsmall
  have hrel := NearbyParentGeometry.log_gap_relative hrg hqg (hgood.2.2.2.trans hclock)
  have hrq : h.node.gap ≤ 3*gapValue v z := hrel.1.trans
    (mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le hqg.le)
  have hqr : gapValue v z ≤ 3*h.node.gap := hrel.2.trans
    (mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le hrg.le)
  have hφ := weight_pos hv
  have hψ := weight_pos hnv
  have hreward := reward_factor_comparison hc hrg hqg hφ hψ hrq hqr hweight
  have hstate : weight h.node.side (stateRatio z.1) = stateWeight z.1 := by rw [hgood.2.1,stateWeight_eq]
  rw [hstate] at hreward
  by_cases hh : 3*((M:ℝ)+1) < h.node.gap
  · have hlow : (M:ℝ)+1 ≤ gapValue v z := by linarith
    have harrival : stateRatio z.1 < gapValue v z/ell := by
      rw [arrivalSet_eq_cutoff v (by linarith : 0 < ell)] at harr
      exact harr
    rw [PrimeExponentialTail.tailReward,ite_eq_left hh,WeightedGapTail.tailReward,
      indicator_of_mem (show z ∈ {z : CostState | (M:ℝ)+1 ≤ gapValue v z ∧ stateRatio z.1 < gapValue v z/ell} from ⟨hlow,harrival⟩)]
    rw [← div_eq_mul_inv,← ENNReal.ofReal_div_of_pos (stateWeight_pos z.1),
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 27)]
    exact ENNReal.ofReal_le_ofReal hreward
  · rw [PrimeExponentialTail.tailReward,ite_eq_right hh]
    exact zero_le

end NumberTheoryLean.SuccessfulRewardComparison

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SourceCompactCoupling
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.CouplingData

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualFlagInvariant KernelCouplingLift PersistentFailureFlag

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem sourceLaw_eq (mesh : ℝ) (n : ℕ) :
    FlaggedSourceStart.sourceLaw hw hell hS0 hS hr hs hsS mesh n = sourceLaw w ell S start hs mesh n := rfl

end NumberTheoryLean.CouplingData

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_ContinuousCompletedOccupation
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointPathLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.continuousParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.jointKernel_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedSourceStart.sourceLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section


namespace NumberTheoryLean.ContinuousCompletedOccupation

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathMeasures ContinuousKilledBins LowStateHorizon CemeteryKernel
open PairedCostGrouping OccupationDecomposition CostPrefixTransport

theorem liftReward_measurable {F : CostState → ℝ≥0∞} (hF : Measurable F) : Measurable (liftReward F) :=
  CemeteryPowers.liftReward_measurable hF

theorem completed_power_lift (v ell S : ℝ) {F : CostState → ℝ≥0∞} (hF : Measurable F)
    (n : ℕ) (q : Space CostState) :
    (∫⁻ y,liftReward F y ∂((continuousChain v ell S)^n) q) =
      liftReward (fun z => ∫⁻ y,F y ∂((lowKernel costKernel v ell S)^n) z) q :=
  CemeteryPowers.power_lift (lowKernel costKernel v ell S) hF n q

theorem low_power_integral_le (v ell S : ℝ) {F : CostState → ℝ≥0∞} (hF : Measurable F)
    (n : ℕ) (z : CostState) :
    (∫⁻ y,F y ∂((lowKernel costKernel v ell S)^n) z) ≤ ∫⁻ y,F y ∂(costKernel^n) z := by
  induction n generalizing z with
  | zero => exact le_rfl
  | succ n ih =>
    have hp : (lowKernel costKernel v ell S)^(n+1) =
        ((lowKernel costKernel v ell S)^n) ∘ₖ lowKernel costKernel v ell S := pow_succ _ _
    have hq : costKernel^(n+1) = (costKernel^n) ∘ₖ costKernel := pow_succ _ _
    rw [hp,hq,Kernel.lintegral_comp _ _ _ hF,Kernel.lintegral_comp _ _ _ hF]
    calc
      _ ≤ ∫⁻ y,∫⁻ a,F a ∂(costKernel^n) y ∂lowKernel costKernel v ell S z := lintegral_mono ih
      _ ≤ _ := by
        rw [lowKernel,Kernel.restrict_apply]
        exact setLIntegral_le_lintegral _ _

theorem inclusive_integral_eq_tsum {F : CostState → ℝ≥0∞} (hF : Measurable F) (z : CostState) :
    (∫⁻ y,F y ∂inclusiveOccupation z) = ∑' n : ℕ,∫⁻ y,F y ∂(costKernel^n) z := by
  rw [inclusiveOccupation,_root_.add_apply,lintegral_add_measure,Kernel.id_apply,
    lintegral_dirac' _ hF,fullOccupation,Kernel.sum_apply,lintegral_sum_measure]
  conv_rhs => rw [tsum_eq_zero_add' ENNReal.summable]
  congr 1
  change F z = ∫⁻ y,F y ∂Measure.dirac z
  rw [lintegral_dirac' _ hF]

theorem completed_finite_occupation_le (v ell S : ℝ) {F : CostState → ℝ≥0∞} (hF : Measurable F)
    (N : ℕ) (z : CostState) :
    (∑ n ∈ range N,∫⁻ y,liftReward F y ∂((continuousChain v ell S)^n) (.inl z)) ≤
      ∫⁻ y,F y ∂inclusiveOccupation z := by
  rw [inclusive_integral_eq_tsum hF z]
  calc
    _ ≤ ∑ n ∈ range N,∫⁻ y,F y ∂(costKernel^n) z := by
      apply Finset.sum_le_sum
      intro n _hn
      rw [completed_power_lift v ell S hF]
      exact low_power_integral_le v ell S hF n z
    _ ≤ _ := ENNReal.sum_le_tsum (range N)

end NumberTheoryLean.ContinuousCompletedOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ContinuousArrivalSupport
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ContinuousArrivalSupport

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ContinuousKilledBins CemeteryKernel LowStateHorizon ArrivalKernelGeometry

theorem arrivalSupported_measurable (v ell : ℝ) : MeasurableSet {z | arrivalSupported v ell z} := by
  apply measurableSet_sum_iff.mpr
  exact ⟨arrivalSet_measurable v ell,MeasurableSet.univ⟩

theorem unsupported_eq (v ell : ℝ) :
    {z : Space CostState | ¬arrivalSupported v ell z} = Sum.inl '' (arrivalSet v ell)ᶜ := by
  ext z
  cases z <;> simp [arrivalSupported]

theorem continuous_row_arrival (v ell S : ℝ) (q : Space CostState) :
    ∀ᵐ y ∂continuousChain v ell S q,arrivalSupported v ell y := by
  apply ae_iff.mpr
  rw [unsupported_eq]
  cases q with
  | inl z =>
    rw [continuousChain,complete_live_mass _ _ (arrivalSet_measurable v ell).compl,
      lowKernel,Kernel.restrict_apply,Measure.restrict_apply (arrivalSet_measurable v ell).compl]
    have he : (arrivalSet v ell)ᶜ ∩ lowDomain v ell S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hy.1 hy.2.1
    rw [he,measure_empty]
  | inr u =>
    cases u
    change Measure.dirac (dead : Space CostState) (Sum.inl '' (arrivalSet v ell)ᶜ) = 0
    rw [Measure.dirac_apply' _ (arrivalSet_measurable v ell).compl.inl_image,
      indicator_of_notMem (by simp [dead])]

theorem continuous_power_arrival (v ell S : ℝ) (q : Space CostState) (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ y ∂((continuousChain v ell S)^n) q,arrivalSupported v ell y := by
  cases n with
  | zero => omega
  | succ n =>
    have hp : (continuousChain v ell S)^(n+1) = continuousChain v ell S ∘ₖ ((continuousChain v ell S)^n) := pow_succ' _ _
    rw [hp]
    apply Kernel.ae_comp_of_ae_ae (arrivalSupported_measurable v ell)
    exact Filter.Eventually.of_forall (continuous_row_arrival v ell S)

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

include hw hell hS0 hS hr hsS in

theorem source_arrival (mesh : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ q ∂CouplingData.sourceLaw w ell S start hs mesh n,
      arrivalSupported (Real.log start.gap) ell q.1.2 := by
  have he := FlaggedSourceStart.sourceLaw_continuous hw hell hS0 hS hr hs hsS mesh n
  rw [CouplingData.sourceLaw_eq hw hell hS0 hS hr hs hsS] at he
  have h : ∀ᵐ y ∂(CouplingData.sourceLaw w ell S start hs mesh n).map (fun q => q.1.2),
      arrivalSupported (Real.log start.gap) ell y := by
    rw [he]
    exact continuous_power_arrival _ _ _ _ n hn
  exact (ae_map_iff (measurable_snd.comp measurable_fst).aemeasurable
    (arrivalSupported_measurable _ _)).mp h

end NumberTheoryLean.ContinuousArrivalSupport

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SuccessfulTailTransport
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SuccessfulTailTransport

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling PersistentFailureFlag ActualFlagInvariant
open RegeneratingInverseBands InvariantInverseWeights ArrivalKernelGeometry
open SuccessfulRewardComparison ContinuousArrivalSupport ContinuousCompletedOccupation
open ContinuousKilledBins CostPrefixTransport

variable {w ell S : ℝ} {start : Node}

theorem positive_completed_occupation_le (v ell S : ℝ) {F : CostState → ℝ≥0∞} (hF : Measurable F)
    (N : ℕ) (z : CostState) :
    (∑ n ∈ range N,∫⁻ y,liftReward F y ∂((continuousChain v ell S)^(n+1)) (.inl z)) ≤
      ∫⁻ y,F y ∂inclusiveOccupation z := by
  refine le_trans ?_ (completed_finite_occupation_le v ell S hF (N+1) z)
  rw [Finset.sum_range_succ']
  exact le_add_of_nonneg_right zero_le

theorem actual_clean_tail_transport : ∃ L : ℝ,0 < L ∧
    ∀ w ell S : ℝ,∀ start : Node,∀ _hw : normalizationThreshold ≤ w,
      ∀ _hell : 1 ≤ ell,∀ _hS0 : 0 ≤ S,∀ _hS : S ≤ (Real.log w)^3,
      ∀ _hr : 0 < start.gap,∀ hs : Valid start.side start.ratio,∀ _hsS : start.ratio ≤ S,
      3 ≤ S → ∀ mesh : ℝ,0 < mesh → ∀ N : ℕ,
        4*(N:ℝ)*mesh ≤ 1 → L*(1+S)^3*mesh ≤ 1 → ∀ M : ℕ,∀ c : ℝ,0 < c →
        (∑ n ∈ range N,∫⁻ q,cleanReward c (3*((M:ℝ)+1)) q
          ∂CouplingData.sourceLaw w ell S start hs mesh (n+1)) ≤
          ENNReal.ofReal 27*(∫⁻ z,WeightedGapTail.tailReward (c/3) (Real.log start.gap) ell M z
            ∂inclusiveOccupation (FlaggedSourceStart.sourceCostState hs)) := by
  obtain ⟨L,hL,hcompare⟩ := actual_good_tail_comparison
  refine ⟨L,hL,?_⟩
  intro w ell S start hw hell hS0 hS hr hs hsS hS3 mesh hm N hclock hsmall M c hc
  let F := WeightedGapTail.tailReward (c/3) (Real.log start.gap) ell M
  have hF : Measurable F := WeightedGapTail.tailReward_measurable _ _ _ _
  have hpoint : ∀ n,1 ≤ n → n ≤ N →
      ∀ᵐ q ∂CouplingData.sourceLaw w ell S start hs mesh n,
        cleanReward c (3*((M:ℝ)+1)) q ≤ ENNReal.ofReal 27*liftReward F q.1.2 := by
    intro n hn hnN
    have hg := FlaggedSourceStart.sourceLaw_good hw hell hS0 hS hr hs hsS hm n
    rw [CouplingData.sourceLaw_eq hw hell hS0 hS hr hs hsS] at hg
    filter_upwards [hg,source_arrival hw hell hS0 hS hr hs hsS mesh n hn] with q hgood harr
    by_cases hb : q.2 = false
    · have hgood := hgood hb
      rw [cleanReward,ite_eq_left hb]
      rcases q with ⟨⟨p,y⟩,b⟩
      cases p with
      | none => exact zero_le
      | some h =>
        cases y with
        | inr u => exact False.elim hgood
        | inl z =>
          have hnum : 4*(n:ℝ)*mesh ≤ 1 := by
            have hnR : (n:ℝ) ≤ (N:ℝ) := by exact_mod_cast hnN
            exact (mul_le_mul_of_nonneg_right (by linarith : 4*(n:ℝ) ≤ 4*(N:ℝ)) hm.le).trans hclock
          exact hcompare w ell S hell hS3 start hr hs hsS (Real.log start.gap) mesh n M hnum hsmall h z hgood harr c hc
    · rw [cleanReward,ite_eq_right hb]
      exact zero_le
  have hone : ∀ n,1 ≤ n → n ≤ N →
      (∫⁻ q,cleanReward c (3*((M:ℝ)+1)) q ∂CouplingData.sourceLaw w ell S start hs mesh n) ≤
        ENNReal.ofReal 27*(∫⁻ y,liftReward F y
          ∂((continuousChain (Real.log start.gap) ell S)^n) (.inl (FlaggedSourceStart.sourceCostState hs))) := by
    intro n hn hnN
    have he := FlaggedSourceStart.sourceLaw_continuous hw hell hS0 hS hr hs hsS mesh n
    rw [CouplingData.sourceLaw_eq hw hell hS0 hS hr hs hsS] at he
    calc
      _ ≤ ∫⁻ q,ENNReal.ofReal 27*liftReward F q.1.2 ∂CouplingData.sourceLaw w ell S start hs mesh n :=
        lintegral_mono_ae (hpoint n hn hnN)
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,← he,
          lintegral_map (g := fun q : FlagState (JointState w ell S start) => q.1.2) (liftReward_measurable hF) (measurable_snd.comp measurable_fst)]
  calc
    _ ≤ ∑ n ∈ range N,ENNReal.ofReal 27*(∫⁻ y,liftReward F y
        ∂((continuousChain (Real.log start.gap) ell S)^(n+1)) (.inl (FlaggedSourceStart.sourceCostState hs))) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hone (n+1) (by omega) (by have hh := Finset.mem_range.mp hn; omega)
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (positive_completed_occupation_le _ _ _ hF N _) zero_le

end NumberTheoryLean.SuccessfulTailTransport

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ScaledOriginalTail
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceSuccessfulTail

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry FinitePathMeasures TransitionKernels PrimeHistories PrimeKilledChain
open SuccessfulTailTransport ExponentialMesh HorizonMeshSmallness UniformBudgetRate LowStateHorizon
open RegeneratingInverseBands CostPrefixTransport

theorem even_source_cost_state {start : Node} (hs : Valid start.side start.ratio)
    (hi : start.side = .even) :
    ∃ s : EvenState,s.1 = start.ratio ∧ FlaggedSourceStart.sourceCostState hs = (.inl s,0) := by
  cases start with
  | mk i s r cap closed =>
    change i = .even at hi
    subst i
    exact ⟨⟨s,hs⟩,rfl,rfl⟩

theorem source_successful_tail_jb247_oai (κ d c : ℝ) (hκ : 0 < κ) (hd : 0 < d) (hc : 0 < c) :
    ∃ b : ℕ → ℝ≥0∞,Tendsto b atTop (𝓝 0) ∧ ∃ w₀ : ℝ,1 < w₀ ∧
      ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ,∀ start : Node,∀ hs : Valid start.side start.ratio,
        1 ≤ ell → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
        0 < start.gap → start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        let S := (Real.log B)^2
        let N := sourceHorizon S B
        ∀ M : ℕ,(∑ n ∈ range N,∫⁻ q,cleanReward c (3*((M:ℝ)+1)) q
          ∂CouplingData.sourceLaw w ell S start hs (mesh κ w) (n+1)) ≤ b M := by
  obtain ⟨L,hL,htransport⟩ := actual_clean_tail_transport
  obtain ⟨b,hb,hband⟩ := EvenInverseBands.source_exponential_reward_tail (show 0 < c/3 by linarith)
  refine ⟨fun M => ENNReal.ofReal 27*b M,?_,?_⟩
  · simpa only [mul_zero] using ENNReal.Tendsto.const_mul (a:=ENNReal.ofReal 27) hb (Or.inr ENNReal.ofReal_ne_top)
  let A := 5*d^3
  have hA : 0 ≤ A := by dsimp [A] <;> positivity
  have hevent := (horizon_mesh_smallness hA hL.le hκ).and
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (d^2)))
  obtain ⟨wAux,hwAux⟩ := eventually_atTop.mp hevent
  refine ⟨max normalizationThreshold wAux,normalizationThreshold_gt_one.trans_le (le_max_left _ _),?_⟩
  intro w hw ell B start hs hell _hB hlogB hcomp hr hi h199 h23
  dsimp only
  intro M
  let S := (Real.log B)^2
  let N := sourceHorizon S B
  have hnorm : normalizationThreshold ≤ w := (le_max_left _ _).trans hw
  have hwe := hwAux w ((le_max_right _ _).trans hw)
  have hscale := source_scale_bound hwe.2 hlogB hcomp
  have hS0 : 0 ≤ S := sq_nonneg _
  have hS3 : 3 ≤ S := by dsimp [S] <;> nlinarith
  have hsS : start.ratio ≤ S := by linarith
  have hnum := hwe.1 S hS0 hscale.1 N hscale.2
  have hsum := htransport w ell S start hnorm hell hS0 hscale.1 hr hs hsS hS3
    (mesh κ w) (mesh_pos κ w) N hnum.2.1 hnum.2.2.1 M c hc
  obtain ⟨s,hsv,hcost⟩ := even_source_cost_state hs hi
  have htail := hband M s (by simpa only [hsv] using h199) (by simpa only [hsv] using h23)
    (Real.log start.gap) ell hell
  rw [hcost] at hsum
  exact hsum.trans (mul_le_mul_of_nonneg_left htail zero_le)

end NumberTheoryLean.SourceSuccessfulTail

end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.NumberTheoryLean.SourceSuccessfulTail.source_successful_tail_jb247_oai := @OAI.Erdos970.NumberTheoryLean.SourceSuccessfulTail.source_successful_tail_jb247_oai
