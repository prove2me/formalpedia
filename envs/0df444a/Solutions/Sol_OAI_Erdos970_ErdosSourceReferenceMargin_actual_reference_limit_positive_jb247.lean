-- Prove2me | solution 1 for OAI.Erdos970.ErdosSourceReferenceMargin.actual_reference_limit_positive_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:56:29.863976+00:00
-- url     : https://prove2.me/submissions/1a4ea903-d776-4c59-b6c2-c547b599f5fa

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
import Mathlib.Analysis.Calculus.Deriv.Slope
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
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
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
import Mathlib.Data.List.OfFn
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
import Mathlib.Probability.Distributions.Bernoulli
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
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UrysohnsLemma
import Definitions.Def_OAIQ247J007
import Theorems.Thm_OAI_Erdos970_ErdosContinuousOmission_actual_loss_summable_jb247
import Theorems.Thm_OAI_Erdos970_ErdosContinuousOmission_actual_signed_loss_series_jb247
import Theorems.Thm_OAI_Erdos970_ErdosOmissionBindings_actual_first_three_partial_sum_lt_jb247
import Theorems.Thm_OAI_Erdos970_ErdosOmissionTail_combinedDensity_integrable_jb247
import Theorems.Thm_OAI_Erdos970_ErdosOmissionTail_combinedDensity_integral_jb247

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_WeightFutureIntegrals
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.DeficitFutureIntegrals

open Filter Set MeasureTheory
open scoped Topology
open LinearSieveFunctions BuchstabBridge NormalizedDeficits

theorem future_integral_of_mass {a b : ℝ → ℝ} {base : ℝ} (hbase : 1 ≤ base)
    (ha : ContinuousOn a (Ioi 0))
    (hb : ∀ t, base - 1 < t → 0 ≤ b t)
    (hd : ∀ t, base < t → HasDerivAt (fun u => u * a u) (-b (t - 1)) t)
    (hl : Tendsto (fun t => t * a t) atTop (𝓝 0))
    {s : ℝ} (hs : base ≤ s) :
    IntegrableOn b (Ioi (s - 1)) ∧ s * a s = ∫ t in Ioi (s - 1), b t := by
  let H : ℝ → ℝ := fun t => (t + 1) * a (t + 1)
  have hs0 : 0 < s := lt_of_lt_of_le (by linarith : 0 < base) hs
  have hc : ContinuousWithinAt H (Ici (s - 1)) (s - 1) := by
    have hm : ContinuousAt (fun t => t * a t) s :=
      continuousAt_id.mul (ha.continuousAt (Ioi_mem_nhds hs0))
    have hm' : ContinuousAt (fun t => t * a t) ((s - 1) + 1) := by simpa only [sub_add_cancel] using hm
    have hc' := hm'.comp (f := fun t : ℝ => t + 1) (x := s - 1)
      ((continuous_id.add continuous_const : Continuous (fun t : ℝ => t + 1)).continuousAt)
    convert! hc'.continuousWithinAt using 1
    all_goals try with_reducible_and_instances rfl
  have hder : ∀ t ∈ Ioi (s - 1), HasDerivAt H (-b t) t := by
    intro t ht
    have hdt := (hd (t + 1) (by change s - 1 < t at ht; linarith)).comp t
      ((hasDerivAt_id t).add_const 1)
    convert! hdt using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hnonpos : ∀ t ∈ Ioi (s - 1), -b t ≤ 0 := by
    intro t ht
    exact neg_nonpos.mpr (hb t (by change s - 1 < t at ht; linarith))
  have hshift : Tendsto (fun t : ℝ => t + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro v
    exact eventually_atTop.mpr ⟨v - 1, fun t ht => by linarith⟩
  have hlim : Tendsto H atTop (𝓝 0) := hl.comp hshift
  have hint := integrableOn_Ioi_deriv_of_nonpos hc hder hnonpos hlim
  have heq := integral_Ioi_of_hasDerivAt_of_nonpos hc hder hnonpos hlim
  constructor
  · exact integrable_neg_iff.mp hint
  · simp only [integral_neg, H, sub_add_cancel, zero_sub] at heq
    linarith

theorem lowerDeficit_nonneg (s : ℝ) : 0 ≤ lowerDeficit s := by
  by_cases hs : 1 ≤ s
  · exact (deficits_pos hs).1.le
  · simp only [lowerDeficit, f_initial sieveA (by linarith : s ≤ 2), sub_zero, zero_le_one]

theorem lower_future_integral {s : ℝ} (hs : 2 ≤ s) :
    IntegrableOn upperDeficit (Ioi (s - 1)) ∧
      s * lowerDeficit s = ∫ t in Ioi (s - 1), upperDeficit t := by
  exact future_integral_of_mass (a := lowerDeficit) (b := upperDeficit) (base := 2) (by norm_num)
    lowerDeficit_continuous.continuousOn (fun t ht => (deficits_pos (s := t) (by linarith)).2.le)
    (fun _ ht => lowerDeficit_mass_deriv ht) lowerDeficit_mass_tendsto_zero hs

theorem upper_future_integral {s : ℝ} (hs : 1 ≤ s) :
    IntegrableOn lowerDeficit (Ioi (s - 1)) ∧
      s * upperDeficit s = ∫ t in Ioi (s - 1), lowerDeficit t := by
  exact future_integral_of_mass (a := upperDeficit) (b := lowerDeficit) (base := 1) le_rfl
    ((F_continuousOn sieveA).sub continuousOn_const) (fun t _ => lowerDeficit_nonneg t)
    (fun _ ht => upperDeficit_mass_deriv_of_one_lt ht) upperDeficit_mass_tendsto_zero hs

end NumberTheoryLean.DeficitFutureIntegrals

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FiniteHistorySupport
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

end NumberTheoryLean.FinitePathGeometry



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

theorem oddDensity_nonneg (s : ℝ) : 0 ≤ oddDensity s := by
  by_cases hs : 1 ≤ s
  · rw [oddDensity, indicator_of_mem (show s ∈ Ici (1 : ℝ) from hs)]
    exact mul_nonneg (oddFactor_bounds hs).1 (phiOdd_pos s).le
  · rw [oddDensity, indicator_of_notMem (show s ∉ Ici (1 : ℝ) from hs)]

end Erdos970Dependency.InvariantDensities

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_DeficitIntegralValues
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory
namespace Erdos970Dependency.DeficitIntegralValues
open NumberTheoryLean.LinearSieveFunctions NumberTheoryLean.BuchstabBridge
open NumberTheoryLean.NormalizedDeficits NumberTheoryLean.DeficitFutureIntegrals

theorem shift_indicator (f : ℝ → ℝ) (a d : ℝ) :
    (fun s ↦ (Ioi a).indicator f (s - d)) = (Ioi (a + d)).indicator (fun s ↦ f (s - d)) := by
  funext s
  by_cases hs : a + d < s
  · rw [indicator_of_mem (show s ∈ Ioi (a + d) from hs),
      indicator_of_mem (show s - d ∈ Ioi a by change a < s - d; linarith)]
  · rw [indicator_of_notMem (show s ∉ Ioi (a + d) from hs),
      indicator_of_notMem (show s - d ∉ Ioi a by change ¬a < s - d; linarith)]

theorem integrableOn_shift_Ioi {f : ℝ → ℝ} {a : ℝ} (hf : IntegrableOn f (Ioi a)) (d : ℝ) :
    IntegrableOn (fun s ↦ f (s - d)) (Ioi (a + d)) := by
  have h := ((integrable_indicator_iff measurableSet_Ioi).mpr hf).comp_sub_right d
  rw [shift_indicator] at h
  exact (integrable_indicator_iff measurableSet_Ioi).mp h

theorem integral_shift_Ioi (f : ℝ → ℝ) (a d : ℝ) :
    (∫ s in Ioi (a + d), f (s - d)) = ∫ s in Ioi a, f s := by
  have h := integral_sub_right_eq_self (μ := (volume : Measure ℝ)) ((Ioi a).indicator f) d
  rw [shift_indicator, integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Ioi] at h
  exact h

theorem upper_integral_one : IntegrableOn upperDeficit (Ioi (1 : ℝ)) ∧
    (∫ s in Ioi (1 : ℝ), upperDeficit s) = 2 := by
  have h := lower_future_integral (s := 2) (by norm_num)
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num] at h
  refine ⟨h.1, ?_⟩
  rw [← h.2]
  norm_num [lowerDeficit, f_initial sieveA (s := 2) (by norm_num)]

theorem lower_integral_zero : IntegrableOn lowerDeficit (Ioi (0 : ℝ)) ∧
    (∫ s in Ioi (0 : ℝ), lowerDeficit s) = sieveA - 1 := by
  have h := upper_future_integral (s := 1) (by norm_num)
  norm_num only [show (1 : ℝ) - 1 = 0 by norm_num, one_mul] at h
  refine ⟨h.1, ?_⟩
  rw [← h.2]
  norm_num [upperDeficit, F_initial sieveA (s := 1) (by norm_num) (by norm_num)]

theorem lower_integral_two : IntegrableOn lowerDeficit (Ioi (2 : ℝ)) ∧
    (∫ s in Ioi (2 : ℝ), lowerDeficit s) = sieveA - 3 := by
  have h := upper_future_integral (s := 3) (by norm_num)
  norm_num only [show (3 : ℝ) - 1 = 2 by norm_num] at h
  refine ⟨h.1, ?_⟩
  rw [← h.2]
  simp only [upperDeficit, F_initial sieveA (s := 3) (by norm_num) (by norm_num)]
  ring

theorem even_majorant_integral :
    IntegrableOn (fun s ↦ lowerDeficit s + upperDeficit (s - 1)) (Ici (2 : ℝ)) ∧
      (∫ s in Ici (2 : ℝ), lowerDeficit s + upperDeficit (s - 1)) = sieveA - 1 := by
  have ha := lower_integral_two.1
  have hc : IntegrableOn (fun s ↦ upperDeficit (s - 1)) (Ioi (2 : ℝ)) := by
    simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using integrableOn_shift_Ioi upper_integral_one.1 1
  refine ⟨Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi (ha.add hc), ?_⟩
  rw [integral_Ici_eq_integral_Ioi, integral_add ha hc, lower_integral_two.2]
  have h := integral_shift_Ioi upperDeficit 1 1
  norm_num only [show (1 : ℝ) + 1 = 2 by norm_num] at h
  rw [h, upper_integral_one.2]
  ring

theorem odd_majorant_integral :
    IntegrableOn (fun s ↦ upperDeficit s + lowerDeficit (s - 1)) (Ici (1 : ℝ)) ∧
      (∫ s in Ici (1 : ℝ), upperDeficit s + lowerDeficit (s - 1)) = sieveA + 1 := by
  have hc := upper_integral_one.1
  have ha : IntegrableOn (fun s ↦ lowerDeficit (s - 1)) (Ioi (1 : ℝ)) := by
    simpa only [zero_add] using integrableOn_shift_Ioi lower_integral_zero.1 1
  refine ⟨Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi (hc.add ha), ?_⟩
  rw [integral_Ici_eq_integral_Ioi, integral_add hc ha, upper_integral_one.2]
  have h := integral_shift_Ioi lowerDeficit 0 1
  rw [zero_add] at h
  rw [h, lower_integral_zero.2]
  ring

end Erdos970Dependency.DeficitIntegralValues

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_VariableUpperIntegral
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open MeasureTheory Set
namespace ErdosContinuousBoundary

theorem continuous_variable_upper_integral
    (F : (ℝ×ℝ) → ℝ → ℝ) (hF : Continuous F.uncurry)
    (c : (ℝ×ℝ) → ℝ) (hc : Continuous c) :
    Continuous (fun p => ∫ x in (1:ℝ)..c p,F p x) := by
  let G : (ℝ×ℝ) → ℝ → ℝ := fun p t => F p ((c p-1)*t+1)
  have hG : Continuous G.uncurry := by
    change Continuous (F.uncurry ∘ (fun q : (ℝ×ℝ)×ℝ => (q.1,(c q.1-1)*q.2+1)))
    apply hF.comp
    exact continuous_fst.prodMk
      (((hc.comp continuous_fst).sub continuous_const).mul continuous_snd |>.add continuous_const)
  have hi : Continuous (fun p => ∫ t in Icc (0:ℝ) 1,G p t) :=
    continuous_parametric_integral_of_continuous hG isCompact_Icc
  have heq (p : ℝ×ℝ) : (c p-1)*(∫ t in Icc (0:ℝ) 1,G p t)=∫ x in (1:ℝ)..c p,F p x := by
    have h := intervalIntegral.smul_integral_comp_mul_add (a:=0) (b:=1) (fun x => F p x) (c p-1) 1
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),← integral_Icc_eq_integral_Ioc] at h
    simpa only [smul_eq_mul,mul_zero,zero_add,mul_one,sub_add_cancel,G] using h
  exact ((hc.sub continuous_const).mul hi).congr heq

end ErdosContinuousBoundary

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceWeightedQuadrature
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


section

open _root_.Set
namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceAdmission

theorem upperCutoff_bounds (i : Side) (r b : ℝ) : 1 ≤ upperCutoff i r b ∧ upperCutoff i r b ≤ 2 := by
  cases i
  · exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
  · exact ⟨le_max_left _ _,max_le (by norm_num) ((min_le_left _ _).trans (min_le_left _ _))⟩

theorem upperCutoff_continuous (i : Side) :
    Continuous (fun p : ℝ×ℝ => upperCutoff i p.1 p.2) := by
  cases i <;> unfold upperCutoff <;> fun_prop

theorem strong_gate_below_two {r x : ℝ} (hx : x ≤ 2) :
    childAdmitted .odd r x ↔ x ≤ (r-2)/2 := by
  change max (2*x) (x+2) ≤ r-x ↔ x ≤ (r-2)/2
  rw [max_eq_right (by linarith : 2*x ≤ x+2)]
  constructor <;> intro h <;> linarith

theorem le_clipped_upper {x t : ℝ} (hx : 1 < x) : x ≤ max 1 t ↔ x ≤ t := by
  rw [le_max_iff]
  exact or_iff_right (not_le_of_gt hx)

theorem mem_upperCutoff (i : Side) (r b x : ℝ) :
    x ∈ Ioc 1 (upperCutoff i r b) ↔
      1 < x ∧ x ≤ 2 ∧ x ≤ b ∧ childAdmitted i r x := by
  constructor
  · intro hx
    cases i with
    | even =>
      have h : x ≤ min 2 b := (le_clipped_upper hx.1).mp hx.2
      exact ⟨hx.1,(le_min_iff.mp h).1,(le_min_iff.mp h).2,trivial⟩
    | odd =>
      have h : x ≤ min (min 2 b) ((r-2)/2) := (le_clipped_upper hx.1).mp hx.2
      obtain ⟨hb,hgate⟩ := le_min_iff.mp h
      obtain ⟨hx2,hxb⟩ := le_min_iff.mp hb
      exact ⟨hx.1,hx2,hxb,(strong_gate_below_two hx2).mpr hgate⟩
  · rintro ⟨hx,hx2,hxb,hgate⟩
    refine ⟨hx,?_⟩
    cases i with
    | even => exact (le_clipped_upper hx).mpr (le_min hx2 hxb)
    | odd => exact (le_clipped_upper hx).mpr (le_min (le_min hx2 hxb) ((strong_gate_below_two hx2).mp hgate))

end ErdosContinuousBoundary

end


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_GateIterates
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set
namespace ErdosContinuousOmission
open ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

theorem gate_integrand_continuous {H : Profile} (hH : JointContinuous H) (i : Side) (r : ℝ) :
    Continuous (fun x : ℝ => H i.flip (r-x) x/(max 1 x)) := by
  have hc : Continuous (fun x : ℝ => H i.flip (r-x) x) :=
    (hH i.flip).comp ((continuous_const.sub continuous_id).prodMk continuous_id)
  exact hc.div (continuous_const.max continuous_id) (fun x => ne_of_gt
    ((by norm_num : (0:ℝ)<1).trans_le (le_max_left 1 x)))

theorem gate_continuous {H : Profile} (hH : JointContinuous H) : JointContinuous (gate H) := by
  intro i
  let F : (ℝ×ℝ) → ℝ → ℝ := fun p x => H i.flip (p.1-x) x/(max 1 x)
  have hc : Continuous (fun q : (ℝ×ℝ)×ℝ => H i.flip (q.1.1-q.2) q.2) :=
    (hH i.flip).comp ((continuous_fst.fst.sub continuous_snd).prodMk continuous_snd)
  have hd : Continuous (fun q : (ℝ×ℝ)×ℝ => max 1 q.2) := continuous_const.max continuous_snd
  have hF : Continuous F.uncurry := hc.div hd (fun q => ne_of_gt
    ((by norm_num : (0:ℝ)<1).trans_le (le_max_left 1 q.2)))
  exact continuous_variable_upper_integral F hF (fun p => upperCutoff i p.1 p.2) (upperCutoff_continuous i)

theorem gate_nonnegative {H : Profile} (hH : ∀ i r b,0 ≤ H i r b) (i : Side) (r b : ℝ) :
    0 ≤ gate H i r b := by
  apply intervalIntegral.integral_nonneg_of_forall (upperCutoff_bounds i r b).1
  intro x
  exact div_nonneg (hH i.flip (r-x) x) (zero_le_one.trans (le_max_left 1 x))

end ErdosContinuousOmission

end

section

open _root_.MeasureTheory _root_.Set
namespace ErdosContinuousOmission
open ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

theorem gateIterate_continuous {H : Profile} (hH : JointContinuous H) (n : ℕ) :
    JointContinuous (gateIterate n H) := by
  induction n with
  | zero => exact hH
  | succ n ih => exact gate_continuous ih

theorem gateIterate_nonnegative {H : Profile} (hH : ∀ i r b,0 ≤ H i r b) (n : ℕ) :
    ∀ i r b,0 ≤ gateIterate n H i r b := by
  induction n with
  | zero => exact hH
  | succ n ih => exact gate_nonnegative ih

end ErdosContinuousOmission

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_OmissionSeries
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set
namespace ErdosContinuousOmission
open ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

theorem baseCutoff_bounds (b : ℝ) : 1 ≤ baseCutoff b ∧ baseCutoff b ≤ 2 :=
  upperCutoff_bounds .even 0 b

theorem baseCutoff_on {b : ℝ} (hb1 : 1 ≤ b) (hb2 : b ≤ 2) : baseCutoff b=b := by
  rw [baseCutoff,min_eq_right hb2,max_eq_right hb1]

theorem cutoff_le_base (i : Side) (r b : ℝ) : upperCutoff i r b ≤ baseCutoff b := by
  cases i with
  | even => exact le_rfl
  | odd => exact max_le_max le_rfl (min_le_left _ _)

theorem survivorBaseline_continuous : Continuous survivorBaseline :=
  (continuous_const.max (continuous_const.min continuous_id)).inv₀ (fun b =>
    ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le (baseCutoff_bounds b).1))

theorem omissionForce_continuous : JointContinuous omissionForce := by
  intro i
  cases i with
  | even => exact continuous_const
  | odd =>
    have hc := (upperCutoff_continuous .odd).inv₀ (fun p => ne_of_gt
      ((by norm_num : (0:ℝ)<1).trans_le (upperCutoff_bounds .odd p.1 p.2).1))
    exact hc.sub (survivorBaseline_continuous.comp continuous_snd)

theorem omissionForce_nonnegative (i : Side) (r b : ℝ) : 0 ≤ omissionForce i r b := by
  cases i with
  | even => exact le_rfl
  | odd =>
    apply sub_nonneg.mpr
    have h := one_div_le_one_div_of_le
      ((by norm_num : (0:ℝ)<1).trans_le (upperCutoff_bounds .odd r b).1) (cutoff_le_base .odd r b)
    simpa only [one_div,survivorBaseline] using h

end ErdosContinuousOmission

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_OmissionForceIntegral
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.MeasureTheory
namespace ErdosContinuousOmission
open ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.ReferenceAdmission

theorem reciprocal_square_integral {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ x : ℝ in a..b,(x^2)⁻¹)=a⁻¹-b⁻¹ := by
  have hn : ∀ x ∈ uIcc a b,x ≠ 0 := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    linarith [hx.1]
  have hc : ContinuousOn (fun x : ℝ => (x^2)⁻¹) (uIcc a b) :=
    (continuous_id.pow 2).continuousOn.inv₀ (fun x hx => pow_ne_zero 2 (hn x hx))
  have hd : ∀ x ∈ uIcc a b,HasDerivAt (fun t : ℝ => -t⁻¹) ((x^2)⁻¹) x := by
    intro x hx
    simpa only [neg_neg] using! (hasDerivAt_inv (hn x hx)).neg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable (μ := volume))]
  ring

theorem omissionForce_odd_integral (r b : ℝ) :
    omissionForce .odd r b=∫ x : ℝ in upperCutoff .odd r b..baseCutoff b,(x^2)⁻¹ := by
  rw [reciprocal_square_integral (upperCutoff_bounds .odd r b).1 (cutoff_le_base .odd r b)]
  rfl

theorem literal_omission_window (r b x : ℝ) :
    x ∈ Ioc (upperCutoff .odd r b) (baseCutoff b) ↔
      1 < x ∧ x ≤ 2 ∧ x ≤ b ∧ ¬childAdmitted .odd r x := by
  constructor
  · intro hx
    have hx1 : 1 < x := (upperCutoff_bounds .odd r b).1.trans_lt hx.1
    have he : x ∈ Ioc 1 (upperCutoff .even r b) := ⟨hx1,hx.2⟩
    obtain ⟨_,hx2,hxb,_⟩ := (mem_upperCutoff .even r b x).mp he
    refine ⟨hx1,hx2,hxb,?_⟩
    intro hgate
    have ha := (mem_upperCutoff .odd r b x).mpr ⟨hx1,hx2,hxb,hgate⟩
    exact (not_lt_of_ge ha.2) hx.1
  · rintro ⟨hx1,hx2,hxb,hbad⟩
    have he := (mem_upperCutoff .even r b x).mpr ⟨hx1,hx2,hxb,trivial⟩
    refine ⟨?_,he.2⟩
    apply lt_of_not_ge
    intro hcap
    exact hbad ((mem_upperCutoff .odd r b x).mp ⟨hx1,hcap⟩).2.2.2

end ErdosContinuousOmission

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_LossBounds
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosBoundaryLoss

theorem log_two_bounds : (69:ℝ)/100 < Real.log 2 ∧ Real.log 2 < (7:ℝ)/10 := by
  constructor
  · linarith [Real.log_two_gt_d9]
  · linarith [Real.log_two_lt_d9]

end ErdosBoundaryLoss

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ScalarFreeGate
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosContinuousOmission
open NumberTheoryLean.FinitePathGeometry

theorem gate_zero_of_side (H : Profile) (i : Side)
    (hH : ∀ r b,H i.flip r b=0) (r b : ℝ) : gate H i r b=0 := by
  simp only [gate,hH,zero_div,intervalIntegral.integral_zero]

theorem omission_wrong_parity_zero (n : ℕ) :
    (∀ r b,gateIterate (2*n) omissionForce .even r b=0) ∧
      (∀ r b,gateIterate (2*n+1) omissionForce .odd r b=0) := by
  induction n with
  | zero =>
    constructor
    · intro r b; rfl
    · intro r b
      exact gate_zero_of_side omissionForce .odd (fun _ _ => rfl) r b
  | succ n ih =>
    have hE : ∀ r b,gateIterate (2*(n+1)) omissionForce .even r b=0 := by
      intro r b
      rw [show 2*(n+1)=(2*n+1)+1 by omega,gateIterate]
      exact gate_zero_of_side (gateIterate (2*n+1) omissionForce) .even ih.2 r b
    refine ⟨hE,?_⟩
    intro r b
    rw [gateIterate]
    exact gate_zero_of_side (gateIterate (2*(n+1)) omissionForce) .odd hE r b

end ErdosContinuousOmission

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

theorem freeGate_continuous {H : Profile} (hH : JointContinuous H) : JointContinuous (freeGate H) := by
  intro i
  let F : (ℝ×ℝ) → ℝ → ℝ := fun p x => H i.flip (p.1-x) x/(max 1 x)
  have hc : Continuous (fun q : (ℝ×ℝ)×ℝ => H i.flip (q.1.1-q.2) q.2) :=
    (hH i.flip).comp ((continuous_fst.fst.sub continuous_snd).prodMk continuous_snd)
  have hd : Continuous (fun q : (ℝ×ℝ)×ℝ => max 1 q.2) := continuous_const.max continuous_snd
  have hF : Continuous F.uncurry := hc.div hd (fun q => ne_of_gt
    ((by norm_num : (0:ℝ)<1).trans_le (le_max_left 1 q.2)))
  have hb : Continuous (fun p : ℝ×ℝ => baseCutoff p.2) :=
    continuous_const.max (continuous_const.min continuous_snd)
  exact continuous_variable_upper_integral F hF (fun p => baseCutoff p.2) hb

theorem freeGate_nonnegative {H : Profile} (hH : ∀ i r b,0 ≤ H i r b) (i : Side) (r b : ℝ) :
    0 ≤ freeGate H i r b := by
  apply intervalIntegral.integral_nonneg_of_forall (baseCutoff_bounds b).1
  intro x
  exact div_nonneg (hH i.flip (r-x) x) (zero_le_one.trans (le_max_left 1 x))

theorem gate_le_freeGate {H : Profile} (hH : JointContinuous H)
    (hpos : ∀ i r b,0 ≤ H i r b) (i : Side) (r b : ℝ) : gate H i r b ≤ freeGate H i r b := by
  have hc := gate_integrand_continuous hH i r
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 1 (upperCutoff i r b))
    (hc.intervalIntegrable (μ := volume) (upperCutoff i r b) (baseCutoff b))
  have hp : 0 ≤ ∫ x in upperCutoff i r b..baseCutoff b,H i.flip (r-x) x/(max 1 x) := by
    apply intervalIntegral.integral_nonneg_of_forall (cutoff_le_base i r b)
    intro x
    exact div_nonneg (hpos i.flip (r-x) x) (zero_le_one.trans (le_max_left 1 x))
  unfold gate freeGate
  linarith

theorem gate_mono {H G : Profile} (hH : JointContinuous H) (hG : JointContinuous G)
    (h : ∀ i r b,H i r b ≤ G i r b) (i : Side) (r b : ℝ) : gate H i r b ≤ gate G i r b := by
  apply intervalIntegral.integral_mono_on (upperCutoff_bounds i r b).1
    ((gate_integrand_continuous hH i r).intervalIntegrable 1 _)
    ((gate_integrand_continuous hG i r).intervalIntegrable 1 _)
  intro x _
  exact div_le_div_of_nonneg_right (h i.flip (r-x) x) (zero_le_one.trans (le_max_left 1 x))

theorem freeGateIterate_continuous {H : Profile} (hH : JointContinuous H) (n : ℕ) :
    JointContinuous (freeGateIterate n H) := by
  induction n with
  | zero => exact hH
  | succ n ih => exact freeGate_continuous ih

theorem freeGateIterate_nonnegative {H : Profile} (hH : ∀ i r b,0 ≤ H i r b) (n : ℕ) :
    ∀ i r b,0 ≤ freeGateIterate n H i r b := by
  induction n with
  | zero => exact hH
  | succ n ih => exact freeGate_nonnegative ih

theorem gateIterate_prefix_le {H : Profile} (hH : JointContinuous H)
    (hpos : ∀ i r b,0 ≤ H i r b) (k n : ℕ) :
    ∀ i r b,gateIterate (k+n) H i r b ≤ freeGateIterate k (gateIterate n H) i r b := by
  induction k with
  | zero => intro i r b; simp only [zero_add,freeGateIterate,le_refl]
  | succ k ih =>
    intro i r b
    rw [show k+1+n=(k+n)+1 by omega,gateIterate,freeGateIterate]
    calc
      _ ≤ gate (freeGateIterate k (gateIterate n H)) i r b :=
        gate_mono (gateIterate_continuous hH _) (freeGateIterate_continuous (gateIterate_continuous hH n) k) ih i r b
      _ ≤ _ := gate_le_freeGate (freeGateIterate_continuous (gateIterate_continuous hH n) k)
        (freeGateIterate_nonnegative (gateIterate_nonnegative hpos n) k) i r b

theorem actual_omission_prefix_le (k : ℕ) (i : Side) (r b : ℝ) :
    gateIterate (k+2) omissionForce i r b ≤
      freeGateIterate k (gateIterate 2 omissionForce) i r b :=
  gateIterate_prefix_le omissionForce_continuous omissionForce_nonnegative k 2 i r b

end ErdosOmissionTail

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionTail

theorem last_window_width {S a b c : ℝ} (ha : a ≤ 2) (hb : 1 ≤ b) (hc : 1 ≤ c) (hab : b ≤ a) :
    1 ≤ (S+a+b+2*c)-(S+2*a) ∧ (S+a+b+2*c)-(S+2*a) ≤ 2*c := by
  constructor <;> linarith

theorem last_window_square_bound {S a b c : ℝ} (hS : 0 ≤ S)
    (ha1 : 1 ≤ a) (ha2 : a ≤ 2) (hb1 : 1 ≤ b) (hc1 : 1 ≤ c) (hab : b ≤ a) :
    lastWindowCoefficient S a b c ≤ (S+a+b+2*c)^2/2 := by
  have hw := last_window_width (S := S) ha2 hb1 hc1 hab
  have hU : 0 ≤ S+a+b+2*c := by linarith
  have hV : 0 ≤ S+2*a := by linarith
  have hUV : S+2*a ≤ S+a+b+2*c := by linarith
  have hcube : (S+a+b+2*c)^3-(S+2*a)^3 ≤
      3*(S+a+b+2*c)^2*((S+a+b+2*c)-(S+2*a)) := by
    have hp := mul_nonneg (sq_nonneg ((S+a+b+2*c)-(S+2*a))) (show 0 ≤ 2*(S+a+b+2*c)+(S+2*a) by linarith)
    nlinarith
  have hwidth := mul_le_mul_of_nonneg_left hw.2 (mul_nonneg (by norm_num : (0:ℝ)≤3) (sq_nonneg (S+a+b+2*c)))
  unfold lastWindowCoefficient
  apply (div_le_iff₀ (by linarith : 0 < 12*c)).mpr
  nlinarith

theorem last_window_mean_bound (k : ℕ) {S a b c : ℝ}
    (hSlo : (k:ℝ) ≤ S) (hShi : S ≤ 2*(k:ℝ)) (hSc : (k:ℝ)*c ≤ S)
    (ha1 : 1 ≤ a) (ha2 : a ≤ 2) (hb1 : 1 ≤ b) (hba : b ≤ a)
    (hc1 : 1 ≤ c) (hcb : c ≤ b) :
    lastWindowCoefficient S a b c ≤
      (((k:ℝ)+4)^2/2)*(3*(S+a+b+c)/((k:ℝ)+3)-2) := by
  let m : ℝ := (k:ℝ)+3
  let T : ℝ := S+a+b+c
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
  have hm : 0 < m := by dsimp [m] <;> linarith
  have hTlo : m ≤ T := by dsimp [m,T] <;> linarith
  have hThi : T ≤ 2*m := by dsimp [m,T] <;> linarith
  have hTc : m*c ≤ T := by dsimp [m,T] <;> nlinarith
  have hmean1 : 1 ≤ T/m := (one_le_div hm).mpr hTlo
  have hmean2 : T/m ≤ 2 := (div_le_iff₀ hm).mpr hThi
  have hmean : (T/m)^2 ≤ 3*(T/m)-2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hmean1) (sub_nonneg.mpr hmean2)
    nlinarith
  have hA : S+a+b+2*c ≤ (m+1)*(T/m) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hm).mpr
    change (S+a+b+2*c)*m ≤ (m+1)*T
    dsimp [T] at hTc ⊢
    nlinarith
  have hA0 : 0 ≤ S+a+b+2*c := by linarith
  have hsq := mul_self_le_mul_self hA0 hA
  have hlin := mul_le_mul_of_nonneg_left hmean (sq_nonneg (m+1))
  have hw := last_window_square_bound (hSlo.trans' hk) ha1 ha2 hb1 hc1 hba
  have hme : (k:ℝ)+4=m+1 := by dsimp [m] <;> ring
  rw [hme]
  change lastWindowCoefficient S a b c ≤ ((m+1)^2/2)*(3*T/m-2)
  have hsq2 : (S+a+b+2*c)^2 ≤ (m+1)^2*(T/m)^2 := by nlinarith [hsq]
  calc
    _ ≤ (S+a+b+2*c)^2/2 := hw
    _ ≤ ((m+1)^2*(T/m)^2)/2 := div_le_div_of_nonneg_right hsq2 (by norm_num)
    _ ≤ ((m+1)^2*(3*(T/m)-2))/2 := div_le_div_of_nonneg_right hlin (by norm_num)
    _ = _ := by ring

end ErdosOmissionTail

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission

theorem orderedMass_continuous (n : ℕ) : Continuous (orderedMass n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hc : Continuous (fun x : ℝ => orderedMass n x/(max 1 x)) :=
      ih.div (continuous_const.max continuous_id) (fun x => ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le (le_max_left _ _)))
    exact (intervalIntegral.differentiable_integral_of_continuous hc).continuous.comp
      (continuous_const.max (continuous_const.min continuous_id))

theorem log_power_primitive (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => (Real.log x)^(n+1)/((n+1).factorial:ℝ))
      ((Real.log x)^n/((n.factorial:ℝ)*x)) x := by
  have hh := ((Real.hasDerivAt_log hx.ne').pow (n+1)).div_const ((n+1).factorial:ℝ)
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Nat.add_sub_cancel_right,Nat.factorial_succ,Nat.cast_mul]
  have hn : (n.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : ((n+1:ℕ):ℝ) ≠ 0 := by positivity
  field_simp

theorem orderedMass_eq (n : ℕ) {b : ℝ} (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    orderedMass n b=(Real.log b)^n/(n.factorial:ℝ) := by
  induction n generalizing b with
  | zero => norm_num [orderedMass]
  | succ n ih =>
    rw [orderedMass,baseCutoff_on hb1 hb2]
    have he : (∫ x in (1:ℝ)..b,orderedMass n x/(max 1 x))=
        ∫ x in (1:ℝ)..b,(Real.log x)^n/((n.factorial:ℝ)*x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hb1] at hx
      dsimp only
      rw [ih hx.1 (hx.2.trans hb2),max_eq_right hx.1]
      ring
    rw [he]
    have hn : (n.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hc : ContinuousOn (fun x : ℝ => (Real.log x)^n/((n.factorial:ℝ)*x)) (uIcc 1 b) := by
      rw [uIcc_of_le hb1]
      intro x hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := simp_all)
    have hd : ∀ x ∈ uIcc (1:ℝ) b,HasDerivAt
        (fun x : ℝ => (Real.log x)^(n+1)/((n+1).factorial:ℝ))
        ((Real.log x)^n/((n.factorial:ℝ)*x)) x := by
      intro x hx
      rw [uIcc_of_le hb1] at hx
      exact log_power_primitive n (by linarith [hx.1])
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable (μ := volume))]
    simp

end ErdosOmissionTail

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

theorem scalarFreeGate_continuous {H : ScalarProfile} (hH : ScalarContinuous H) :
    ScalarContinuous (scalarFreeGate H) :=
  freeGate_continuous (H := fun _ => H) (fun _ => hH) .even

theorem scalarFreeIterate_continuous {H : ScalarProfile} (hH : ScalarContinuous H) (n : ℕ) :
    ScalarContinuous (scalarFreeIterate n H) := by
  induction n with
  | zero => exact hH
  | succ n ih => exact scalarFreeGate_continuous ih

theorem freeGate_total {H : Profile} (hH : JointContinuous H) (r b : ℝ) :
    freeGate H .even r b+freeGate H .odd r b=
      scalarFreeGate (fun r b => H .even r b+H .odd r b) r b := by
  have he := (gate_integrand_continuous hH .even r).intervalIntegrable (μ := volume) 1 (baseCutoff b)
  have ho := (gate_integrand_continuous hH .odd r).intervalIntegrable (μ := volume) 1 (baseCutoff b)
  unfold freeGate scalarFreeGate
  rw [← intervalIntegral.integral_add he ho]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only [Side.flip]
  ring

theorem freeGateIterate_total {H : Profile} (hH : JointContinuous H) (n : ℕ) (r b : ℝ) :
    freeGateIterate n H .even r b+freeGateIterate n H .odd r b=
      scalarFreeIterate n (fun r b => H .even r b+H .odd r b) r b := by
  induction n generalizing r b with
  | zero => rfl
  | succ n ih =>
    rw [freeGateIterate,freeGate_total (freeGateIterate_continuous hH n)]
    have he : (fun r b => freeGateIterate n H .even r b+freeGateIterate n H .odd r b)=
        scalarFreeIterate n (fun r b => H .even r b+H .odd r b) := by funext r b; exact ih r b
    rw [he]
    rfl

theorem terminalBlock_continuous : ScalarContinuous terminalBlock :=
  gateIterate_continuous omissionForce_continuous 2 .odd

theorem terminalBlock_nonnegative (r b : ℝ) : 0 ≤ terminalBlock r b :=
  gateIterate_nonnegative omissionForce_nonnegative 2 .odd r b

theorem actual_free_total (k : ℕ) (r b : ℝ) :
    freeGateIterate k (gateIterate 2 omissionForce) .even r b+
      freeGateIterate k (gateIterate 2 omissionForce) .odd r b=
        scalarFreeIterate k terminalBlock r b := by
  rw [freeGateIterate_total (gateIterate_continuous omissionForce_continuous 2)]
  have he : (fun r b => gateIterate 2 omissionForce .even r b+gateIterate 2 omissionForce .odd r b)=terminalBlock := by
    funext r b
    have hh := (omission_wrong_parity_zero 1).1 r b
    norm_num only [Nat.reduceMul] at hh
    rw [hh,zero_add]
    rfl
  rw [he]

theorem actual_combined_density_le (k : ℕ) (y : ℝ) :
    combinedDensity (k+2) y ≤ 2*y^2*scalarFreeIterate k terminalBlock (2*y+2) 2 := by
  have he := actual_omission_prefix_le k .even (2*y+2) 2
  have ho := actual_omission_prefix_le k .odd (2*y+2) 2
  have hpe := gateIterate_nonnegative omissionForce_nonnegative (k+2) .even (2*y+2) 2
  have hfE := freeGateIterate_nonnegative (gateIterate_nonnegative omissionForce_nonnegative 2) k .even (2*y+2) 2
  have hbE : (if 1 < y then omissionDensity (k+2) .even y else 0) ≤
      2*y^2*freeGateIterate k (gateIterate 2 omissionForce) .even (2*y+2) 2 := by
    by_cases h : 1 < y
    · rw [ite_eq_left h]
      have hh := mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num : (0:ℝ)≤2) (sq_nonneg y))
      unfold omissionDensity sourceWeight
      nlinarith
    · rw [ite_eq_right h]
      exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg y)) hfE
  have hbO : omissionDensity (k+2) .odd y ≤
      2*y^2*freeGateIterate k (gateIterate 2 omissionForce) .odd (2*y+2) 2 :=
    mul_le_mul_of_nonneg_left ho (mul_nonneg (by norm_num) (sq_nonneg y))
  have hh := actual_free_total k (2*y+2) 2
  unfold combinedDensity
  nlinarith

end ErdosOmissionTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_BoundedRectangleFubini
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
open _root_.Filter _root_.Erdos970.Filter
namespace ErdosOmissionBindings

theorem bounded_rectangle_integrable {f : ℝ×ℝ → ℝ} (hf : Measurable f)
    (a b c d C : ℝ)
    (hbound : ∀ x ∈ Icc a b,∀ y ∈ Icc c d,|f (x,y)| ≤ C) :
    Integrable f ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  let ν : Measure ℝ := volume.restrict (Icc c d)
  let : IsFiniteMeasure μ := ⟨by
    dsimp [μ]
    rw [Measure.restrict_apply_univ,Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  let : IsFiniteMeasure ν := ⟨by
    dsimp [ν]
    rw [Measure.restrict_apply_univ,Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  have hmem : ∀ᵐ p : ℝ×ℝ ∂μ.prod ν,p.1 ∈ Icc a b ∧ p.2 ∈ Icc c d := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.prod measurableSet_Icc)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact ⟨hx,hy⟩
  apply (integrable_const C).mono' hf.aestronglyMeasurable
  filter_upwards [hmem] with p hp
  simpa only [Real.norm_eq_abs] using hbound p.1 hp.1 p.2 hp.2

theorem bounded_rectangle_swap {f : ℝ×ℝ → ℝ} (hf : Measurable f)
    (a b c d C : ℝ)
    (hbound : ∀ x ∈ Icc a b,∀ y ∈ Icc c d,|f (x,y)| ≤ C) :
    (∫ x in Icc a b,∫ y in Icc c d,f (x,y))=
      ∫ y in Icc c d,∫ x in Icc a b,f (x,y) := by
  exact integral_integral_swap (bounded_rectangle_integrable hf a b c d C hbound)

end ErdosOmissionBindings

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_BoundedLossTerms
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceAdmission

theorem force_as_threshold (a y : ℝ) {b : ℝ} (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    omissionForce .odd (2*y+2-a) b=
      ∫ t : ℝ in 1..b,if y<a/2+t then (t^2)⁻¹ else 0 := by
  classical
  let r := 2*y+2-a
  have hb : baseCutoff b=b := baseCutoff_on hb1 hb2
  have hc : upperCutoff .odd r b ≤ b := by simpa only [hb] using cutoff_le_base .odd r b
  have hset : Ioc (upperCutoff .odd r b) b=Ioc (1:ℝ) b ∩ {t : ℝ | y<a/2+t} := by
    ext t
    have he := literal_omission_window r b t
    rw [hb] at he
    constructor
    · intro ht
      obtain ⟨ht1,ht2,htb,hbad⟩ := he.mp ht
      refine ⟨⟨ht1,htb⟩,?_⟩
      rw [strong_gate_below_two ht2] at hbad
      have hh := lt_of_not_ge hbad
      change y<a/2+t
      dsimp [r] at hh
      linarith
    · rintro ⟨⟨ht1,htb⟩,hy⟩
      apply he.mpr
      refine ⟨ht1,htb.trans hb2,htb,?_⟩
      rw [strong_gate_below_two (htb.trans hb2)]
      intro hgate
      change y<a/2+t at hy
      dsimp [r] at hgate
      linarith
  have hm : MeasurableSet {t : ℝ | y<a/2+t} :=
    measurableSet_lt measurable_const (measurable_const.add measurable_id)
  rw [omissionForce_odd_integral,hb,intervalIntegral.integral_of_le hc,intervalIntegral.integral_of_le hb1]
  change (∫ t in Ioc (upperCutoff .odd r b) b,(t^2)⁻¹)=
    ∫ t in Ioc (1:ℝ) b,({t : ℝ | y<a/2+t}).indicator (fun t => (t^2)⁻¹) t
  rw [setIntegral_indicator hm,hset]

theorem force_high_zero (i : Side) {r b : ℝ} (hr : 6 ≤ r) : omissionForce i r b=0 := by
  cases i with
  | even => rfl
  | odd =>
    have hc : upperCutoff .odd r b=baseCutoff b := by
      change max 1 (min (min 2 b) ((r-2)/2))=max 1 (min 2 b)
      rw [min_eq_left ((min_le_left 2 b).trans (by linarith))]
    simp only [omissionForce,hc,survivorBaseline,sub_self]

theorem iterated_force_high_zero (n : ℕ) (i : Side) {r b : ℝ}
    (hr : 2*(n:ℝ)+6 ≤ r) : gateIterate n omissionForce i r b=0 := by
  induction n generalizing i r b with
  | zero => exact force_high_zero i (by simpa only [Nat.cast_zero,mul_zero,zero_add] using hr)
  | succ n ih =>
    rw [gateIterate,gate]
    calc
      _ = ∫ _x : ℝ in 1..upperCutoff i r b,(0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (upperCutoff_bounds i r b).1] at hx
        dsimp only
        have hx2 : x ≤ 2 := hx.2.trans (upperCutoff_bounds i r b).2
        rw [ih i.flip (by push_cast at hr; linarith : 2*(n:ℝ)+6 ≤ r-x),zero_div]
      _ = 0 := by simp

end ErdosOmissionBindings

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_ThresholdFubini
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionBindings

theorem weighted_threshold_swap {P W T : ℝ → ℝ}
    (hP : Measurable P) (hW : Measurable W) (hT : Measurable T)
    (a Y b CP CW : ℝ) (hCP : 0 ≤ CP) (hCW : 0 ≤ CW)
    (hPb : ∀ y ∈ Icc a Y,|P y| ≤ CP)
    (hWb : ∀ t ∈ Icc (1:ℝ) b,|W t| ≤ CW)
    (hTb : ∀ t ∈ Icc (1:ℝ) b,a ≤ T t ∧ T t ≤ Y) :
    (∫ y in Icc a Y,P y*(∫ t in Icc (1:ℝ) b,if y<T t then W t else 0))=
      ∫ t in Icc (1:ℝ) b,W t*(∫ y : ℝ in a..T t,P y) := by
  classical
  let G : ℝ×ℝ → ℝ := fun p => if p.1<T p.2 then P p.1*W p.2 else 0
  have hG : Measurable G := Measurable.ite
    (measurableSet_lt measurable_fst (hT.comp measurable_snd))
    ((hP.comp measurable_fst).mul (hW.comp measurable_snd)) measurable_const
  have hb : ∀ y ∈ Icc a Y,∀ t ∈ Icc (1:ℝ) b,|G (y,t)| ≤ CP*CW := by
    intro y hy t ht
    dsimp only [G]
    split_ifs
    · rw [abs_mul]
      exact mul_le_mul (hPb y hy) (hWb t ht) (abs_nonneg _) hCP
    · simpa only [abs_zero] using mul_nonneg hCP hCW
  have hs := bounded_rectangle_swap hG a Y 1 b (CP*CW) hb
  have hleft (y : ℝ) : (∫ t in Icc (1:ℝ) b,G (y,t))=
      P y*(∫ t in Icc (1:ℝ) b,if y<T t then W t else 0) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp only [G]
    split_ifs <;> simp
  have hright (t : ℝ) (ht : t ∈ Icc (1:ℝ) b) :
      (∫ y in Icc a Y,G (y,t))=W t*(∫ y : ℝ in a..T t,P y) := by
    have hset : Icc a Y ∩ Iio (T t)=Ico a (T t) := by
      ext y
      constructor
      · rintro ⟨hy,hyT⟩; exact ⟨hy.1,hyT⟩
      · intro hy; exact ⟨⟨hy.1,hy.2.le.trans (hTb t ht).2⟩,hy.2⟩
    have he : (fun y : ℝ => G (y,t))=(Iio (T t)).indicator (fun y => W t*P y) := by
      funext y
      dsimp only [G]
      by_cases hh : y<T t
      · rw [ite_eq_left hh,indicator_of_mem (show y ∈ Iio (T t) from hh)]
        ring
      · rw [ite_eq_right hh,indicator_of_notMem (show y ∉ Iio (T t) from hh)]
    rw [he,setIntegral_indicator measurableSet_Iio,hset,integral_const_mul,
      integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le (hTb t ht).1]
  simp_rw [hleft] at hs
  rw [hs]
  exact setIntegral_congr_fun measurableSet_Icc hright

end ErdosOmissionBindings

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ScalarTailRecurrence
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission

theorem quadratic_window_integral (l u e : ℝ) :
    (∫ y : ℝ in l..u,y^2-e)=(u^3-l^3)/3-e*(u-l) := by
  have hp : IntervalIntegrable (fun y : ℝ => y^2) volume l u :=
    (continuous_id.pow 2).intervalIntegrable l u
  have hc : IntervalIntegrable (fun _y : ℝ => e) volume l u := intervalIntegrable_const
  rw [intervalIntegral.integral_sub hp hc,integral_pow,intervalIntegral.integral_const]
  norm_num
  ring

theorem integrated_force_window (a l Y b e : ℝ) (hl : 0 ≤ l) (hb1 : 1 ≤ b) (hb2 : b ≤ 2)
    (hlT : l ≤ a/2+1) (hTY : a/2+b ≤ Y) :
    (∫ y : ℝ in l..Y,(y^2-e)*omissionForce .odd (2*y+2-a) b)=
      ∫ t : ℝ in 1..b,(((a/2+t)^3-l^3)/3-e*(a/2+t-l))/(t^2) := by
  have hlY : l ≤ Y := by linarith
  have hY : 0 ≤ Y := hl.trans hlY
  have hP : Measurable (fun y : ℝ => y^2-e) := (measurable_id.pow_const 2).sub measurable_const
  have hW : Measurable (fun t : ℝ => (t^2)⁻¹) := (measurable_id.pow_const 2).inv
  have hT : Measurable (fun t : ℝ => a/2+t) := measurable_const.add measurable_id
  have hPb : ∀ y ∈ Icc l Y,|y^2-e| ≤ Y^2+|e| := by
    intro y hy
    have hy0 : 0 ≤ y := hl.trans hy.1
    have hy2 : y^2 ≤ Y^2 := by nlinarith [hy.2]
    calc
      _ ≤ |y^2|+|e| := abs_sub _ _
      _ = y^2+|e| := by rw [abs_of_nonneg (sq_nonneg y)]
      _ ≤ _ := add_le_add hy2 le_rfl
  have hWb : ∀ t ∈ Icc (1:ℝ) b,|(t^2)⁻¹| ≤ 1 := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    rw [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t))]
    apply (inv_le_one₀ (sq_pos_of_pos ht0)).mpr
    nlinarith [ht.1]
  have hTb : ∀ t ∈ Icc (1:ℝ) b,l ≤ a/2+t ∧ a/2+t ≤ Y := by
    intro t ht
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have h := weighted_threshold_swap hP hW hT l Y b (Y^2+|e|) 1
    (by positivity) (by norm_num) hPb hWb hTb
  have hinner (y : ℝ) :
      (∫ t in Icc (1:ℝ) b,if y<a/2+t then (t^2)⁻¹ else 0)=omissionForce .odd (2*y+2-a) b := by
    rw [force_as_threshold a y hb1 hb2,intervalIntegral.integral_of_le hb1,← integral_Icc_eq_integral_Ioc]
  simp_rw [hinner,quadratic_window_integral] at h
  rw [intervalIntegral.integral_of_le hlY,← integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hb1,← integral_Icc_eq_integral_Ioc]
  rw [h]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t _ht
  dsimp only
  ring

end ErdosOmissionBindings

end

section

open _root_.Set _root_.Erdos970.Set _root_.Filter _root_.Erdos970.Filter _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission ErdosOmissionBindings

theorem terminalBlock_high {r b : ℝ} (hr : 10 ≤ r) : terminalBlock r b=0 := by
  exact iterated_force_high_zero 2 .odd (by norm_num; exact hr)

theorem scalarFreeIterate_nonnegative {H : ScalarProfile} (hH : ∀ r b,0 ≤ H r b) (n : ℕ) :
    ∀ r b,0 ≤ scalarFreeIterate n H r b := by
  induction n with
  | zero => exact hH
  | succ n ih =>
    intro r b
    apply intervalIntegral.integral_nonneg_of_forall (baseCutoff_bounds b).1
    intro x
    exact div_nonneg (ih (r-x) x) (zero_le_one.trans (le_max_left _ _))

theorem scalarFreeIterate_high (n : ℕ) {r b : ℝ} (hr : 2*(n:ℝ)+10 ≤ r) :
    scalarFreeIterate n terminalBlock r b=0 := by
  induction n generalizing r b with
  | zero => exact terminalBlock_high (by simpa only [Nat.cast_zero,mul_zero,zero_add] using hr)
  | succ n ih =>
    rw [scalarFreeIterate,scalarFreeGate]
    calc
      _ = ∫ _x : ℝ in 1..baseCutoff b,(0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (baseCutoff_bounds b).1] at hx
        have hx2 : x ≤ 2 := hx.2.trans (baseCutoff_bounds b).2
        dsimp only
        rw [ih (by push_cast at hr; linarith : 2*(n:ℝ)+10 ≤ r-x),zero_div]
      _ = 0 := by simp

theorem scalarTailIntegrand_continuous (n : ℕ) (S b : ℝ) : Continuous (scalarTailIntegrand n S b) := by
  have hb : Continuous (fun p : ℝ×ℝ => scalarFreeIterate n terminalBlock p.1 p.2) :=
    scalarFreeIterate_continuous terminalBlock_continuous n
  have hp : Continuous (fun y : ℝ => (2*y+2-S,b)) := by fun_prop
  have hc : Continuous (fun y : ℝ => scalarFreeIterate n terminalBlock (2*y+2-S) b) := hb.comp hp
  exact (continuous_const.mul (continuous_id.pow 2)).mul hc

theorem scalarTailIntegrand_integrable (n : ℕ) (S b : ℝ) :
    IntegrableOn (scalarTailIntegrand n S b) (Ioi 0) := by
  let Y : ℝ := |S|+(n:ℝ)+5
  have hY : 0 ≤ Y := by dsimp [Y] <;> positivity
  have hc := (scalarTailIntegrand_continuous n S b).integrableOn_Icc (μ := volume) (a := 0) (b := Y)
  have hz : IntegrableOn (scalarTailIntegrand n S b) (Ioi Y) := by
    have hzero : IntegrableOn (fun _ : ℝ => (0:ℝ)) (Ioi Y) := integrable_zero ℝ ℝ _
    apply hzero.congr_fun _ measurableSet_Ioi
    intro y hy
    have hyY : Y < y := hy
    have hS := le_abs_self S
    have hS0 := abs_nonneg S
    have hh : 2*(n:ℝ)+10 ≤ 2*y+2-S := by dsimp [Y] at hyY <;> linarith
    simp only [scalarTailIntegrand,scalarFreeIterate_high n hh,mul_zero]
  have hu := hc.union hz
  rw [Icc_union_Ioi_eq_Ici hY] at hu
  exact hu.mono_set Ioi_subset_Ici_self

end ErdosOmissionTail

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission

theorem actual_loss_le_scalarTailMass (k : ℕ) : omissionLossTerm (k+2) ≤ scalarTailMass k 0 2 := by
  rw [← combinedDensity_integral_jb247]
  apply integral_mono_ae (combinedDensity_integrable_jb247 (k+2)) (scalarTailIntegrand_integrable k 0 2)
  exact Filter.Eventually.of_forall (fun y => by
    simpa only [scalarTailIntegrand,sub_zero] using actual_combined_density_le k y)

end ErdosOmissionTail

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

theorem omissionForce_le_one (i : Side) (r b : ℝ) : omissionForce i r b ≤ 1 := by
  cases i with
  | even => norm_num [omissionForce]
  | odd =>
    have hc := (upperCutoff_bounds .odd r b).1
    have hb : 0 ≤ (baseCutoff b)⁻¹ := inv_nonneg.mpr (by linarith [(baseCutoff_bounds b).1])
    have hi : (upperCutoff .odd r b)⁻¹ ≤ 1 :=
      (inv_le_one₀ (by linarith : 0 < upperCutoff .odd r b)).mpr hc
    unfold omissionForce survivorBaseline
    linarith

theorem freeGate_le_one {H : Profile} (hH : JointContinuous H)
    (hupper : ∀ i r b,H i r b ≤ 1) (i : Side) (r b : ℝ) : freeGate H i r b ≤ 1 := by
  have hc := gate_integrand_continuous hH i r
  have hi := intervalIntegral.integral_mono_on (baseCutoff_bounds b).1
    (hc.intervalIntegrable (μ := volume) 1 (baseCutoff b))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 1 (baseCutoff b))
    (fun x _ => (div_le_one (by linarith [le_max_left (1:ℝ) x] : 0 < max 1 x)).mpr
      ((hupper i.flip (r-x) x).trans (le_max_left _ _)))
  simp only [intervalIntegral.integral_const,smul_eq_mul,mul_one] at hi
  exact hi.trans (by linarith [(baseCutoff_bounds b).2])

theorem gateIterate_force_le_one (n : ℕ) (i : Side) (r b : ℝ) : gateIterate n omissionForce i r b ≤ 1 := by
  induction n generalizing i r b with
  | zero => exact omissionForce_le_one i r b
  | succ n ih =>
    exact (gate_le_freeGate (gateIterate_continuous omissionForce_continuous n)
      (gateIterate_nonnegative omissionForce_nonnegative n) i r b).trans
      (freeGate_le_one (gateIterate_continuous omissionForce_continuous n) ih i r b)

theorem terminalBlock_le_one (r b : ℝ) : terminalBlock r b ≤ 1 := gateIterate_force_le_one 2 .odd r b

theorem scalarFreeIterate_le_one (n : ℕ) (r b : ℝ) : scalarFreeIterate n terminalBlock r b ≤ 1 := by
  induction n generalizing r b with
  | zero => exact terminalBlock_le_one r b
  | succ n ih =>
    exact freeGate_le_one (H := fun _ => scalarFreeIterate n terminalBlock)
      (fun _ => scalarFreeIterate_continuous terminalBlock_continuous n) (fun _ => ih) .even r b

end ErdosOmissionTail

end

section

open _root_.Set _root_.Erdos970.Set _root_.Filter _root_.Erdos970.Filter _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission ErdosOmissionBindings

theorem scalarTailMass_bounded (n : ℕ) (S b Y : ℝ) (hY : 0 ≤ Y)
    (hhigh : S/2+(n:ℝ)+4 ≤ Y) :
    scalarTailMass n S b=∫ y : ℝ in 0..Y,scalarTailIntegrand n S b y := by
  have hz : (∫ y in Ioi Y,scalarTailIntegrand n S b y)=0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    change Y < y at hy
    have hh : 2*(n:ℝ)+10 ≤ 2*y+2-S := by linarith
    simp only [scalarTailIntegrand,scalarFreeIterate_high n hh,mul_zero]
  have hh := intervalIntegral.integral_Ioi_sub_Ioi (scalarTailIntegrand_integrable n S b) hY
  rw [hz,sub_zero] at hh
  exact hh

theorem scalarTailMass_succ (n : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    scalarTailMass (n+1) S b=∫ x : ℝ in 1..b,scalarTailMass n (S+x) x/x := by
  let Y : ℝ := S/2+(n:ℝ)+5
  have hY : 0 ≤ Y := by dsimp [Y] <;> positivity
  let G : ℝ×ℝ → ℝ := fun p =>
    2*p.1^2*scalarFreeIterate n terminalBlock (2*p.1+2-S-p.2) p.2/(max 1 p.2)
  have hpmap : Continuous (fun p : ℝ×ℝ => (2*p.1+2-S-p.2,p.2)) := by fun_prop
  have hphi : Continuous (fun p : ℝ×ℝ => scalarFreeIterate n terminalBlock (2*p.1+2-S-p.2) p.2) :=
    (scalarFreeIterate_continuous terminalBlock_continuous n).comp hpmap
  have hG : Continuous G := by
    apply ((continuous_const.mul (continuous_fst.pow 2)).mul hphi).div
      (continuous_const.max continuous_snd)
    intro p
    exact ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le (le_max_left _ _))
  have hbnd : ∀ y ∈ Icc (0:ℝ) Y,∀ x ∈ Icc (1:ℝ) b,|G (y,x)| ≤ 2*Y^2 := by
    intro y hy x _hx
    have hp := scalarFreeIterate_nonnegative terminalBlock_nonnegative n (2*y+2-S-x) x
    have hu := scalarFreeIterate_le_one n (2*y+2-S-x) x
    have hn : 0 ≤ 2*y^2*scalarFreeIterate n terminalBlock (2*y+2-S-x) x := by positivity
    have hh := mul_le_mul_of_nonneg_left hu (mul_nonneg (by norm_num : (0:ℝ)≤2) (sq_nonneg y))
    dsimp only [G]
    rw [abs_of_nonneg (div_nonneg hn (zero_le_one.trans (le_max_left _ _)))]
    apply (div_le_self hn (le_max_left (1:ℝ) x)).trans
    nlinarith [hy.1,hy.2]
  have hswap := bounded_rectangle_swap hG.measurable 0 Y 1 b (2*Y^2) hbnd
  have hswap' : (∫ y : ℝ in 0..Y,∫ x : ℝ in 1..b,G (y,x))=
      ∫ x : ℝ in 1..b,∫ y : ℝ in 0..Y,G (y,x) := by
    simpa only [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hY,
      ← intervalIntegral.integral_of_le hb1] using hswap
  rw [scalarTailMass_bounded (n+1) S b Y hY (by dsimp [Y]; push_cast <;> linarith)]
  have hleft : (∫ y : ℝ in 0..Y,scalarTailIntegrand (n+1) S b y)=
      ∫ y : ℝ in 0..Y,∫ x : ℝ in 1..b,G (y,x) := by
    apply intervalIntegral.integral_congr
    intro y _hy
    simp only [scalarTailIntegrand,scalarFreeIterate,scalarFreeGate,baseCutoff_on hb1 hb2,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only [G]
    ring
  rw [hleft,hswap']
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hb1] at hx
  have hx2 : x ≤ 2 := hx.2.trans hb2
  dsimp only
  rw [scalarTailMass_bounded n (S+x) x Y hY (by dsimp [Y] <;> linarith),← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro y _hy
  dsimp only [G,scalarTailIntegrand]
  rw [max_eq_right hx.1]
  have he : 2*y+2-S-x=2*y+2-(S+x) := by ring
  rw [he]

end ErdosOmissionTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_ScalarMassContinuity
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology
namespace ErdosOmissionTail
open ErdosContinuousBoundary

theorem scalarTailMass_continuous (n : ℕ) :
    Continuous (fun p : ℝ×ℝ => scalarTailMass n p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let Y : ℝ := |p.1|+(n:ℝ)+5
  have hY : 0 ≤ Y := by dsimp [Y] <;> positivity
  let F : (ℝ×ℝ) → ℝ → ℝ := fun q y => scalarTailIntegrand n q.1 q.2 y
  have hpmap : Continuous (fun q : (ℝ×ℝ)×ℝ => (2*q.2+2-q.1.1,q.1.2)) := by fun_prop
  have hh : Continuous (fun q : (ℝ×ℝ)×ℝ => scalarFreeIterate n terminalBlock (2*q.2+2-q.1.1) q.1.2) :=
    (scalarFreeIterate_continuous terminalBlock_continuous n).comp hpmap
  have hF : Continuous F.uncurry := (continuous_const.mul (continuous_snd.pow 2)).mul hh
  have hI : Continuous (fun q : ℝ×ℝ => ∫ y in Icc (0:ℝ) Y,F q y) :=
    continuous_parametric_integral_of_continuous hF isCompact_Icc
  apply hI.continuousAt.congr_of_eventuallyEq
  have hnear : ∀ᶠ q : ℝ×ℝ in 𝓝 p,q.1 < p.1+1 :=
    continuous_fst.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by linarith : p.1 < p.1+1))
  filter_upwards [hnear] with q hq
  have hp := le_abs_self p.1
  have hp0 := abs_nonneg p.1
  have hhigh : q.1/2+(n:ℝ)+4 ≤ Y := by dsimp [Y] <;> linarith
  rw [scalarTailMass_bounded n q.1 q.2 Y hY hhigh,
    intervalIntegral.integral_of_le hY,← integral_Icc_eq_integral_Ioc]

end ErdosOmissionTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_TerminalForceIntegral
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission ErdosContinuousBoundary ErdosOmissionBindings
open NumberTheoryLean.FinitePathGeometry

theorem terminalBlock_mask (S y : ℝ) {b : ℝ} (_hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    terminalBlock (2*y+2-S) b=
      ∫ a in Icc (1:ℝ) b,if S/2+a ≤ y then
        gate omissionForce .even (2*y+2-S-a) a/(max 1 a) else 0 := by
  have hset : Ioc (1:ℝ) (upperCutoff .odd (2*y+2-S) b)=
      Ioc (1:ℝ) b ∩ {a : ℝ | S/2+a ≤ y} := by
    ext a
    constructor
    · intro ha
      obtain ⟨ha1,ha2,hab,hgate⟩ := (mem_upperCutoff .odd (2*y+2-S) b a).mp ha
      have hh := (strong_gate_below_two ha2).mp hgate
      exact ⟨⟨ha1,hab⟩,by change S/2+a ≤ y; linarith⟩
    · rintro ⟨⟨ha1,hab⟩,hy⟩
      apply (mem_upperCutoff .odd (2*y+2-S) b a).mpr
      refine ⟨ha1,hab.trans hb2,hab,?_⟩
      apply (strong_gate_below_two (hab.trans hb2)).mpr
      change S/2+a ≤ y at hy
      linarith
  have hm : MeasurableSet {a : ℝ | S/2+a ≤ y} :=
    measurableSet_le (measurable_const.add measurable_id) measurable_const
  change (∫ a : ℝ in 1..upperCutoff .odd (2*y+2-S) b,
    gate omissionForce .even (2*y+2-S-a) a/(max 1 a))=_
  rw [intervalIntegral.integral_of_le (upperCutoff_bounds .odd (2*y+2-S) b).1,
    hset,← setIntegral_indicator hm,← integral_Icc_eq_integral_Ioc]
  rfl

theorem terminalOuterIntegrand_measurable (S : ℝ) : Measurable (terminalOuterIntegrand S) := by
  have hc0 : Continuous (fun p : ℝ×ℝ => gate omissionForce .even p.1 p.2) :=
    gate_continuous omissionForce_continuous .even
  have hp : Continuous (fun p : ℝ×ℝ => (2*p.1+2-S-p.2,p.2)) := by fun_prop
  have hc : Continuous (fun p : ℝ×ℝ => gate omissionForce .even (2*p.1+2-S-p.2) p.2) := hc0.comp hp
  exact Measurable.ite (measurableSet_le (measurable_const.add measurable_snd) measurable_fst)
    (((measurable_const.mul (measurable_fst.pow_const 2)).mul hc.measurable).div
      (measurable_const.max measurable_snd)) measurable_const

theorem terminalOuterIntegrand_bound (S a : ℝ) {y Y : ℝ} (hy0 : 0 ≤ y) (hyY : y ≤ Y) :
    |terminalOuterIntegrand S (y,a)| ≤ 2*Y^2 := by
  unfold terminalOuterIntegrand
  split_ifs
  · have hp := gate_nonnegative omissionForce_nonnegative .even (2*y+2-S-a) a
    have hu := gateIterate_force_le_one 1 .even (2*y+2-S-a) a
    change gate omissionForce .even (2*y+2-S-a) a ≤ 1 at hu
    have hn : 0 ≤ 2*y^2*gate omissionForce .even (2*y+2-S-a) a := by positivity
    have hm := mul_le_mul_of_nonneg_left hu (mul_nonneg (by norm_num : (0:ℝ)≤2) (sq_nonneg y))
    rw [abs_of_nonneg (div_nonneg hn (zero_le_one.trans (le_max_left _ _)))]
    apply (div_le_self hn (le_max_left (1:ℝ) a)).trans
    nlinarith
  · simpa only [abs_zero] using mul_nonneg (by norm_num : (0:ℝ)≤2) (sq_nonneg Y)

theorem scalarTailMass_zero_outer {S b : ℝ} (hS : 0 ≤ S) (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    scalarTailMass 0 S b=
      ∫ a : ℝ in 1..b,(2/a)*(∫ y : ℝ in S/2+a..S/2+4,
        y^2*gate omissionForce .even (2*y+2-S-a) a) := by
  let Y : ℝ := S/2+4
  have hY : 0 ≤ Y := by dsimp [Y] <;> linarith
  have hl (y : ℝ) : scalarTailIntegrand 0 S b y=∫ a in Icc (1:ℝ) b,terminalOuterIntegrand S (y,a) := by
    change 2*y^2*terminalBlock (2*y+2-S) b=_
    rw [terminalBlock_mask S y hb1 hb2,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with a
    dsimp only [terminalOuterIntegrand]
    split_ifs <;> ring
  have hs := bounded_rectangle_swap (terminalOuterIntegrand_measurable S) 0 Y 1 b (2*Y^2)
    (fun y hy a _ha => terminalOuterIntegrand_bound S a hy.1 hy.2)
  have hr (a : ℝ) (ha : a ∈ Icc (1:ℝ) b) :
      (∫ y in Icc (0:ℝ) Y,terminalOuterIntegrand S (y,a))=
        (2/a)*(∫ y : ℝ in S/2+a..Y,y^2*gate omissionForce .even (2*y+2-S-a) a) := by
    have ha2 : a ≤ 2 := ha.2.trans hb2
    have hlo : 0 ≤ S/2+a := by linarith [ha.1]
    have hhi : S/2+a ≤ Y := by dsimp [Y] <;> linarith
    have hset : Icc (0:ℝ) Y ∩ Ici (S/2+a)=Icc (S/2+a) Y := by
      ext y
      constructor
      · rintro ⟨hy,hylo⟩; exact ⟨hylo,hy.2⟩
      · intro hy; exact ⟨⟨hlo.trans hy.1,hy.2⟩,hy.1⟩
    have he : (fun y : ℝ => terminalOuterIntegrand S (y,a))=
        (Ici (S/2+a)).indicator (fun y => (2/a)*(y^2*gate omissionForce .even (2*y+2-S-a) a)) := by
      funext y
      unfold terminalOuterIntegrand
      by_cases h : S/2+a ≤ y
      · rw [ite_eq_left h,indicator_of_mem (show y ∈ Ici (S/2+a) from h),max_eq_right ha.1]
        ring
      · rw [ite_eq_right h,indicator_of_notMem (show y ∉ Ici (S/2+a) from h)]
    rw [he,setIntegral_indicator measurableSet_Ici,hset,integral_const_mul,
      integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hhi]
  rw [scalarTailMass_bounded 0 S b Y hY (by dsimp [Y] <;> norm_num),
    intervalIntegral.integral_of_le hY,← integral_Icc_eq_integral_Ioc]
  simp_rw [hl]
  rw [hs,intervalIntegral.integral_of_le hb1,← integral_Icc_eq_integral_Ioc]
  exact setIntegral_congr_fun measurableSet_Icc hr

end ErdosOmissionTail

end

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission ErdosContinuousBoundary ErdosOmissionBindings
open NumberTheoryLean.FinitePathGeometry

theorem evenGate_weighted_swap (S a l Y : ℝ) (ha1 : 1 ≤ a) (ha2 : a ≤ 2)
    (hl : 0 ≤ l) (hlY : l ≤ Y) :
    (∫ y : ℝ in l..Y,y^2*gate omissionForce .even (2*y+2-S-a) a)=
      ∫ u : ℝ in 1..a,(∫ y : ℝ in l..Y,y^2*omissionForce .odd (2*y+2-S-a-u) u)/u := by
  let G : ℝ×ℝ → ℝ := fun p => p.1^2*omissionForce .odd (2*p.1+2-S-a-p.2) p.2/(max 1 p.2)
  have hpmap : Continuous (fun p : ℝ×ℝ => (2*p.1+2-S-a-p.2,p.2)) := by fun_prop
  have hc : Continuous (fun p : ℝ×ℝ => omissionForce .odd (2*p.1+2-S-a-p.2) p.2) :=
    (omissionForce_continuous .odd).comp hpmap
  have hG : Continuous G := by
    apply ((continuous_fst.pow 2).mul hc).div (continuous_const.max continuous_snd)
    intro p
    exact ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le (le_max_left _ _))
  have hbnd : ∀ y ∈ Icc l Y,∀ u ∈ Icc (1:ℝ) a,|G (y,u)| ≤ Y^2 := by
    intro y hy u _hu
    have hy0 : 0 ≤ y := hl.trans hy.1
    have hp := omissionForce_nonnegative .odd (2*y+2-S-a-u) u
    have hu := omissionForce_le_one .odd (2*y+2-S-a-u) u
    have hn : 0 ≤ y^2*omissionForce .odd (2*y+2-S-a-u) u := by positivity
    have hh := mul_le_mul_of_nonneg_left hu (sq_nonneg y)
    dsimp only [G]
    rw [abs_of_nonneg (div_nonneg hn (zero_le_one.trans (le_max_left _ _)))]
    apply (div_le_self hn (le_max_left (1:ℝ) u)).trans
    nlinarith [hy.2]
  have hs := bounded_rectangle_swap hG.measurable l Y 1 a (Y^2) hbnd
  have hs' : (∫ y : ℝ in l..Y,∫ u : ℝ in 1..a,G (y,u))=
      ∫ u : ℝ in 1..a,∫ y : ℝ in l..Y,G (y,u) := by
    simpa only [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hlY,
      ← intervalIntegral.integral_of_le ha1] using hs
  have hl' : (∫ y : ℝ in l..Y,y^2*gate omissionForce .even (2*y+2-S-a) a)=
      ∫ y : ℝ in l..Y,∫ u : ℝ in 1..a,G (y,u) := by
    apply intervalIntegral.integral_congr
    intro y _hy
    dsimp only
    rw [gate,show upperCutoff .even (2*y+2-S-a) a=a from baseCutoff_on ha1 ha2,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _hu
    dsimp only [G,Side.flip]
    ring
  rw [hl',hs']
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ha1] at hu
  dsimp only
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro y _hy
  dsimp only [G]
  rw [max_eq_right hu.1]

theorem scalarTailMass_zero_triple {S b : ℝ} (hS : 0 ≤ S) (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    scalarTailMass 0 S b=
      ∫ a : ℝ in 1..b,∫ u : ℝ in 1..a,∫ c : ℝ in 1..u,
        lastWindowCoefficient S a u c/(a*u*c) := by
  rw [scalarTailMass_zero_outer hS hb1 hb2]
  apply intervalIntegral.integral_congr
  intro a ha
  rw [uIcc_of_le hb1] at ha
  have ha2 : a ≤ 2 := ha.2.trans hb2
  have hl : 0 ≤ S/2+a := by linarith [ha.1]
  have hlY : S/2+a ≤ S/2+4 := by linarith
  dsimp only
  rw [evenGate_weighted_swap S a (S/2+a) (S/2+4) ha.1 ha2 hl hlY,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ha.1] at hu
  have hu2 : u ≤ 2 := hu.2.trans ha2
  have hw := integrated_force_window (S+a+u) (S/2+a) (S/2+4) u 0 hl hu.1 hu2
    (by linarith [hu.1]) (by linarith)
  simp only [sub_zero,zero_mul] at hw
  have hgap (y : ℝ) : 2*y+2-S-a-u=2*y+2-(S+a+u) := by ring
  dsimp only
  simp_rw [hgap]
  rw [hw,← intervalIntegral.integral_div,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro c hc
  rw [uIcc_of_le hu.1] at hc
  have ha0 : a ≠ 0 := by linarith [ha.1]
  have hu0 : u ≠ 0 := by linarith [hu.1]
  have hc0 : c ≠ 0 := by linarith [hc.1]
  dsimp only [lastWindowCoefficient]
  field_simp
  ring

end ErdosOmissionTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_OnePairCost
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory
namespace Erdos970Dependency.InvariantCostBound
open NumberTheoryLean NumberTheoryLean.BuchstabBridge NumberTheoryLean.DerivativeWeights
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.FinitePathMeasures
open NumberTheoryLean.NormalizedDeficits NumberTheoryLean.DeficitFutureIntegrals
open Erdos970Dependency.InvariantDensities Erdos970Dependency.DeficitIntegralValues

theorem cost_le_inv {s : ℝ} (hs : 0 < s) : cost s ≤ 1 / s := by
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / s by positivity)
  change Real.log (1 + 1 / s) ≤ 1 / s
  linarith

theorem evenCost_nonneg (s : ℝ) : 0 ≤ evenCost s := by
  by_cases hs : 2 ≤ s
  · rw [evenCost, evenDensity, indicator_of_mem (show s ∈ Ici (2 : ℝ) from hs)]
    exact mul_nonneg (phiEven_pos (by linarith)).le (cost_pos (by linarith)).le
  · rw [evenCost, evenDensity, indicator_of_notMem (show s ∉ Ici (2 : ℝ) from hs), zero_mul]

theorem oddCost_nonneg (s : ℝ) : 0 ≤ oddCost s := by
  by_cases hs : 1 ≤ s
  · rw [oddCost]
    exact mul_nonneg (oddDensity_nonneg s) (cost_pos (by linarith)).le
  · rw [oddCost, oddDensity, indicator_of_notMem (show s ∉ Ici (1 : ℝ) from hs), zero_mul]

theorem evenCost_le_major (s : ℝ) : evenCost s ≤ evenMajor s := by
  by_cases hs : 2 ≤ s
  · rw [evenCost, evenDensity, evenMajor,
      indicator_of_mem (show s ∈ Ici (2 : ℝ) from hs), indicator_of_mem (show s ∈ Ici (2 : ℝ) from hs)]
    calc
      phiEven s * cost s ≤ phiEven s * (1 / s) :=
        mul_le_mul_of_nonneg_left (cost_le_inv (by linarith)) (phiEven_pos (by linarith)).le
      _ = _ := by rw [phiEven_eq_deficits hs]; field_simp
  · rw [evenCost, evenDensity, evenMajor,
      indicator_of_notMem (show s ∉ Ici (2 : ℝ) from hs),
      indicator_of_notMem (show s ∉ Ici (2 : ℝ) from hs), zero_mul]

theorem oddCost_le_major (s : ℝ) : oddCost s ≤ oddMajor s := by
  by_cases hs : 1 ≤ s
  · rw [oddCost, oddDensity, oddMajor,
      indicator_of_mem (show s ∈ Ici (1 : ℝ) from hs), indicator_of_mem (show s ∈ Ici (1 : ℝ) from hs)]
    have hphi : oddFactor s * phiOdd s ≤ phiOdd s := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (oddFactor_bounds hs).2 (phiOdd_pos s).le
    calc
      (oddFactor s * phiOdd s) * cost s ≤ phiOdd s * cost s :=
        mul_le_mul_of_nonneg_right hphi (cost_pos (by linarith)).le
      _ ≤ phiOdd s * (1 / s) :=
        mul_le_mul_of_nonneg_left (cost_le_inv (by linarith)) (phiOdd_pos s).le
      _ = _ := by rw [phiOdd_eq_deficits hs]; field_simp
  · rw [oddCost, oddDensity, oddMajor,
      indicator_of_notMem (show s ∉ Ici (1 : ℝ) from hs),
      indicator_of_notMem (show s ∉ Ici (1 : ℝ) from hs), zero_mul]

theorem evenMajor_integrable : Integrable evenMajor :=
  (integrable_indicator_iff measurableSet_Ici).mpr even_majorant_integral.1

theorem oddMajor_integrable : Integrable oddMajor :=
  (integrable_indicator_iff measurableSet_Ici).mpr odd_majorant_integral.1

theorem evenCost_integrable : Integrable evenCost := by
  apply evenMajor_integrable.mono' (evenDensity_measurable.mul cost_measurable).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun s ↦ by
    change ‖evenCost s‖ ≤ evenMajor s
    rw [Real.norm_of_nonneg (evenCost_nonneg s)]
    exact evenCost_le_major s)

theorem oddCost_integrable : Integrable oddCost := by
  apply oddMajor_integrable.mono' (oddDensity_measurable.mul cost_measurable).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun s ↦ by
    change ‖oddCost s‖ ≤ oddMajor s
    rw [Real.norm_of_nonneg (oddCost_nonneg s)]
    exact oddCost_le_major s)

theorem even_cost_bound : (∫ s, evenCost s) ≤ sieveA - 1 := by
  have h := integral_mono evenCost_integrable evenMajor_integrable evenCost_le_major
  rw [evenMajor, integral_indicator measurableSet_Ici, even_majorant_integral.2] at h
  exact h

theorem odd_cost_bound : (∫ s, oddCost s) ≤ sieveA + 1 := by
  have h := integral_mono oddCost_integrable oddMajor_integrable oddCost_le_major
  rw [oddMajor, integral_indicator measurableSet_Ici, odd_majorant_integral.2] at h
  exact h

theorem even_cost_pos : 0 < ∫ s, evenCost s := by
  apply (integral_pos_iff_support_of_nonneg evenCost_nonneg evenCost_integrable).mpr
  have hsub : Icc (2 : ℝ) 3 ⊆ Function.support evenCost := by
    intro s hs
    apply ne_of_gt
    rw [evenCost, evenDensity, indicator_of_mem (show s ∈ Ici (2 : ℝ) from hs.1)]
    exact mul_pos (phiEven_pos (by linarith [hs.1])) (cost_pos (by linarith [hs.1]))
  exact lt_of_lt_of_le (by norm_num [Real.volume_Icc] : 0 < volume (Icc (2 : ℝ) 3)) (measure_mono hsub)

theorem costMass_pos : 0 < costMass :=
  add_pos_of_pos_of_nonneg even_cost_pos (integral_nonneg oddCost_nonneg)

theorem costMass_le : costMass ≤ 2 * sieveA := by
  unfold costMass
  linarith [even_cost_bound, odd_cost_bound]

end Erdos970Dependency.InvariantCostBound

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_OrderedWindowKernel
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission ErdosContinuousBoundary

theorem windowKernel_continuous (S : ℝ) :
    Continuous (fun q : (ℝ×ℝ)×ℝ => windowKernel S q.1.1 q.1.2 q.2) := by
  have hn : Continuous (fun q : (ℝ×ℝ)×ℝ => (S+q.1.1+q.1.2+2*q.2)^3-(S+2*q.1.1)^3) := by fun_prop
  have hd : Continuous (fun q : (ℝ×ℝ)×ℝ => 12*(max 1 q.1.1)*(max 1 q.1.2)*(max 1 q.2)^2) := by fun_prop
  apply hn.div hd
  intro q
  have h1 : 0 < max (1:ℝ) q.1.1 := (by norm_num : (0:ℝ)<1).trans_le (le_max_left _ _)
  have h2 : 0 < max (1:ℝ) q.1.2 := (by norm_num : (0:ℝ)<1).trans_le (le_max_left _ _)
  have h3 : 0 < max (1:ℝ) q.2 := (by norm_num : (0:ℝ)<1).trans_le (le_max_left _ _)
  positivity

theorem windowMiddle_continuous (S : ℝ) : Continuous (fun p : ℝ×ℝ => windowMiddle S p.1 p.2) := by
  exact continuous_variable_upper_integral (fun p c => windowKernel S p.1 p.2 c)
    (windowKernel_continuous S) (fun p => baseCutoff p.2)
    (continuous_const.max (continuous_const.min continuous_snd))

theorem windowOuter_continuous (S : ℝ) : Continuous (windowOuter S) := by
  have hp : Continuous (fun q : (ℝ×ℝ)×ℝ => (q.1.1,q.2)) := by fun_prop
  have hF : Continuous (fun q : (ℝ×ℝ)×ℝ => windowMiddle S q.1.1 q.2) :=
    (windowMiddle_continuous S).comp hp
  have hcap : Continuous (fun p : ℝ×ℝ => baseCutoff p.1) :=
    continuous_const.max (continuous_const.min continuous_fst)
  have hh : Continuous (fun p : ℝ×ℝ => ∫ u : ℝ in 1..baseCutoff p.1,windowMiddle S p.1 u) :=
    continuous_variable_upper_integral (fun p u => windowMiddle S p.1 u) hF (fun p => baseCutoff p.1) hcap
  have hmap : Continuous (fun a : ℝ => (a,(0:ℝ))) := by fun_prop
  change Continuous (fun a : ℝ => ∫ u : ℝ in 1..baseCutoff a,windowMiddle S a u)
  simpa only [Function.comp_def] using! hh.comp hmap

theorem windowKernel_literal {S a u c : ℝ} (ha : 1 ≤ a) (hu : 1 ≤ u) (hc : 1 ≤ c) :
    windowKernel S a u c=lastWindowCoefficient S a u c/(a*u*c) := by
  rw [windowKernel,max_eq_right ha,max_eq_right hu,max_eq_right hc,lastWindowCoefficient]
  ring

theorem scalarTailMass_zero_eq_windowMass {S b : ℝ} (hS : 0 ≤ S) (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    scalarTailMass 0 S b=windowMass S b := by
  rw [scalarTailMass_zero_triple hS hb1 hb2,windowMass,baseCutoff_on hb1 hb2]
  apply intervalIntegral.integral_congr
  intro a ha
  rw [uIcc_of_le hb1] at ha
  dsimp only
  rw [windowOuter,baseCutoff_on ha.1 (ha.2.trans hb2)]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ha.1] at hu
  dsimp only
  rw [windowMiddle,baseCutoff_on hu.1 (hu.2.trans (ha.2.trans hb2))]
  apply intervalIntegral.integral_congr
  intro c hc
  rw [uIcc_of_le hu.1] at hc
  exact (windowKernel_literal ha.1 hu.1 hc.1).symm

end ErdosOmissionTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_OrderedAffineMoment
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission

theorem orderedFirstMoment_continuous (n : ℕ) : Continuous (orderedFirstMoment n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hc : Continuous (fun x : ℝ => (x*orderedMass n x+orderedFirstMoment n x)/(max 1 x)) :=
      ((continuous_id.mul (orderedMass_continuous n)).add ih).div
        (continuous_const.max continuous_id) (fun x => ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le (le_max_left _ _)))
    exact (intervalIntegral.differentiable_integral_of_continuous hc).continuous.comp
      (continuous_const.max (continuous_const.min continuous_id))

theorem first_moment_primitive (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => (x-1)*((Real.log x)^(n+1)/((n+1).factorial:ℝ)))
      ((Real.log x)^(n+1)/((n+1).factorial:ℝ)+(x-1)*((Real.log x)^n/(n.factorial:ℝ))/x) x := by
  have hh := ((hasDerivAt_id x).sub_const 1).mul (log_power_primitive n hx)
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [id_eq,one_mul]
  ring

theorem orderedFirstMoment_eq (n : ℕ) {b : ℝ} (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    orderedFirstMoment (n+1) b=(b-1)*((Real.log b)^n/(n.factorial:ℝ)) := by
  induction n generalizing b with
  | zero =>
    rw [orderedFirstMoment,baseCutoff_on hb1 hb2]
    have he : (∫ x in (1:ℝ)..b,(x*orderedMass 0 x+orderedFirstMoment 0 x)/(max 1 x))=
        ∫ _x in (1:ℝ)..b,(1:ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hb1] at hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      simp [orderedMass,orderedFirstMoment,max_eq_right hx.1,hx0]
    rw [he]
    simp
  | succ n ih =>
    rw [orderedFirstMoment,baseCutoff_on hb1 hb2]
    have he : (∫ x in (1:ℝ)..b,(x*orderedMass (n+1) x+orderedFirstMoment (n+1) x)/(max 1 x))=
        ∫ x in (1:ℝ)..b,((Real.log x)^(n+1)/((n+1).factorial:ℝ)+(x-1)*((Real.log x)^n/(n.factorial:ℝ))/x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hb1] at hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      dsimp only
      rw [orderedMass_eq (n+1) hx.1 (hx.2.trans hb2),ih hx.1 (hx.2.trans hb2),max_eq_right hx.1]
      field_simp
    rw [he]
    have hn : (n.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hn1 : ((n+1).factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n+1)
    have hc : ContinuousOn (fun x : ℝ => (Real.log x)^(n+1)/((n+1).factorial:ℝ)+(x-1)*((Real.log x)^n/(n.factorial:ℝ))/x)
        (uIcc 1 b) := by
      rw [uIcc_of_le hb1]
      intro x hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := simp_all)
    have hd : ∀ x ∈ uIcc (1:ℝ) b, HasDerivAt
        (fun x : ℝ => (x-1)*((Real.log x)^(n+1)/((n+1).factorial:ℝ)))
        ((Real.log x)^(n+1)/((n+1).factorial:ℝ)+(x-1)*((Real.log x)^n/(n.factorial:ℝ))/x) x := by
      intro x hx
      rw [uIcc_of_le hb1] at hx
      exact first_moment_primitive n (by linarith [hx.1])
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable (μ := volume))]
    simp

end ErdosOmissionTail

end

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission

theorem orderedAffine_continuous (m : ℝ) (n : ℕ) :
    Continuous (fun p : ℝ×ℝ => orderedAffine m n p.1 p.2) := by
  have hM : Continuous (fun p : ℝ×ℝ => orderedMass n p.2) := (orderedMass_continuous n).comp continuous_snd
  have hF : Continuous (fun p : ℝ×ℝ => orderedFirstMoment n p.2) := (orderedFirstMoment_continuous n).comp continuous_snd
  exact (((continuous_const.mul continuous_fst).div_const m).sub continuous_const |>.mul hM).add
    (continuous_const.mul hF)

theorem orderedAffine_shift_continuous (m : ℝ) (n : ℕ) (S : ℝ) :
    Continuous (fun x : ℝ => orderedAffine m n (S+x) x) := by
  have hp : Continuous (fun x : ℝ => (S+x,x)) := by fun_prop
  exact (orderedAffine_continuous m n).comp hp

theorem orderedAffine_shift_div_continuous (m : ℝ) (n : ℕ) (S : ℝ) :
    Continuous (fun x : ℝ => orderedAffine m n (S+x) x/(max 1 x)) :=
  (orderedAffine_shift_continuous m n S).div (continuous_const.max continuous_id)
    (fun x => ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le (le_max_left _ _)))

theorem orderedAffine_zero (m S b : ℝ) : orderedAffine m 0 S b=3*S/m-2 := by
  simp [orderedAffine,orderedMass,orderedFirstMoment]

theorem orderedAffine_succ (m : ℝ) (n : ℕ) (S b : ℝ) :
    orderedAffine m (n+1) S b=
      ∫ x : ℝ in 1..baseCutoff b,orderedAffine m n (S+x) x/(max 1 x) := by
  have hd : ∀ x : ℝ,max 1 x ≠ 0 := fun x => ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le (le_max_left _ _))
  have hM : Continuous (fun x : ℝ => orderedMass n x/(max 1 x)) :=
    (orderedMass_continuous n).div (continuous_const.max continuous_id) hd
  have hF : Continuous (fun x : ℝ => (x*orderedMass n x+orderedFirstMoment n x)/(max 1 x)) :=
    ((continuous_id.mul (orderedMass_continuous n)).add (orderedFirstMoment_continuous n)).div
      (continuous_const.max continuous_id) hd
  change (3*S/m-2)*(∫ x : ℝ in 1..baseCutoff b,orderedMass n x/(max 1 x))+
    (3/m)*(∫ x : ℝ in 1..baseCutoff b,(x*orderedMass n x+orderedFirstMoment n x)/(max 1 x))=_
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add
      ((hM.const_mul (3*S/m-2)).intervalIntegrable (μ := volume) 1 _)
      ((hF.const_mul (3/m)).intervalIntegrable (μ := volume) 1 _)]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only [orderedAffine]
  ring

theorem orderedAffine_at_two (n : ℕ) :
    orderedAffine ((n+1:ℕ):ℝ) (n+1) 0 2=
      (3/Real.log 2-2)*(Real.log 2)^(n+1)/((n+1).factorial:ℝ) := by
  rw [orderedAffine,orderedMass_eq (n+1) (by norm_num) le_rfl,
    orderedFirstMoment_eq n (by norm_num) le_rfl]
  norm_num only [mul_zero,zero_div,zero_sub,sub_self,sub_zero,show (2:ℝ)-1=1 by norm_num,one_mul]
  rw [Nat.factorial_succ,pow_succ,Nat.cast_mul]
  have hn : ((n+1:ℕ):ℝ) ≠ 0 := by positivity
  have hf : (n.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1:ℝ)<2)).ne'
  field_simp
  ring

end ErdosOmissionTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ExponentialTailBound
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosOmissionTail

theorem expTerm_hasSum (x : ℝ) : HasSum (expTerm x) (Real.exp x) := by
  simpa only [Real.exp_eq_exp_ℝ] using! NormedSpace.expSeries_div_hasSum_exp x

theorem firstExpTerm_succ (x : ℝ) (n : ℕ) : firstExpTerm x (n+1)=x*expTerm x n := by
  unfold firstExpTerm expTerm
  rw [Nat.factorial_succ,pow_succ,Nat.cast_mul]
  have hn : ((n+1:ℕ):ℝ) ≠ 0 := by positivity
  field_simp

theorem secondExpTerm_add_two (x : ℝ) (n : ℕ) : secondExpTerm x (n+2)=x^2*expTerm x n := by
  unfold secondExpTerm expTerm
  rw [show n+2=(n+1)+1 by omega,Nat.factorial_succ,Nat.factorial_succ,pow_succ,pow_succ]
  push_cast
  have hn1 : (n:ℝ)+1 ≠ 0 := by positivity
  have hn2 : (n:ℝ)+1+1 ≠ 0 := by positivity
  field_simp
  ring

theorem firstExpTerm_hasSum (x : ℝ) : HasSum (firstExpTerm x) (x*Real.exp x) := by
  apply (hasSum_nat_add_iff' 1).mp
  have hh := (expTerm_hasSum x).mul_left x
  simp_rw [firstExpTerm_succ]
  simpa only [Finset.sum_range_one,firstExpTerm,Nat.cast_zero,zero_mul,sub_zero] using! hh

theorem secondExpTerm_hasSum (x : ℝ) : HasSum (secondExpTerm x) (x^2*Real.exp x) := by
  apply (hasSum_nat_add_iff' 2).mp
  have hh := (expTerm_hasSum x).mul_left (x^2)
  simp_rw [secondExpTerm_add_two]
  simpa only [Finset.sum_range_succ,Finset.sum_range_zero,Finset.sum_empty,
    secondExpTerm,Nat.cast_zero,Nat.cast_one,zero_mul,sub_self,mul_zero,add_zero,sub_zero] using! hh

theorem weightedExpTerm_hasSum (x : ℝ) :
    HasSum (weightedExpTerm x) ((x^2+3*x+1)*Real.exp x) := by
  have hh := ((secondExpTerm_hasSum x).add ((firstExpTerm_hasSum x).mul_left 3)).add (expTerm_hasSum x)
  convert! hh using 1
  · funext n
    unfold weightedExpTerm secondExpTerm firstExpTerm
    ring
  · ring

theorem weighted_log_two_tail_hasSum :
    HasSum (fun n : ℕ => weightedExpTerm (Real.log 2) (n+4))
      (1+2*Real.log 2-(5:ℝ)/2*(Real.log 2)^2-(8:ℝ)/3*(Real.log 2)^3) := by
  have hh := (hasSum_nat_add_iff' 4).mpr (weightedExpTerm_hasSum (Real.log 2))
  rw [Real.exp_log (by norm_num : (0:ℝ)<2)] at hh
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  norm_num [weightedExpTerm,expTerm,Finset.sum_range_succ]
  ring

theorem weighted_log_two_tail_lt :
    (∑' n : ℕ,weightedExpTerm (Real.log 2) (n+4)) < (314:ℝ)/1000 := by
  rw [weighted_log_two_tail_hasSum.tsum_eq]
  have h := ErdosBoundaryLoss.log_two_bounds
  have hq : 0 < (Real.log 2)^2+(69:ℝ)/100*Real.log 2+(69:ℝ)^2/10000 := by positivity
  have hp := mul_pos (sub_pos.mpr h.1)
    (show 0 < (5:ℝ)/2*(Real.log 2+(69:ℝ)/100)+(8:ℝ)/3*
      ((Real.log 2)^2+(69:ℝ)/100*Real.log 2+(69:ℝ)^2/10000)-2 by nlinarith)
  nlinarith

theorem log_two_mean_factor_bounds :
    0 < 3/Real.log 2-2 ∧ 3/Real.log 2-2 < (235:ℝ)/100 := by
  have h := ErdosBoundaryLoss.log_two_bounds
  have hp : 0 < Real.log 2 := by linarith
  constructor
  · have hh : 2*Real.log 2 < 3 := by linarith
    exact sub_pos.mpr ((lt_div_iff₀ hp).mpr hh)
  · have hh : 3/Real.log 2 < (435:ℝ)/100 := (div_lt_iff₀ hp).mpr (by linarith)
    linarith

theorem numerical_tail_majorant_lt :
    (1:ℝ)/2*(3/Real.log 2-2)*(∑' n : ℕ,weightedExpTerm (Real.log 2) (n+4)) < (37:ℝ)/100 := by
  have hf := log_two_mean_factor_bounds
  have ht := weighted_log_two_tail_lt
  have hnon : 0 ≤ ∑' n : ℕ,weightedExpTerm (Real.log 2) (n+4) := by
    apply tsum_nonneg
    intro n
    unfold weightedExpTerm expTerm
    positivity
  have hm := mul_lt_mul_of_pos_left ht (mul_pos (by norm_num : (0:ℝ)<1/2) hf.1)
  have hf' := mul_lt_mul_of_pos_right hf.2 (by norm_num : (0:ℝ)<(314:ℝ)/2000)
  nlinarith

end ErdosOmissionTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceRootReference
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission

theorem terminal_mass_affine_bound (k : ℕ) {S b : ℝ}
    (hSlo : (k:ℝ) ≤ S) (hShi : S ≤ 2*(k:ℝ)) (hSb : (k:ℝ)*b ≤ S)
    (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    scalarTailMass 0 S b ≤ (((k:ℝ)+4)^2/2)*orderedAffine ((k:ℝ)+3) 3 S b := by
  let m : ℝ := (k:ℝ)+3
  let C : ℝ := ((k:ℝ)+4)^2/2
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
  have hS : 0 ≤ S := hk.trans hSlo
  have hmiddle : ∀ a ∈ Icc (1:ℝ) b,∀ u ∈ Icc (1:ℝ) a,
      windowMiddle S a u ≤ C/(a*u)*orderedAffine m 1 (S+a+u) u := by
    intro a ha u hu
    have ha2 : a ≤ 2 := ha.2.trans hb2
    have hu2 : u ≤ 2 := hu.2.trans ha2
    have ha0 : 0 < a := by linarith [ha.1]
    have hu0 : 0 < u := by linarith [hu.1]
    have hpmap : Continuous (fun c : ℝ => ((a,u),c)) := by fun_prop
    have hlower : Continuous (windowKernel S a u) := by
      simpa only [Function.comp_def] using! (windowKernel_continuous S).comp hpmap
    have hupper := (orderedAffine_shift_div_continuous m 0 (S+a+u)).const_mul (C/(a*u))
    have hh := intervalIntegral.integral_mono_on hu.1
      (hlower.intervalIntegrable (μ := volume) 1 u) (hupper.intervalIntegrable (μ := volume) 1 u) (fun c hc => by
        have hc0 : 0 < c := by linarith [hc.1]
        have hcb : c ≤ b := hc.2.trans (hu.2.trans ha.2)
        have hSc : (k:ℝ)*c ≤ S := (mul_le_mul_of_nonneg_left hcb hk).trans hSb
        have hw := last_window_mean_bound k hSlo hShi hSc ha.1 ha2 hu.1 hu.2 hc.1 hc.2
        rw [windowKernel_literal ha.1 hu.1 hc.1]
        change lastWindowCoefficient S a u c/(a*u*c) ≤ C/(a*u)*(orderedAffine m 0 (S+a+u+c) c/(max 1 c))
        rw [orderedAffine_zero,max_eq_right hc.1]
        have hd := div_le_div_of_nonneg_right hw (show 0 ≤ a*u*c by positivity)
        convert! hd using 1; dsimp [C,m] <;> ring)
    unfold windowMiddle
    rw [baseCutoff_on hu.1 hu2]
    apply hh.trans_eq
    rw [intervalIntegral.integral_const_mul,orderedAffine_succ m 0 (S+a+u) u,baseCutoff_on hu.1 hu2]
  have houter : ∀ a ∈ Icc (1:ℝ) b,windowOuter S a ≤ C/a*orderedAffine m 2 (S+a) a := by
    intro a ha
    have ha2 : a ≤ 2 := ha.2.trans hb2
    have hpmap : Continuous (fun u : ℝ => (a,u)) := by fun_prop
    have hlower : Continuous (windowMiddle S a) := by
      simpa only [Function.comp_def] using! (windowMiddle_continuous S).comp hpmap
    have hupper := (orderedAffine_shift_div_continuous m 1 (S+a)).const_mul (C/a)
    have hh := intervalIntegral.integral_mono_on ha.1
      (hlower.intervalIntegrable (μ := volume) 1 a) (hupper.intervalIntegrable (μ := volume) 1 a) (fun u hu => by
        have hw := hmiddle a ha u hu
        change windowMiddle S a u ≤ C/a*(orderedAffine m 1 (S+a+u) u/(max 1 u))
        rw [max_eq_right hu.1]
        convert! hw using 1; ring)
    unfold windowOuter
    rw [baseCutoff_on ha.1 ha2]
    apply hh.trans_eq
    rw [intervalIntegral.integral_const_mul,orderedAffine_succ m 1 (S+a) a,baseCutoff_on ha.1 ha2]
  rw [scalarTailMass_zero_eq_windowMass hS hb1 hb2,windowMass,baseCutoff_on hb1 hb2]
  have hupper := (orderedAffine_shift_div_continuous m 2 S).const_mul C
  have hh := intervalIntegral.integral_mono_on hb1
    ((windowOuter_continuous S).intervalIntegrable (μ := volume) 1 b)
    (hupper.intervalIntegrable (μ := volume) 1 b) (fun a ha => by
      have hw := houter a ha
      change windowOuter S a ≤ C*(orderedAffine m 2 (S+a) a/(max 1 a))
      rw [max_eq_right ha.1]
      convert! hw using 1; ring)
  apply hh.trans_eq
  rw [intervalIntegral.integral_const_mul,orderedAffine_succ m 2 S b,baseCutoff_on hb1 hb2]

end ErdosOmissionTail

end

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission

theorem scalarTailMass_affine_bound (n k : ℕ) {S b : ℝ}
    (hSlo : (k:ℝ) ≤ S) (hShi : S ≤ 2*(k:ℝ)) (hSb : (k:ℝ)*b ≤ S)
    (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    scalarTailMass n S b ≤ (((k:ℝ)+(n:ℝ)+4)^2/2)*
      orderedAffine ((k:ℝ)+(n:ℝ)+3) (n+3) S b := by
  induction n generalizing k S b with
  | zero =>
    simpa only [Nat.cast_zero,add_zero,Nat.zero_add] using terminal_mass_affine_bound k hSlo hShi hSb hb1 hb2
  | succ n ih =>
    have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
    have hS : 0 ≤ S := hk.trans hSlo
    simp only [Nat.cast_add,Nat.cast_one]
    rw [show (k:ℝ)+((n:ℝ)+1)+4=(k:ℝ)+(n:ℝ)+5 by ring,
      show (k:ℝ)+((n:ℝ)+1)+3=(k:ℝ)+(n:ℝ)+4 by ring,
      show (n+1)+3=(n+3)+1 by omega]
    let m : ℝ := (k:ℝ)+(n:ℝ)+4
    let C : ℝ := ((k:ℝ)+(n:ℝ)+5)^2/2
    change scalarTailMass (n+1) S b ≤ C*orderedAffine m ((n+3)+1) S b
    rw [scalarTailMass_succ n hS hb1 hb2,orderedAffine_succ,baseCutoff_on hb1 hb2,
      ← intervalIntegral.integral_const_mul]
    have hpmap : Continuous (fun x : ℝ => (S+x,x)) := by fun_prop
    have hc : Continuous (fun x : ℝ => scalarTailMass n (S+x) x/(max 1 x)) :=
      ((scalarTailMass_continuous n).comp hpmap).div (continuous_const.max continuous_id)
        (fun x => ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le (le_max_left _ _)))
    have hlow : IntervalIntegrable (fun x : ℝ => scalarTailMass n (S+x) x/x) volume 1 b := by
      apply (hc.intervalIntegrable (μ := volume) 1 b).congr_uIoo
      intro x hx
      rw [uIoo_of_le hb1] at hx
      simp only [max_eq_right hx.1.le]
    have hupper := (orderedAffine_shift_div_continuous m (n+3) S).const_mul C
    apply intervalIntegral.integral_mono_on hb1 hlow (hupper.intervalIntegrable (μ := volume) 1 b)
    intro x hx
    have hx2 : x ≤ 2 := hx.2.trans hb2
    have hlo : ((k+1:ℕ):ℝ) ≤ S+x := by push_cast <;> linarith [hx.1]
    have hhi : S+x ≤ 2*((k+1:ℕ):ℝ) := by push_cast <;> linarith
    have horder : ((k+1:ℕ):ℝ)*x ≤ S+x := by
      have hh := mul_le_mul_of_nonneg_left hx.2 hk
      push_cast
      nlinarith
    have hh := ih (k+1) hlo hhi horder hx.1 hx2
    have hm : ((k+1:ℕ):ℝ)+(n:ℝ)+3=m := by dsimp [m]; push_cast <;> ring
    have hC : (((k+1:ℕ):ℝ)+(n:ℝ)+4)^2/2=C := by dsimp [C]; push_cast <;> ring
    rw [hm,hC] at hh
    rw [max_eq_right hx.1]
    have hd := div_le_div_of_nonneg_right hh (show 0 ≤ x by linarith [hx.1])
    convert! hd using 1; ring

end ErdosOmissionTail

end

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionTail
open ErdosContinuousOmission

theorem actual_omission_factorial_bound (n : ℕ) :
    omissionLossTerm (n+3) ≤
      (1:ℝ)/2*(3/Real.log 2-2)*weightedExpTerm (Real.log 2) (n+4) := by
  have hh := scalarTailMass_affine_bound (n+1) 0 (S := 0) (b := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl
  norm_num only [Nat.cast_zero,zero_add] at hh
  have hm : ((n+1:ℕ):ℝ)+3=((n+4:ℕ):ℝ) := by push_cast <;> ring
  rw [hm,show (n+1)+3=n+4 by omega,show n+4=(n+3)+1 by omega,orderedAffine_at_two] at hh
  have hc := (actual_loss_le_scalarTailMass (n+1)).trans hh
  have he : (n+1)+2=n+3 := by omega
  rw [he] at hc
  convert! hc using 1
  all_goals try with_reducible_and_instances rfl
  unfold weightedExpTerm expTerm
  push_cast
  ring

theorem actual_omission_tail_lt : (∑' n : ℕ,omissionLossTerm (n+3)) < (37:ℝ)/100 := by
  have hl : Summable (fun n : ℕ => omissionLossTerm (n+3)) :=
    actual_loss_summable_jb247.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hu := weighted_log_two_tail_hasSum.summable.mul_left ((1:ℝ)/2*(3/Real.log 2-2))
  have hh := hl.tsum_le_tsum actual_omission_factorial_bound hu
  rw [tsum_mul_left] at hh
  exact hh.trans_lt numerical_tail_majorant_lt

end ErdosOmissionTail

end

section

open _root_.Set _root_.Filter
open scoped Topology
namespace ErdosPositiveReference
open ErdosOmissionBindings ErdosOmissionTail ErdosContinuousOmission
open ErdosBoundaryIntegral ErdosBoundaryLoss
open Erdos970Dependency.InvariantCostBound
open NumberTheoryLean.BuchstabBridge

theorem actual_I_gt_eleven_seventyfive : (11:ℝ)/75 < signedCoefficientI := by
  have hfirst := actual_first_three_partial_sum_lt_jb247
  have htail := actual_omission_tail_lt
  have hsplit := actual_loss_summable_jb247.sum_add_tsum_nat_add 3
  have htotal := actual_signed_loss_series_jb247
  linarith

theorem exp_gamma_lt_two : Real.exp Real.eulerMascheroniConstant < 2 := by
  have hg : Real.eulerMascheroniConstant < Real.log 2 := by
    linarith [Real.eulerMascheroniConstant_lt_two_thirds,log_two_bounds.1]
  have h := Real.exp_lt_exp.mpr hg
  simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using h

theorem costMass_lt_eight : costMass < 8 := by
  have h := costMass_le
  change costMass ≤ 2*(2*Real.exp Real.eulerMascheroniConstant) at h
  linarith [exp_gamma_lt_two]

theorem source_reference_coefficient_margin :
    (2:ℝ)/100 < -(1:ℝ)/100+2*signedCoefficientI/costMass := by
  have h : (3:ℝ)/100 < 2*signedCoefficientI/costMass := by
    apply (lt_div_iff₀ costMass_pos).mpr
    nlinarith [actual_I_gt_eleven_seventyfive,costMass_lt_eight]
  linarith

end ErdosPositiveReference

end

section

open _root_.Set _root_.Filter
open scoped Topology
namespace ErdosSourceReferenceMargin
open ErdosCorrectionLimit ErdosBoundaryIntegral ErdosPositiveReference
open Erdos970Dependency.InvariantCostBound

theorem actual_reference_limit_positive_jb247_oai :
    Real.exp Real.eulerMascheroniConstant/100 <
      Real.exp Real.eulerMascheroniConstant*(-(1:ℝ)/100+2*signedCoefficientI/costMass) := by
  have hh := mul_lt_mul_of_pos_left source_reference_coefficient_margin (Real.exp_pos Real.eulerMascheroniConstant)
  nlinarith [Real.exp_pos Real.eulerMascheroniConstant]

end ErdosSourceReferenceMargin

end


end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.ErdosSourceReferenceMargin.actual_reference_limit_positive_jb247_oai := @OAI.Erdos970.ErdosSourceReferenceMargin.actual_reference_limit_positive_jb247_oai
