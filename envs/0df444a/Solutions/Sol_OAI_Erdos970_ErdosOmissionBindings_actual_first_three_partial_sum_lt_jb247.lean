-- Prove2me | solution 1 for OAI.Erdos970.ErdosOmissionBindings.actual_first_three_partial_sum_lt_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:56:24.600702+00:00
-- url     : https://prove2.me/submissions/e1225d42-22f1-4b02-8373-9ab398f43283

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
import Theorems.Thm_OAI_Erdos970_ErdosContinuousOmission_actual_first_loss_eq_one_jb247
import Theorems.Thm_OAI_Erdos970_ErdosOmissionBindings_second_loss_bounded_jb247
import Theorems.Thm_OAI_Erdos970_ErdosOmissionBindings_third_loss_bounded_jb247

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
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory
namespace ErdosBoundaryLoss

theorem inner2Primitive_deriv (t x : ℝ) (ht : 0 < t) (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => inner2Primitive t x) (loss2Kernel t x) x := by
  unfold inner2Primitive loss2Kernel
  have h0 := (hasDerivAt_id x)
  have h1 := (((hasDerivAt_const x (-1:ℝ)).mul (hasDerivAt_id x)).mul (hasDerivAt_const x (t^2)⁻¹))
  have h2 := (((hasDerivAt_const x (-2:ℝ)).mul (hasDerivAt_const x (t^1)⁻¹)).mul ((hasDerivAt_id x).log (by positivity)))
  have h3 := (((hasDerivAt_const x (1/4:ℝ)).mul (hasDerivAt_const x (t^1)⁻¹)).mul ((hasDerivAt_id x).pow 2))
  have h4 := (((hasDerivAt_const x (1/36:ℝ)).mul (hasDerivAt_const x (t^2)⁻¹)).mul ((hasDerivAt_id x).pow 3))
  have h5 := (((hasDerivAt_const x (2/3:ℝ)).mul (hasDerivAt_const x t)).mul ((hasDerivAt_id x).log (by positivity)))
  have h6 := (((hasDerivAt_const x (4/3:ℝ)).mul (hasDerivAt_const x (t^2)⁻¹)).mul ((hasDerivAt_id x).log (by positivity)))
  have hd := ((((((h0.add h1).add h2).add h3).add h4).add h5).add h6)
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  simp only [id_eq,Pi.mul_apply,Pi.pow_apply]
  field_simp
  ring

theorem inner3Primitive_deriv (t u x : ℝ) (ht : 0 < t) (hu : 0 < u) (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => inner3Primitive t u x) (loss3Kernel t u x) x := by
  unfold inner3Primitive loss3Kernel
  have h0 := ((hasDerivAt_id x).mul (hasDerivAt_const x (t^1)⁻¹))
  have h1 := ((hasDerivAt_id x).mul (hasDerivAt_const x (u^1)⁻¹))
  have h2 := (((hasDerivAt_const x (1/8:ℝ)).mul (hasDerivAt_const x (t^2)⁻¹)).mul ((hasDerivAt_id x).pow 2))
  have h3 := ((((hasDerivAt_const x (1/2:ℝ)).mul (hasDerivAt_const x u)).mul (hasDerivAt_const x (t^1)⁻¹)).mul ((hasDerivAt_id x).log (by positivity)))
  have h4 := ((((hasDerivAt_const x (-7/36:ℝ)).mul (hasDerivAt_const x (t^2)⁻¹)).mul (hasDerivAt_const x (u^1)⁻¹)).mul ((hasDerivAt_id x).pow 3))
  have h5 := ((((hasDerivAt_const x (1/4:ℝ)).mul (hasDerivAt_const x u)).mul (hasDerivAt_id x)).mul (hasDerivAt_const x (t^2)⁻¹))
  have h6 := ((((hasDerivAt_const x (1/4:ℝ)).mul (hasDerivAt_const x (t^1)⁻¹)).mul (hasDerivAt_const x (u^1)⁻¹)).mul ((hasDerivAt_id x).pow 2))
  have h7 := ((((hasDerivAt_const x (1/12:ℝ)).mul (hasDerivAt_const x (t^2)⁻¹)).mul (hasDerivAt_const x (u^2))).mul ((hasDerivAt_id x).log (by positivity)))
  have h8 := ((((hasDerivAt_const x (2/3:ℝ)).mul (hasDerivAt_const x t)).mul (hasDerivAt_const x (u^1)⁻¹)).mul ((hasDerivAt_id x).log (by positivity)))
  have h9 := ((hasDerivAt_id x).log (by positivity))
  have hd := (((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9)
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  simp only [id_eq,Pi.mul_apply,Pi.pow_apply]
  field_simp
  ring

set_option maxHeartbeats 1000000 in
theorem middle3Primitive_deriv (t u : ℝ) (ht : 0 < t) (hu : 0 < u) :
    HasDerivAt (fun u : ℝ => middle3Primitive t u) (middle3Kernel t u) u := by
  unfold middle3Primitive middle3Kernel
  have h0 := ((hasDerivAt_const u (2:ℝ)).mul ((hasDerivAt_id u).log (by positivity)))
  have h1 := ((hasDerivAt_id u).mul (hasDerivAt_const u (Real.log (2:ℝ))))
  have h2 := ((hasDerivAt_const u (t^1)⁻¹).mul ((hasDerivAt_id u).log (by positivity)))
  have h3 := (((hasDerivAt_const u (1/2:ℝ)).mul (hasDerivAt_id u)).mul (hasDerivAt_const u (t^2)⁻¹))
  have h4 := (((hasDerivAt_const u (-1:ℝ)).mul (hasDerivAt_id u)).mul ((hasDerivAt_id u).log (by positivity)))
  have h5 := (((hasDerivAt_const u (2:ℝ)).mul (hasDerivAt_id u)).mul (hasDerivAt_const u (t^1)⁻¹))
  have h6 := (((hasDerivAt_const u (-14/9:ℝ)).mul (hasDerivAt_const u (t^2)⁻¹)).mul ((hasDerivAt_id u).log (by positivity)))
  have h7 := (((hasDerivAt_const u (-11/216:ℝ)).mul (hasDerivAt_const u (t^2)⁻¹)).mul ((hasDerivAt_id u).pow 3))
  have h8 := (((hasDerivAt_const u (-1/2:ℝ)).mul (hasDerivAt_const u (t^1)⁻¹)).mul ((hasDerivAt_id u).pow 2))
  have h9 := (((hasDerivAt_const u (-1/3:ℝ)).mul (hasDerivAt_const u t)).mul (((hasDerivAt_id u).log (by positivity)).pow 2))
  have h10 := (((hasDerivAt_const u (1/4:ℝ)).mul (hasDerivAt_const u (t^2)⁻¹)).mul ((hasDerivAt_id u).pow 2))
  have h11 := ((((hasDerivAt_const u (-1/4:ℝ)).mul (hasDerivAt_const u (t^1)⁻¹)).mul ((hasDerivAt_id u).pow 2)).mul ((hasDerivAt_id u).log (by positivity)))
  have h12 := ((((hasDerivAt_const u (-1/36:ℝ)).mul (hasDerivAt_const u (t^2)⁻¹)).mul ((hasDerivAt_id u).pow 3)).mul ((hasDerivAt_id u).log (by positivity)))
  have h13 := ((((hasDerivAt_const u (1/4:ℝ)).mul (hasDerivAt_const u (t^1)⁻¹)).mul ((hasDerivAt_id u).pow 2)).mul (hasDerivAt_const u (Real.log (2:ℝ))))
  have h14 := ((((hasDerivAt_const u (1/36:ℝ)).mul (hasDerivAt_const u (t^2)⁻¹)).mul ((hasDerivAt_id u).pow 3)).mul (hasDerivAt_const u (Real.log (2:ℝ))))
  have h15 := ((((hasDerivAt_const u (2/3:ℝ)).mul (hasDerivAt_const u t)).mul (hasDerivAt_const u (Real.log (2:ℝ)))).mul ((hasDerivAt_id u).log (by positivity)))
  have hd := (((((((((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9).add h10).add h11).add h12).add h13).add h14).add h15)
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  simp only [id_eq,Pi.mul_apply,Pi.pow_apply]
  field_simp
  ring

theorem outer2Primitive_deriv (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => outer2Primitive t) (reduced2 t) t := by
  unfold outer2Primitive reduced2
  have h0 := (((hasDerivAt_id t).log (by positivity)).pow 2)
  have h1 := ((hasDerivAt_const t (2:ℝ)).mul (hasDerivAt_id t))
  have h2 := ((hasDerivAt_const t (2:ℝ)).mul ((hasDerivAt_id t).log (by positivity)))
  have h3 := ((hasDerivAt_const t (-17/36:ℝ)).mul ((hasDerivAt_id t).pow 2))
  have h4 := ((hasDerivAt_const t (28/9:ℝ)).mul (((hasDerivAt_id t).pow 1).inv (by change t^1 ≠ 0; positivity)))
  have h5 := (((hasDerivAt_const t (-2:ℝ)).mul (hasDerivAt_const t (Real.log (2:ℝ)))).mul ((hasDerivAt_id t).log (by positivity)))
  have h6 := (((hasDerivAt_const t (-4/3:ℝ)).mul (((hasDerivAt_id t).pow 1).inv (by change t^1 ≠ 0; positivity))).mul (hasDerivAt_const t (Real.log (2:ℝ))))
  have h7 := (((hasDerivAt_const t (-1/3:ℝ)).mul ((hasDerivAt_id t).pow 2)).mul ((hasDerivAt_id t).log (by positivity)))
  have h8 := (((hasDerivAt_const t (1/3:ℝ)).mul ((hasDerivAt_id t).pow 2)).mul (hasDerivAt_const t (Real.log (2:ℝ))))
  have h9 := (((hasDerivAt_const t (4/3:ℝ)).mul (((hasDerivAt_id t).pow 1).inv (by change t^1 ≠ 0; positivity))).mul ((hasDerivAt_id t).log (by positivity)))
  have hd := (((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9)
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  simp only [id_eq,Pi.mul_apply,Pi.pow_apply,Pi.inv_apply]
  field_simp
  ring

theorem outer3Primitive_deriv (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => outer3Primitive t) (reduced3 t) t := by
  unfold outer3Primitive reduced3
  have h0 := ((hasDerivAt_const t (-85/27:ℝ)).mul (((hasDerivAt_id t).pow 1).inv (by change t^1 ≠ 0; positivity)))
  have h1 := ((hasDerivAt_const t (-1/2:ℝ)).mul (((hasDerivAt_id t).log (by positivity)).pow 2))
  have h2 := ((hasDerivAt_const t (-1/4:ℝ)).mul (hasDerivAt_id t))
  have h3 := ((hasDerivAt_const t (3/2:ℝ)).mul ((hasDerivAt_id t).log (by positivity)))
  have h4 := ((hasDerivAt_const t (17/432:ℝ)).mul ((hasDerivAt_id t).pow 2))
  have h5 := ((hasDerivAt_const t (Real.log (2:ℝ))).mul ((hasDerivAt_id t).log (by positivity)))
  have h6 := (((hasDerivAt_const t (-2:ℝ)).mul (hasDerivAt_id t)).mul ((hasDerivAt_id t).log (by positivity)))
  have h7 := (((hasDerivAt_const t (2:ℝ)).mul (hasDerivAt_id t)).mul (hasDerivAt_const t (Real.log (2:ℝ))))
  have h8 := (((hasDerivAt_const t (-17/36:ℝ)).mul ((hasDerivAt_id t).pow 2)).mul (hasDerivAt_const t (Real.log (2:ℝ))))
  have h9 := (((hasDerivAt_const t (-14/9:ℝ)).mul (((hasDerivAt_id t).pow 1).inv (by change t^1 ≠ 0; positivity))).mul ((hasDerivAt_id t).log (by positivity)))
  have h10 := (((hasDerivAt_const t (1/6:ℝ)).mul ((hasDerivAt_id t).pow 2)).mul (hasDerivAt_const t ((Real.log (2:ℝ))^2)))
  have h11 := (((hasDerivAt_const t (1/6:ℝ)).mul ((hasDerivAt_id t).pow 2)).mul (((hasDerivAt_id t).log (by positivity)).pow 2))
  have h12 := (((hasDerivAt_const t (14/9:ℝ)).mul (((hasDerivAt_id t).pow 1).inv (by change t^1 ≠ 0; positivity))).mul (hasDerivAt_const t (Real.log (2:ℝ))))
  have h13 := (((hasDerivAt_const t (17/36:ℝ)).mul ((hasDerivAt_id t).pow 2)).mul ((hasDerivAt_id t).log (by positivity)))
  have h14 := ((((hasDerivAt_const t (-1/3:ℝ)).mul ((hasDerivAt_id t).pow 2)).mul (hasDerivAt_const t (Real.log (2:ℝ)))).mul ((hasDerivAt_id t).log (by positivity)))
  have hd := ((((((((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9).add h10).add h11).add h12).add h13).add h14)
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  simp only [id_eq,Pi.mul_apply,Pi.pow_apply,Pi.inv_apply]
  field_simp
  ring

end ErdosBoundaryLoss

end

section

open Set MeasureTheory
namespace ErdosBoundaryLoss

theorem loss2_inner_integrable {t : ℝ} (ht : t ∈ Icc 1 2) :
    IntervalIntegrable (loss2Kernel t) volume t 2 := by
  have ht0 : t ≠ 0 := by have := ht.1; linarith
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le ht.2]
  intro x hx
  have hx0 : x ≠ 0 := by have := ht.1; have := hx.1; linarith
  apply ContinuousAt.continuousWithinAt
  unfold loss2Kernel
  fun_prop (disch := simp_all)

theorem loss2_inner_reduction {t : ℝ} (ht : t ∈ Icc 1 2) :
    (∫ x in t..2,loss2Kernel t x)=reduced2 t := by
  have htpos : 0 < t := by have := ht.1; linarith
  have hd : ∀ x ∈ uIcc t 2, HasDerivAt (inner2Primitive t) (loss2Kernel t x) x := by
    intro x hx
    rw [uIcc_of_le ht.2] at hx
    exact inner2Primitive_deriv t x htpos (lt_of_lt_of_le htpos hx.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (loss2_inner_integrable ht)]
  have ht0 : t ≠ 0 := ne_of_gt htpos
  unfold inner2Primitive reduced2
  norm_num
  field_simp
  ring

theorem loss3_inner_integrable {t u : ℝ} (ht : t ∈ Icc 1 2) (hu : u ∈ Icc t 2) :
    IntervalIntegrable (loss3Kernel t u) volume u 2 := by
  have ht0 : t ≠ 0 := by have := ht.1; linarith
  have hu0 : u ≠ 0 := by have := ht.1; have := hu.1; linarith
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hu.2]
  intro x hx
  have hx0 : x ≠ 0 := by have := ht.1; have := hu.1; have := hx.1; linarith
  apply ContinuousAt.continuousWithinAt
  unfold loss3Kernel
  fun_prop (disch := simp_all)

theorem loss3_inner_reduction {t u : ℝ} (ht : t ∈ Icc 1 2) (hu : u ∈ Icc t 2) :
    (∫ x in u..2,loss3Kernel t u x)=middle3Kernel t u := by
  have htpos : 0 < t := by have := ht.1; linarith
  have hupos : 0 < u := lt_of_lt_of_le htpos hu.1
  have hd : ∀ x ∈ uIcc u 2, HasDerivAt (inner3Primitive t u) (loss3Kernel t u x) x := by
    intro x hx
    rw [uIcc_of_le hu.2] at hx
    exact inner3Primitive_deriv t u x htpos hupos (lt_of_lt_of_le hupos hx.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (loss3_inner_integrable ht hu)]
  have ht0 : t ≠ 0 := ne_of_gt htpos
  have hu0 : u ≠ 0 := ne_of_gt hupos
  unfold inner3Primitive middle3Kernel
  norm_num
  field_simp
  ring

theorem loss3_middle_kernel_integrable {t : ℝ} (ht : t ∈ Icc 1 2) :
    IntervalIntegrable (middle3Kernel t) volume t 2 := by
  have ht0 : t ≠ 0 := by have := ht.1; linarith
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le ht.2]
  intro u hu
  have hu0 : u ≠ 0 := by have := ht.1; have := hu.1; linarith
  apply ContinuousAt.continuousWithinAt
  unfold middle3Kernel
  fun_prop (disch := simp_all)

theorem loss3_middle_reduction {t : ℝ} (ht : t ∈ Icc 1 2) :
    (∫ u in t..2,∫ x in u..2,loss3Kernel t u x)=reduced3 t := by
  have htpos : 0 < t := by have := ht.1; linarith
  have hi : (∫ u in t..2,∫ x in u..2,loss3Kernel t u x)=∫ u in t..2,middle3Kernel t u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.2] at hu
    exact loss3_inner_reduction ht hu
  rw [hi]
  have hd : ∀ u ∈ uIcc t 2, HasDerivAt (middle3Primitive t) (middle3Kernel t u) u := by
    intro u hu
    rw [uIcc_of_le ht.2] at hu
    exact middle3Primitive_deriv t u htpos (lt_of_lt_of_le htpos hu.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (loss3_middle_kernel_integrable ht)]
  have ht0 : t ≠ 0 := ne_of_gt htpos
  unfold middle3Primitive reduced3
  norm_num
  field_simp
  ring

end ErdosBoundaryLoss

end

section

open Set MeasureTheory
namespace ErdosBoundaryLoss

theorem reduced2_integrable : IntervalIntegrable reduced2 volume 1 2 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)]
  intro t ht
  have ht0 : t ≠ 0 := by have := ht.1; linarith
  apply ContinuousAt.continuousWithinAt
  unfold reduced2
  fun_prop (disch := simp_all)

theorem reduced3_integrable : IntervalIntegrable reduced3 volume 1 2 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)]
  intro t ht
  have ht0 : t ≠ 0 := by have := ht.1; linarith
  apply ContinuousAt.continuousWithinAt
  unfold reduced3
  fun_prop (disch := simp_all)

theorem L2_eq : L2=-(35:ℝ)/36-(Real.log 2)^2+3*Real.log 2 := by
  have hi : L2=∫ t in (1:ℝ)..2,reduced2 t := by
    unfold L2
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at ht
    exact loss2_inner_reduction ht
  rw [hi]
  have hd : ∀ t ∈ uIcc (1:ℝ) 2, HasDerivAt outer2Primitive (reduced2 t) t := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at ht
    exact outer2Primitive_deriv t (by have := ht.1; linarith)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd reduced2_integrable]
  unfold outer2Primitive
  norm_num
  ring

theorem L3_eq : L3=(623:ℝ)/432-(19:ℝ)/12*Real.log 2+(1:ℝ)/3*(Real.log 2)^2 := by
  have hi : L3=∫ t in (1:ℝ)..2,reduced3 t := by
    unfold L3
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at ht
    exact loss3_middle_reduction ht
  rw [hi]
  have hd : ∀ t ∈ uIcc (1:ℝ) 2, HasDerivAt outer3Primitive (reduced3 t) t := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at ht
    exact outer3Primitive_deriv t (by have := ht.1; linarith)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd reduced3_integrable]
  unfold outer3Primitive
  norm_num
  ring

end ErdosBoundaryLoss

end

section

namespace ErdosBoundaryLoss

theorem log_two_bounds : (69:ℝ)/100 < Real.log 2 ∧ Real.log 2 < (7:ℝ)/10 := by
  constructor
  · linarith [Real.log_two_gt_d9]
  · linarith [Real.log_two_lt_d9]

theorem L2_lt : L2 < (64:ℝ)/100 := by
  rw [L2_eq]
  have h := log_two_bounds
  have hp := mul_pos (sub_pos.mpr h.2)
    (show 0 < 3-(7:ℝ)/10-Real.log 2 by linarith)
  nlinarith

theorem L3_lt : L3 < (51:ℝ)/100 := by
  rw [L3_eq]
  have h := log_two_bounds
  have hp := mul_pos (sub_pos.mpr h.1)
    (show 0 < (19:ℝ)/12-(Real.log 2+(69:ℝ)/100)/3 by linarith)
  nlinarith

end ErdosBoundaryLoss

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_OrderedTriangleFubini
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

theorem ordered_triangle_swap {f : ℝ×ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x ∈ Icc (1:ℝ) 2,∀ t ∈ Icc (1:ℝ) 2,|f (x,t)| ≤ C) :
    (∫ x : ℝ in 1..2,∫ t : ℝ in 1..x,f (x,t))=
      ∫ t : ℝ in 1..2,∫ x : ℝ in t..2,f (x,t) := by
  classical
  let g : ℝ×ℝ → ℝ := fun p => if p.2 ≤ p.1 then f p else 0
  have hg : Measurable g := Measurable.ite (measurableSet_le measurable_snd measurable_fst) hf measurable_const
  have hb : ∀ x ∈ Icc (1:ℝ) 2,∀ t ∈ Icc (1:ℝ) 2,|g (x,t)| ≤ C := by
    intro x hx t ht
    dsimp only [g]
    split_ifs
    · exact hbound x hx t ht
    · simpa only [abs_zero] using hC
  have hs := bounded_rectangle_swap hg 1 2 1 2 C hb
  have hleft (x : ℝ) (hx : x ∈ Icc (1:ℝ) 2) :
      (∫ t in Icc (1:ℝ) 2,g (x,t))=∫ t : ℝ in 1..x,f (x,t) := by
    have hset : Icc (1:ℝ) 2 ∩ Iic x=Icc 1 x := by
      ext t
      constructor
      · rintro ⟨ht,hx'⟩; exact ⟨ht.1,hx'⟩
      · intro ht; exact ⟨⟨ht.1,ht.2.trans hx.2⟩,ht.2⟩
    change (∫ t in Icc (1:ℝ) 2,(Iic x).indicator (fun t => f (x,t)) t)=_
    rw [setIntegral_indicator measurableSet_Iic,hset,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hx.1]
  have hright (t : ℝ) (ht : t ∈ Icc (1:ℝ) 2) :
      (∫ x in Icc (1:ℝ) 2,g (x,t))=∫ x : ℝ in t..2,f (x,t) := by
    have hset : Icc (1:ℝ) 2 ∩ Ici t=Icc t 2 := by
      ext x
      constructor
      · rintro ⟨hx,ht'⟩; exact ⟨ht',hx.2⟩
      · intro hx; exact ⟨⟨ht.1.trans hx.1,hx.2⟩,hx.1⟩
    change (∫ x in Icc (1:ℝ) 2,(Ici t).indicator (fun x => f (x,t)) x)=_
    rw [setIntegral_indicator measurableSet_Ici,hset,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le ht.2]
  have he : (∫ x in Icc (1:ℝ) 2,∫ t in Icc (1:ℝ) 2,g (x,t))=
      ∫ x in Icc (1:ℝ) 2,∫ t : ℝ in 1..x,f (x,t) :=
    setIntegral_congr_fun measurableSet_Icc hleft
  have ho : (∫ t in Icc (1:ℝ) 2,∫ x in Icc (1:ℝ) 2,g (x,t))=
      ∫ t in Icc (1:ℝ) 2,∫ x : ℝ in t..2,f (x,t) :=
    setIntegral_congr_fun measurableSet_Icc hright
  rw [he,ho] at hs
  simpa only [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤2)] using hs

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

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SecondLossKernel
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
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry

theorem omissionForce_le_one (i : Side) (r b : ℝ) : omissionForce i r b ≤ 1 := by
  cases i with
  | even => norm_num [omissionForce]
  | odd =>
    have hc : (upperCutoff .odd r b)⁻¹ ≤ (1:ℝ) :=
      (inv_le_one₀ ((by norm_num : (0:ℝ)<1).trans_le (upperCutoff_bounds .odd r b).1)).mpr
        (upperCutoff_bounds .odd r b).1
    have hb : 0 ≤ survivorBaseline b := inv_nonneg.mpr (zero_le_one.trans (baseCutoff_bounds b).1)
    change (upperCutoff .odd r b)⁻¹-survivorBaseline b ≤ 1
    linarith

theorem secondKernel_continuous : Continuous secondKernel := by
  have hf : Continuous (fun p : ℝ×ℝ => omissionForce .odd (2*p.1+2-p.2) p.2) :=
    (omissionForce_continuous .odd).comp
      (((continuous_const.mul continuous_fst).add continuous_const |>.sub continuous_snd).prodMk continuous_snd)
  have hp : Continuous (fun p : ℝ×ℝ => 2*(p.1^2-1)/(max 1 p.2)) :=
    (continuous_const.mul ((continuous_fst.pow 2).sub continuous_const)).div
      (continuous_const.max continuous_snd) (fun p => ne_of_gt
        ((by norm_num : (0:ℝ)<1).trans_le (le_max_left 1 p.2)))
  exact hp.mul hf

theorem secondKernel_bound {y x : ℝ} (hy : y ∈ Icc (1:ℝ) 3) (hx : x ∈ Icc (1:ℝ) 2) :
    |secondKernel (y,x)| ≤ 16 := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hpoly : 0 ≤ y^2-1 := by nlinarith [hy.1]
  have hpoly8 : y^2-1 ≤ 8 := by nlinarith [hy.1,hy.2]
  have hp0 : 0 ≤ 2*(y^2-1)/x := div_nonneg (mul_nonneg (by norm_num) hpoly) hx0.le
  have hp16 : 2*(y^2-1)/x ≤ 16 := by
    apply (div_le_iff₀ hx0).mpr
    nlinarith [hx.1]
  unfold secondKernel
  dsimp only
  rw [max_eq_right hx.1,abs_of_nonneg (mul_nonneg hp0 (omissionForce_nonnegative .odd _ _))]
  calc
    _ ≤ (2*(y^2-1)/x)*1 := mul_le_mul_of_nonneg_left (omissionForce_le_one .odd _ _) hp0
    _ ≤ 16 := by simpa only [mul_one] using hp16

theorem second_density_kernel (y : ℝ) :
    omissionDensity 1 .even y=∫ x : ℝ in 1..2,secondKernel (y,x) := by
  change 2*(y^2-1)*(∫ x : ℝ in 1..upperCutoff .even (2*y+2) 2,
    omissionForce .odd (2*y+2-x) x/(max 1 x))=_
  have hc : upperCutoff .even (2*y+2) 2=2 := by norm_num [upperCutoff]
  rw [hc,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _hx
  dsimp only [secondKernel]
  ring

end ErdosOmissionBindings

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SecondLossIntegration
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
open ErdosContinuousOmission ErdosBoundaryLoss

theorem secondKernel_integral {x : ℝ} (hx : x ∈ Icc (1:ℝ) 2) :
    (∫ y in Icc (1:ℝ) 3,secondKernel (y,x))=∫ t : ℝ in 1..x,loss2Kernel t x := by
  have hx0 : x ≠ 0 := by linarith [hx.1]
  have h := integrated_force_window x 1 3 x 1 (by norm_num) hx.1 hx.2
    (by linarith [hx.1]) (by linarith [hx.2])
  have he : (fun y : ℝ => secondKernel (y,x))=
      (fun y => (2/x)*((y^2-1)*omissionForce .odd (2*y+2-x) x)) := by
    funext y
    simp only [secondKernel,max_eq_right hx.1]
    ring
  rw [he,integral_const_mul,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤3),h,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hx.1] at ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  dsimp only [loss2Kernel]
  field_simp
  ring

theorem second_loss_ordered_integral :
    omissionLossTerm 1=∫ x : ℝ in 1..2,∫ t : ℝ in 1..x,loss2Kernel t x := by
  rw [second_loss_bounded_jb247]
  simp_rw [second_density_kernel]
  rw [intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤3)]
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤2),← integral_Icc_eq_integral_Ioc]
  rw [bounded_rectangle_swap secondKernel_continuous.measurable 1 3 1 2 16
    (fun _ hy _ hx => secondKernel_bound hy hx)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  exact secondKernel_integral hx

end ErdosOmissionBindings

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_ThirdInnerKernel
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
open ErdosContinuousOmission ErdosBoundaryLoss

theorem lossTwo_measurable : Measurable (fun p : ℝ×ℝ => loss2Kernel p.2 p.1) := by
  unfold loss2Kernel
  fun_prop

theorem lossTwo_bound {x t : ℝ} (hx : x ∈ Icc (1:ℝ) 2) (ht : t ∈ Icc (1:ℝ) 2) :
    |loss2Kernel t x| ≤ 16 := by
  have hx0 : 0 < x := by linarith [hx.1]
  have ht0 : 0 < t := by linarith [ht.1]
  have he : loss2Kernel t x=((x+2*t-2)^2*(x+2*t+4))/(12*x*t^2) := by
    unfold loss2Kernel
    field_simp
    ring
  have hs : 0 ≤ x+2*t-2 ∧ x+2*t-2 ≤ 4 := by constructor <;> linarith [hx.1,hx.2,ht.1,ht.2]
  have hs2 : (x+2*t-2)^2 ≤ 16 := by nlinarith
  have hs4 : 0 ≤ x+2*t+4 ∧ x+2*t+4 ≤ 10 := by constructor <;> linarith [hx.1,hx.2,ht.1,ht.2]
  have hnum : (x+2*t-2)^2*(x+2*t+4) ≤ 160 := by
    have h := mul_le_mul hs2 hs4.2 hs4.1 (by norm_num : (0:ℝ)≤16)
    norm_num at h
    exact h
  have ht2 : 1 ≤ t^2 := by nlinarith [ht.1]
  have hden : 12 ≤ 12*x*t^2 := by
    have h := mul_le_mul hx.1 ht2 (by norm_num : (0:ℝ)≤1) hx0.le
    nlinarith
  have hden0 : 0 < 12*x*t^2 := by positivity
  rw [he,abs_of_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) hs4.1) hden0.le)]
  apply (div_le_iff₀ hden0).mpr
  nlinarith

theorem actual_second_loss_eq_L2 : omissionLossTerm 1=L2 := by
  rw [second_loss_ordered_integral]
  have h := ordered_triangle_swap lossTwo_measurable (by norm_num : (0:ℝ)≤16)
    (fun _ hx _ ht => lossTwo_bound hx ht)
  exact h

end ErdosOmissionBindings

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosBoundaryLoss

theorem lossThree_bound {x u t : ℝ} (hx : x ∈ Icc (1:ℝ) 2)
    (hu : u ∈ Icc (1:ℝ) 2) (ht : t ∈ Icc (1:ℝ) 2) : |loss3Kernel t u x| ≤ 64 := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hu0 : 0 < u := by linarith [hu.1]
  have ht0 : 0 < t := by linarith [ht.1]
  have hs0 : 0 ≤ x+u+2*t := by positivity
  have hs8 : x+u+2*t ≤ 8 := by linarith [hx.2,hu.2,ht.2]
  have hsx : 2*x ≤ x+u+2*t := by linarith [hx.2,hu.1,ht.1]
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ)≤2*x) hsx 3
  have hnum0 : 0 ≤ (x+u+2*t)^3-8*x^3 := by nlinarith
  have hp8 := pow_le_pow_left₀ hs0 hs8 3
  have hnum : (x+u+2*t)^3-8*x^3 ≤ 512 := by nlinarith [pow_nonneg hx0.le 3]
  have ht2 : 1 ≤ t^2 := by nlinarith [ht.1]
  have hxu : (1:ℝ) ≤ x*u := by simpa only [one_mul] using mul_le_mul hx.1 hu.1 (by norm_num : (0:ℝ)≤1) hx0.le
  have hprod : (1:ℝ) ≤ x*u*t^2 := by
    simpa only [one_mul] using mul_le_mul hxu ht2 (by norm_num : (0:ℝ)≤1) (mul_pos hx0 hu0).le
  have hden : 12 ≤ 12*x*u*t^2 := by nlinarith
  have hden0 : 0 < 12*x*u*t^2 := by positivity
  rw [loss3Kernel,abs_of_nonneg (div_nonneg hnum0 hden0.le)]
  apply (div_le_iff₀ hden0).mpr
  nlinarith

theorem clampedThird_eq {x u t : ℝ} (hx : x ∈ Icc (1:ℝ) 2)
    (hu : u ∈ Icc (1:ℝ) 2) (ht : t ∈ Icc (1:ℝ) 2) :
    clampedThird x u t=loss3Kernel t u x := by
  simp only [clampedThird,baseCutoff_on hx.1 hx.2,baseCutoff_on hu.1 hu.2,baseCutoff_on ht.1 ht.2]

theorem clampedThird_bound (x u t : ℝ) : |clampedThird x u t| ≤ 64 :=
  lossThree_bound (baseCutoff_bounds x) (baseCutoff_bounds u) (baseCutoff_bounds t)

theorem clampedThird_continuous :
    Continuous (fun p : ℝ×ℝ×ℝ => clampedThird p.1 p.2.1 p.2.2) := by
  have hn : Continuous (fun p : ℝ×ℝ×ℝ =>
      (baseCutoff p.1+baseCutoff p.2.1+2*baseCutoff p.2.2)^3-8*(baseCutoff p.1)^3) := by
    unfold baseCutoff
    fun_prop
  have hd : Continuous (fun p : ℝ×ℝ×ℝ =>
      12*baseCutoff p.1*baseCutoff p.2.1*(baseCutoff p.2.2)^2) := by
    unfold baseCutoff
    fun_prop
  have hp (a : ℝ) : 0 < baseCutoff a := zero_lt_one.trans_le (baseCutoff_bounds a).1
  exact hn.div hd (fun p => ne_of_gt
    (mul_pos (mul_pos (mul_pos (by norm_num) (hp p.1)) (hp p.2.1)) (sq_pos_of_pos (hp p.2.2))))

theorem baseCutoff_continuous : Continuous baseCutoff := by unfold baseCutoff; fun_prop

end ErdosOmissionBindings

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceAdmission

theorem odd_gate_indicator (H : Profile) (y : ℝ) :
    gate H .odd (2*y+2) 2=
      ∫ x : ℝ in 1..2,if x≤y then H .even (2*y+2-x) x/(max 1 x) else 0 := by
  classical
  have heq : Ioc (1:ℝ) (upperCutoff .odd (2*y+2) 2)=Ioc (1:ℝ) 2 ∩ Iic y := by
    ext x
    have hc := mem_upperCutoff .odd (2*y+2) 2 x
    constructor
    · intro hx
      obtain ⟨hx1,hx2,_hxb,ha⟩ := hc.mp hx
      rw [strong_gate_below_two hx2] at ha
      refine ⟨⟨hx1,hx2⟩,?_⟩
      change x≤y
      linarith
    · rintro ⟨⟨hx1,hx2⟩,hxy⟩
      apply hc.mpr
      refine ⟨hx1,hx2,hx2,?_⟩
      rw [strong_gate_below_two hx2]
      change x≤y at hxy
      linarith
  rw [gate,intervalIntegral.integral_of_le (upperCutoff_bounds .odd (2*y+2) 2).1,
    intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤2)]
  change (∫ x in Ioc (1:ℝ) (upperCutoff .odd (2*y+2) 2),H .even (2*y+2-x) x/(max 1 x))=
    ∫ x in Ioc (1:ℝ) 2,(Iic y).indicator (fun x => H .even (2*y+2-x) x/(max 1 x)) x
  rw [setIntegral_indicator measurableSet_Iic,heq]

theorem gate_force_bounds (i : Side) (r b : ℝ) :
    0 ≤ gate omissionForce i r b ∧ gate omissionForce i r b ≤ 1 := by
  have hnon := gate_nonnegative omissionForce_nonnegative i r b
  refine ⟨hnon,?_⟩
  have hb (x : ℝ) : |omissionForce i.flip (r-x) x/(max 1 x)| ≤ 1 := by
    have hd : 0 < max (1:ℝ) x := (by norm_num : (0:ℝ)<1).trans_le (le_max_left 1 x)
    rw [abs_div,abs_of_pos hd,abs_of_nonneg (omissionForce_nonnegative _ _ _)]
    exact (div_le_one hd).mpr ((omissionForce_le_one _ _ _).trans (le_max_left 1 x))
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a:=1) (b:=upperCutoff i r b)
    (C:=1) (f:=fun x => omissionForce i.flip (r-x) x/(max 1 x))
    (fun x _ => by simpa only [Real.norm_eq_abs] using hb x)
  have hc := upperCutoff_bounds i r b
  rw [Real.norm_eq_abs,one_mul,abs_of_nonneg (by linarith : 0 ≤ upperCutoff i r b-1)] at h
  change |gate omissionForce i r b| ≤ upperCutoff i r b-1 at h
  rw [abs_of_nonneg hnon] at h
  linarith

theorem thirdKernel_measurable : Measurable thirdKernel := by
  have hg := gate_continuous omissionForce_continuous .even
  have hc : Continuous (fun p : ℝ×ℝ => gate omissionForce .even (2*p.1+2-p.2) p.2) :=
    hg.comp (((continuous_const.mul continuous_fst).add continuous_const |>.sub continuous_snd).prodMk continuous_snd)
  have hp : Measurable (fun p : ℝ×ℝ => 2*p.1^2/(max 1 p.2)) := by fun_prop
  exact Measurable.ite (measurableSet_le measurable_snd measurable_fst) (hp.mul hc.measurable) measurable_const

theorem thirdKernel_bound {y x : ℝ} (hy : y ∈ Icc (0:ℝ) 4) (hx : x ∈ Icc (1:ℝ) 2) :
    |thirdKernel (y,x)| ≤ 32 := by
  have hx0 : 0 < x := by linarith [hx.1]
  unfold thirdKernel
  dsimp only
  split_ifs
  · rw [max_eq_right hx.1]
    have hp0 : 0 ≤ 2*y^2/x := by positivity
    have hp32 : 2*y^2/x ≤ 32 := by
      apply (div_le_iff₀ hx0).mpr
      nlinarith [hy.1,hy.2,hx.1]
    rw [abs_of_nonneg (mul_nonneg hp0 (gate_force_bounds _ _ _).1)]
    exact (mul_le_mul_of_nonneg_left (gate_force_bounds _ _ _).2 hp0).trans (by simpa only [mul_one] using hp32)
  · norm_num

theorem third_density_kernel (y : ℝ) :
    omissionDensity 2 .odd y=∫ x : ℝ in 1..2,thirdKernel (y,x) := by
  change 2*y^2*gate (gate omissionForce) .odd (2*y+2) 2=_
  rw [odd_gate_indicator,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _hx
  dsimp only [thirdKernel]
  split_ifs <;> ring

end ErdosOmissionBindings

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry

theorem thirdInnerKernel_continuous (x : ℝ) : Continuous (thirdInnerKernel x) := by
  have hf : Continuous (fun p : ℝ×ℝ => omissionForce .odd (2*p.1+2-x-p.2) p.2) :=
    (omissionForce_continuous .odd).comp
      ((((continuous_const.mul continuous_fst).add continuous_const |>.sub continuous_const).sub continuous_snd).prodMk continuous_snd)
  have hp : Continuous (fun p : ℝ×ℝ => p.1^2/(max 1 p.2)) :=
    (continuous_fst.pow 2).div (continuous_const.max continuous_snd) (fun p => ne_of_gt
      ((by norm_num : (0:ℝ)<1).trans_le (le_max_left 1 p.2)))
  exact hp.mul hf

theorem thirdInnerKernel_bound {x y u : ℝ} (hx : x ∈ Icc (1:ℝ) 2)
    (hy : y ∈ Icc x 4) (hu : u ∈ Icc (1:ℝ) x) : |thirdInnerKernel x (y,u)| ≤ 16 := by
  have hu0 : 0 < u := by linarith [hu.1]
  have hy0 : 0 ≤ y := by linarith [hx.1,hy.1]
  have hp0 : 0 ≤ y^2/u := div_nonneg (sq_nonneg _) hu0.le
  have hp16 : y^2/u ≤ 16 := by
    apply (div_le_iff₀ hu0).mpr
    nlinarith [hy.2,hu.1]
  unfold thirdInnerKernel
  dsimp only
  rw [max_eq_right hu.1,abs_of_nonneg (mul_nonneg hp0 (omissionForce_nonnegative _ _ _))]
  exact (mul_le_mul_of_nonneg_left (omissionForce_le_one _ _ _) hp0).trans (by simpa only [mul_one] using hp16)

theorem third_even_gate (y : ℝ) {x : ℝ} (hx : x ∈ Icc (1:ℝ) 2) :
    y^2*gate omissionForce .even (2*y+2-x) x=
      ∫ u : ℝ in 1..x,thirdInnerKernel x (y,u) := by
  have hc : upperCutoff .even (2*y+2-x) x=x := baseCutoff_on hx.1 hx.2
  rw [gate,hc,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _hu
  dsimp only [thirdInnerKernel,Side.flip]
  ring

end ErdosOmissionBindings

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_ThirdMovingIntegrals
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
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosContinuousBoundary ErdosBoundaryLoss

theorem thirdLowerIntegral_continuous : Continuous thirdLowerIntegral := by
  let F : (ℝ×ℝ) → ℝ → ℝ := fun p t => clampedThird p.1 p.2 t
  have hF : Continuous F.uncurry := by
    change Continuous ((fun q : ℝ×ℝ×ℝ => clampedThird q.1 q.2.1 q.2.2) ∘
      (fun p : (ℝ×ℝ)×ℝ => (p.1.1,p.1.2,p.2)))
    exact clampedThird_continuous.comp
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  exact continuous_variable_upper_integral F hF (fun p => baseCutoff p.2)
    (baseCutoff_continuous.comp continuous_snd)

theorem thirdUpperIntegral_continuous : Continuous thirdUpperIntegral := by
  let F : (ℝ×ℝ) → ℝ → ℝ := fun p x => clampedThird x p.1 p.2
  have hF : Continuous F.uncurry := by
    change Continuous ((fun q : ℝ×ℝ×ℝ => clampedThird q.1 q.2.1 q.2.2) ∘
      (fun p : (ℝ×ℝ)×ℝ => (p.2,p.1.1,p.1.2)))
    exact clampedThird_continuous.comp
      (continuous_snd.prodMk (continuous_fst.fst.prodMk continuous_fst.snd))
  have h2 := continuous_variable_upper_integral F hF (fun _ => (2:ℝ)) continuous_const
  have hc := continuous_variable_upper_integral F hF (fun p => baseCutoff p.1)
    (baseCutoff_continuous.comp continuous_fst)
  have he (p : ℝ×ℝ) : (∫ x : ℝ in 1..2,F p x)-(∫ x : ℝ in 1..baseCutoff p.1,F p x)=thirdUpperIntegral p := by
    have hf : Continuous (F p) := by
      change Continuous (F.uncurry ∘ (fun x : ℝ => (p,x)))
      exact hF.comp (continuous_const.prodMk continuous_id)
    have hi := intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (μ := volume) 1 (baseCutoff p.1))
      (hf.intervalIntegrable (μ := volume) (baseCutoff p.1) 2)
    change (∫ x in 1..2,F p x)-(∫ x in 1..baseCutoff p.1,F p x)=∫ x in baseCutoff p.1..2,F p x
    linarith
  exact (h2.sub hc).congr he

theorem thirdLowerIntegral_bound (p : ℝ×ℝ) : |thirdLowerIntegral p| ≤ 64 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a:=1) (b:=baseCutoff p.2)
    (C:=64) (f:=fun t => clampedThird p.1 p.2 t)
    (fun t _ => by simpa only [Real.norm_eq_abs] using clampedThird_bound p.1 p.2 t)
  have hc := baseCutoff_bounds p.2
  change |thirdLowerIntegral p| ≤ 64
  rw [Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ baseCutoff p.2-1)] at h
  exact h.trans (by nlinarith)

theorem thirdUpperIntegral_bound (p : ℝ×ℝ) : |thirdUpperIntegral p| ≤ 64 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a:=baseCutoff p.1) (b:=2)
    (C:=64) (f:=fun x => clampedThird x p.1 p.2)
    (fun x _ => by simpa only [Real.norm_eq_abs] using clampedThird_bound x p.1 p.2)
  have hc := baseCutoff_bounds p.1
  change |thirdUpperIntegral p| ≤ 64
  rw [Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ 2-baseCutoff p.1)] at h
  exact h.trans (by nlinarith)

theorem thirdLowerIntegral_eq {x u : ℝ} (hx : x ∈ Icc (1:ℝ) 2) (hu : u ∈ Icc (1:ℝ) 2) :
    thirdLowerIntegral (x,u)=∫ t : ℝ in 1..u,loss3Kernel t u x := by
  rw [thirdLowerIntegral,baseCutoff_on hu.1 hu.2]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hu.1] at ht
  exact clampedThird_eq hx hu ⟨ht.1,ht.2.trans hu.2⟩

theorem thirdUpperIntegral_eq {u t : ℝ} (hu : u ∈ Icc (1:ℝ) 2) (ht : t ∈ Icc (1:ℝ) 2) :
    thirdUpperIntegral (u,t)=∫ x : ℝ in u..2,loss3Kernel t u x := by
  rw [thirdUpperIntegral,baseCutoff_on hu.1 hu.2]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hu.2] at hx
  exact clampedThird_eq ⟨hu.1.trans hx.1,hx.2⟩ hu ht

end ErdosOmissionBindings

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
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosBoundaryLoss

theorem thirdInner_integral {x u : ℝ} (hx : x ∈ Icc (1:ℝ) 2) (hu : u ∈ Icc (1:ℝ) x) :
    (2/x)*(∫ y in Icc x 4,thirdInnerKernel x (y,u))=
      ∫ t : ℝ in 1..u,loss3Kernel t u x := by
  have hx0 : x ≠ 0 := by linarith [hx.1]
  have hu0 : u ≠ 0 := by linarith [hu.1]
  have hu2 : u ≤ 2 := hu.2.trans hx.2
  have h := integrated_force_window (x+u) x 4 u 0 (by linarith [hx.1]) hu.1 hu2
    (by linarith [hx.2,hu.1]) (by linarith [hx.2])
  have he : (fun y : ℝ => thirdInnerKernel x (y,u))=
      (fun y => u⁻¹*(y^2*omissionForce .odd (2*y+2-(x+u)) u)) := by
    funext y
    have hh : 2*y+2-x-u=2*y+2-(x+u) := by ring
    simp only [thirdInnerKernel,max_eq_right hu.1,hh]
    ring
  rw [he,integral_const_mul,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [hx.2] : x≤4)]
  simp only [sub_zero,zero_mul,sub_zero] at h
  rw [h,← mul_assoc,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hu.1] at ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  dsimp only [loss3Kernel]
  field_simp
  ring

theorem thirdKernel_integral {x : ℝ} (hx : x ∈ Icc (1:ℝ) 2) :
    (∫ y in Icc (0:ℝ) 4,thirdKernel (y,x))=
      ∫ u : ℝ in 1..x,∫ t : ℝ in 1..u,loss3Kernel t u x := by
  classical
  have he : (fun y : ℝ => thirdKernel (y,x))=
      (Ici x).indicator (fun y => (2/x)*(y^2*gate omissionForce .even (2*y+2-x) x)) := by
    funext y
    dsimp only [thirdKernel]
    by_cases hh : x≤y
    · rw [ite_eq_left hh,indicator_of_mem (show y ∈ Ici x from hh),max_eq_right hx.1]
      ring
    · rw [ite_eq_right hh,indicator_of_notMem (show y ∉ Ici x from hh)]
  have hset : Icc (0:ℝ) 4 ∩ Ici x=Icc x 4 := by
    ext y
    constructor
    · rintro ⟨hy,hxy⟩; exact ⟨hxy,hy.2⟩
    · intro hy; exact ⟨⟨by linarith [hx.1,hy.1],hy.2⟩,hy.1⟩
  rw [he,setIntegral_indicator measurableSet_Ici,hset,integral_const_mul]
  simp_rw [third_even_gate _ hx,intervalIntegral.integral_of_le hx.1,← integral_Icc_eq_integral_Ioc]
  rw [bounded_rectangle_swap (thirdInnerKernel_continuous x).measurable x 4 1 x 16
    (fun _ hy _ hu => thirdInnerKernel_bound hx hy hu),← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  exact thirdInner_integral hx hu

theorem third_loss_ordered_integral :
    omissionLossTerm 2=∫ x : ℝ in 1..2,∫ u : ℝ in 1..x,∫ t : ℝ in 1..u,loss3Kernel t u x := by
  rw [third_loss_bounded_jb247]
  simp_rw [third_density_kernel]
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤4)]
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤2),← integral_Icc_eq_integral_Ioc]
  rw [bounded_rectangle_swap thirdKernel_measurable 0 4 1 2 32
    (fun _ hy _ hx => thirdKernel_bound hy hx)]
  exact setIntegral_congr_fun measurableSet_Icc (fun _ hx => thirdKernel_integral hx)

end ErdosOmissionBindings

end

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosBoundaryLoss

theorem third_inner_rectangle_swap {u : ℝ} (hu : u ∈ Icc (1:ℝ) 2) :
    (∫ x : ℝ in u..2,∫ t : ℝ in 1..u,loss3Kernel t u x)=
      ∫ t : ℝ in 1..u,∫ x : ℝ in u..2,loss3Kernel t u x := by
  have hm : Measurable (fun p : ℝ×ℝ => loss3Kernel p.2 u p.1) := by unfold loss3Kernel; fun_prop
  have hb : ∀ x ∈ Icc u 2,∀ t ∈ Icc (1:ℝ) u,|loss3Kernel t u x| ≤ 64 := by
    intro x hx t ht
    exact lossThree_bound ⟨hu.1.trans hx.1,hx.2⟩ hu ⟨ht.1,ht.2.trans hu.2⟩
  have h := bounded_rectangle_swap hm u 2 1 u 64 hb
  simpa only [intervalIntegral.integral_of_le hu.1,intervalIntegral.integral_of_le hu.2,
    ← integral_Icc_eq_integral_Ioc] using h

theorem third_ordered_reversal :
    (∫ x : ℝ in 1..2,∫ u : ℝ in 1..x,∫ t : ℝ in 1..u,loss3Kernel t u x)=L3 := by
  calc
    _ = ∫ x : ℝ in 1..2,∫ u : ℝ in 1..x,thirdLowerIntegral (x,u) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num : (1:ℝ)≤2)] at hx
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hx.1] at hu
      exact (thirdLowerIntegral_eq hx ⟨hu.1,hu.2.trans hx.2⟩).symm
    _ = ∫ u : ℝ in 1..2,∫ x : ℝ in u..2,thirdLowerIntegral (x,u) :=
      ordered_triangle_swap thirdLowerIntegral_continuous.measurable (by norm_num : (0:ℝ)≤64)
        (fun _ _ _ _ => thirdLowerIntegral_bound _)
    _ = ∫ u : ℝ in 1..2,∫ t : ℝ in 1..u,∫ x : ℝ in u..2,loss3Kernel t u x := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le (by norm_num : (1:ℝ)≤2)] at hu
      have he : (∫ x : ℝ in u..2,thirdLowerIntegral (x,u))=
          ∫ x : ℝ in u..2,∫ t : ℝ in 1..u,loss3Kernel t u x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hu.2] at hx
        exact thirdLowerIntegral_eq ⟨hu.1.trans hx.1,hx.2⟩ hu
      exact he.trans (third_inner_rectangle_swap hu)
    _ = ∫ u : ℝ in 1..2,∫ t : ℝ in 1..u,thirdUpperIntegral (u,t) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le (by norm_num : (1:ℝ)≤2)] at hu
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hu.1] at ht
      exact (thirdUpperIntegral_eq hu ⟨ht.1,ht.2.trans hu.2⟩).symm
    _ = ∫ t : ℝ in 1..2,∫ u : ℝ in t..2,thirdUpperIntegral (u,t) :=
      ordered_triangle_swap thirdUpperIntegral_continuous.measurable (by norm_num : (0:ℝ)≤64)
        (fun _ _ _ _ => thirdUpperIntegral_bound _)
    _ = L3 := by
      unfold L3
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num : (1:ℝ)≤2)] at ht
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le ht.2] at hu
      exact thirdUpperIntegral_eq ⟨ht.1.trans hu.1,hu.2⟩ ht

theorem actual_third_loss_eq_L3 : omissionLossTerm 2=L3 :=
  third_loss_ordered_integral.trans third_ordered_reversal

end ErdosOmissionBindings

end

section

open _root_.Set _root_.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission ErdosBoundaryLoss

theorem actual_first_three_loss_lt : omissionLossTerm 0+omissionLossTerm 1+omissionLossTerm 2<(43:ℝ)/20 := by
  rw [actual_first_loss_eq_one_jb247,actual_second_loss_eq_L2,actual_third_loss_eq_L3]
  linarith [L2_lt,L3_lt]

theorem actual_first_three_partial_sum_lt_jb247_oai : (∑ n ∈ Finset.range 3,omissionLossTerm n)<(43:ℝ)/20 := by
  have h := actual_first_three_loss_lt
  simpa only [Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,zero_add] using h

end ErdosOmissionBindings

end


end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.ErdosOmissionBindings.actual_first_three_partial_sum_lt_jb247_oai := @OAI.Erdos970.ErdosOmissionBindings.actual_first_three_partial_sum_lt_jb247_oai
