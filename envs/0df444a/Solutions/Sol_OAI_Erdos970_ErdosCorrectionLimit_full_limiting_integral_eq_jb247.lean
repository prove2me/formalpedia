-- Prove2me | solution 1 for OAI.Erdos970.ErdosCorrectionLimit.full_limiting_integral_eq_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:55:58.215988+00:00
-- url     : https://prove2.me/submissions/973bdcf7-1995-4395-a589-c4357f31b20c

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
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
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
import Theorems.Thm_OAI_Erdos970_ErdosContinuousAnomaly_common_anomaly_exponential_jb247
import Theorems.Thm_OAI_Erdos970_ErdosCorrectionLimit_fullWeighted_section_radial_jb247

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

theorem upperCutoff_odd_small {r b : ℝ} (hr : r ≤ 4) : upperCutoff .odd r b=1 := by
  apply max_eq_left
  exact (min_le_right _ _).trans (by linarith)

end ErdosContinuousBoundary

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_BoundaryGateSets
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
namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry

theorem boundaryTerm_continuous (n : ℕ) (i : Side) :
    Continuous (fun p : ℝ×ℝ => boundaryTerm n i p.1 p.2) := by
  induction n generalizing i with
  | zero => exact continuous_const
  | succ n ih =>
    let F : (ℝ×ℝ) → ℝ → ℝ := fun p x => boundaryTerm n i.flip (p.1-x) x/(max 1 x)
    have hchild : Continuous (fun q : (ℝ×ℝ)×ℝ => boundaryTerm n i.flip (q.1.1-q.2) q.2) :=
      (ih i.flip).comp ((continuous_fst.fst.sub continuous_snd).prodMk continuous_snd)
    have hden : Continuous (fun q : (ℝ×ℝ)×ℝ => (max 1 q.2)⁻¹) :=
      (continuous_const.max continuous_snd).inv₀ (fun q => ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left 1 q.2)))
    have hF : Continuous F.uncurry := by
      have he : F.uncurry = (fun q : (ℝ×ℝ)×ℝ => boundaryTerm n i.flip (q.1.1-q.2) q.2) *
          (fun q => (max 1 q.2)⁻¹) := by
        funext ⟨p,x⟩
        exact div_eq_mul_inv _ _
      rw [he]
      exact hchild.mul hden
    exact continuous_variable_upper_integral F hF (fun p => upperCutoff i p.1 p.2) (upperCutoff_continuous i)

theorem boundaryTerm_odd_small (n : ℕ) {r b : ℝ} (hr : r ≤ 4) :
    boundaryTerm (n+1) .odd r b=0 := by
  rw [boundaryTerm,upperCutoff_odd_small hr,intervalIntegral.integral_same]

theorem boundaryTerm_depth_zero (n : ℕ) (i : Side) {r b : ℝ} (hr : r ≤ (n:ℝ)+1) :
    boundaryTerm (n+2) i r b=0 := by
  induction n generalizing i r b with
  | zero =>
    cases i with
    | odd => exact boundaryTerm_odd_small 1 (by norm_num at hr <;> linarith)
    | even =>
      rw [boundaryTerm]
      calc
        _ = ∫ _x in (1:ℝ)..upperCutoff .even r b,(0:ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_le (upperCutoff_bounds .even r b).1] at hx
          dsimp only [Side.flip]
          rw [boundaryTerm_odd_small 0 (by norm_num at hr <;> linarith [hx.1]),zero_div]
        _ = 0 := by simp
  | succ n ih =>
    rw [show n+1+2=(n+2)+1 by omega,boundaryTerm]
    calc
      _ = ∫ _x in (1:ℝ)..upperCutoff i r b,(0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (upperCutoff_bounds i r b).1] at hx
        dsimp only
        have hchild : r-x ≤ (n:ℝ)+1 := by push_cast at hr <;> linarith [hx.1]
        rw [ih i.flip hchild,zero_div]
      _ = 0 := by simp

end ErdosContinuousBoundary

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_ContinuousReference
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set _root_.Filter
open scoped Topology
namespace ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry

theorem boundaryTerm_zero_of_index (n : ℕ) (hn : 2 ≤ n) (i : Side) {r b : ℝ}
    (hr : r ≤ (n:ℝ)-1) : boundaryTerm n i r b=0 := by
  have he : n=(n-2)+2 := by omega
  rw [he]
  apply boundaryTerm_depth_zero
  have hc : ((n-2:ℕ):ℝ)=(n:ℝ)-2 := by rw [Nat.cast_sub hn]; norm_num
  linarith

theorem truncatedReference_stable {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M)
    (i : Side) {r b : ℝ} (hr : r ≤ (N:ℝ)-1) :
    truncatedReference N i r b=truncatedReference M i r b := by
  unfold truncatedReference
  apply Finset.sum_subset (Finset.range_mono hNM)
  intro n _hnM hnN
  have hNn : N ≤ n := le_of_not_gt (by simpa only [Finset.mem_range] using hnN)
  have hrn : r ≤ (n:ℝ)-1 := hr.trans (sub_le_sub_right (by exact_mod_cast hNn) 1)
  rw [boundaryTerm_zero_of_index n (hN.trans hNn) i hrn,mul_zero]

theorem referenceDepth_bounds (r : ℝ) : 2 ≤ referenceDepth r ∧ r ≤ (referenceDepth r : ℝ)-1 := by
  have h := Nat.le_ceil (max r 0)
  have hr : r ≤ max r 0 := le_max_left _ _
  unfold referenceDepth
  constructor
  · omega
  · push_cast
    linarith

theorem boundaryReference_eq_truncated (N : ℕ) (hN : 2 ≤ N) (i : Side)
    {r b : ℝ} (hr : r ≤ (N:ℝ)-1) : boundaryReference i r b=truncatedReference N i r b := by
  unfold boundaryReference
  rcases le_total (referenceDepth r) N with h | h
  · exact truncatedReference_stable (referenceDepth_bounds r).1 h i (referenceDepth_bounds r).2
  · exact (truncatedReference_stable hN h i hr).symm

theorem truncatedReference_continuous (N : ℕ) (i : Side) :
    Continuous (fun p : ℝ×ℝ => truncatedReference N i p.1 p.2) := by
  apply continuous_finsetSum
  intro n _hn
  exact continuous_const.mul (boundaryTerm_continuous n i)

theorem boundaryReference_continuous (i : Side) :
    Continuous (fun p : ℝ×ℝ => boundaryReference i p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let N := referenceDepth (p.1+1)
  have hc := (truncatedReference_continuous N i).continuousAt (x:=p)
  apply hc.congr_of_eventuallyEq
  have he : ∀ᶠ q : ℝ×ℝ in 𝓝 p,q.1 < p.1+1 :=
    continuous_fst.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by linarith : p.1 < p.1+1))
  filter_upwards [he] with q hq
  exact boundaryReference_eq_truncated N (referenceDepth_bounds (p.1+1)).1 i
    (hq.le.trans (referenceDepth_bounds (p.1+1)).2)

end ErdosContinuousBoundary

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_WeightedAnomalyConvergence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set _root_.Filter
open _root_.Erdos970.MeasureTheory _root_.Erdos970.Set _root_.Erdos970.Filter
open scoped Topology
namespace ErdosContinuousAnomaly
open ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceAdmission
open NumberTheoryLean.ReferenceBenchmarkDecay NumberTheoryLean.BoundaryAnomaly
open NumberTheoryLean.LinearSieveFunctions NumberTheoryLean.BuchstabBridge

theorem continuousAnomaly_continuousOn (i : Side) : ContinuousOn (continuousAnomaly i) (Ici 2) := by
  intro r hr
  have hq : ContinuousAt (fun x : ℝ => boundaryReference i x 2) r :=
    ((boundaryReference_continuous i).comp (continuous_id.prodMk continuous_const)).continuousAt
  have hb : ContinuousAt (fun x : ℝ => benchmark i (x/2)) r := by
    cases i with
    | even => exact (f_continuous sieveA).continuousAt.comp (continuousAt_id.div_const 2)
    | odd =>
      have hx : r/2 ≠ 0 := by have h := hr; change 2 ≤ r at h; linarith
      have hg : ContinuousAt (fun x : ℝ => x/2) r := continuousAt_id.div_const 2
      have hF : ContinuousAt (F sieveA) ((fun x : ℝ => x/2) r) := F_continuousAt sieveA hx
      simpa only [Function.comp_def,benchmark] using hF.comp (f := fun x : ℝ => x/2) hg
  exact (hq.sub (continuousAt_const.mul hb)).continuousWithinAt

end ErdosContinuousAnomaly

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_BoundaryRadialCoefficient
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
namespace ErdosBoundaryIntegral
open ErdosContinuousBoundary ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceBenchmarkDecay
open NumberTheoryLean.LinearSieveFunctions NumberTheoryLean.BuchstabBridge

theorem lower_reference_deviation (y : ℝ) :
    lowerReference y-f sieveA (y+1)=2*shiftedAnomaly .even y := by
  unfold lowerReference shiftedAnomaly continuousAnomaly
  have he : (2*y+2)/2=y+1 := by ring
  rw [he,benchmark]
  ring

theorem upper_reference_deviation (y : ℝ) :
    upperReference y-F sieveA (y+1)=2*shiftedAnomaly .odd y := by
  unfold upperReference shiftedAnomaly continuousAnomaly
  have he : (2*y+2)/2=y+1 := by ring
  rw [he,benchmark]
  ring

theorem signedCoefficient_eq_anomaly :
    signedCoefficientI =
      2*(∫ y in Ioi 1,(y^2-1)*shiftedAnomaly .even y)-
        2*(∫ y in Ioi 0,y^2*shiftedAnomaly .odd y) := by
  unfold signedCoefficientI
  simp_rw [lower_reference_deviation,upper_reference_deviation]
  have he (y : ℝ) : (y^2-1)*(2*shiftedAnomaly .even y)=2*((y^2-1)*shiftedAnomaly .even y) := by ring
  have ho (y : ℝ) : y^2*(2*shiftedAnomaly .odd y)=2*(y^2*shiftedAnomaly .odd y) := by ring
  simp_rw [he,ho,integral_const_mul]

end ErdosBoundaryIntegral

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosBoundaryIntegral
open ErdosContinuousAnomaly

theorem boundary_affine_integral (a : ℝ) (g : ℝ → ℝ) :
    (∫ r in Ioi (2*a+2),g r) = ∫ y in Ioi a,2*g (2*y+2) := by
  have hd : ∀ x ∈ Ioi a,HasDerivWithinAt (fun y : ℝ => 2*y+2) 2 (Ioi a) x := by
    intro x _
    convert! (((hasDerivAt_id x).const_mul 2).add_const 2).hasDerivWithinAt using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hinj : InjOn (fun y : ℝ => 2*y+2) (Ioi a) := by
    intro x _ y _ h
    linarith
  have him : (fun y : ℝ => 2*y+2) '' Ioi a=Ioi (2*a+2) := by
    ext r
    constructor
    · rintro ⟨y,hy,rfl⟩
      change a < y at hy
      change 2*a+2 < 2*y+2
      linarith
    · intro hr
      refine ⟨(r-2)/2,?_,by ring⟩
      change a < (r-2)/2
      change 2*a+2 < r at hr
      linarith
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj g
  rw [him] at h
  simpa only [abs_of_pos (by norm_num : (0:ℝ)<2),smul_eq_mul] using! h

theorem radial_coefficient_eq_twice_I :
    ((∫ r in Ioi 4,r*(r/2-2)*continuousAnomaly .even r)-
      ∫ r in Ioi 2,(r^2/2-2*r+2)*continuousAnomaly .odd r)=2*signedCoefficientI := by
  have he := boundary_affine_integral 1 (fun r => r*(r/2-2)*continuousAnomaly .even r)
  have ho := boundary_affine_integral 0 (fun r => (r^2/2-2*r+2)*continuousAnomaly .odd r)
  norm_num only [mul_one,mul_zero,zero_add] at he ho
  rw [he,ho,signedCoefficient_eq_anomaly]
  have he' (y : ℝ) : 2*((2*y+2)*((2*y+2)/2-2)*continuousAnomaly .even (2*y+2))=
      4*((y^2-1)*shiftedAnomaly .even y) := by unfold shiftedAnomaly; ring
  have ho' (y : ℝ) : 2*(((2*y+2)^2/2-2*(2*y+2)+2)*continuousAnomaly .odd (2*y+2))=
      4*(y^2*shiftedAnomaly .odd y) := by unfold shiftedAnomaly; ring
  simp_rw [he',ho',integral_const_mul]
  ring

end ErdosBoundaryIntegral

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

theorem evenDensity_nonneg (s : ℝ) : 0 ≤ evenDensity s := by
  by_cases hs : 2 ≤ s
  · rw [evenDensity, indicator_of_mem (show s ∈ Ici (2 : ℝ) from hs)]
    exact (phiEven_pos (by linarith)).le
  · rw [evenDensity, indicator_of_notMem (show s ∉ Ici (2 : ℝ) from hs)]

theorem oddDensity_nonneg (s : ℝ) : 0 ≤ oddDensity s := by
  by_cases hs : 1 ≤ s
  · rw [oddDensity, indicator_of_mem (show s ∈ Ici (1 : ℝ) from hs)]
    exact mul_nonneg (oddFactor_bounds hs).1 (phiOdd_pos s).le
  · rw [oddDensity, indicator_of_notMem (show s ∉ Ici (1 : ℝ) from hs)]

end Erdos970Dependency.InvariantDensities

end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Erdos970Dependency.InvariantFiniteness
open NumberTheoryLean NumberTheoryLean.DerivativeWeights NumberTheoryLean.TransitionKernels
open Erdos970Dependency.InvariantDensities

theorem integrableOn_Ici_of_exp_tail {f : ℝ → ℝ} {a : ℝ}
    (hm : Measurable f) (hc : ContinuousOn f (Ici a)) (hn : ∀ s, a ≤ s → 0 ≤ f s)
    {C T : ℝ} (hT : a ≤ T) (hb : ∀ s, T ≤ s → f s ≤ C * Real.exp (-s)) :
    IntegrableOn f (Ici a) := by
  have hcompact : IntegrableOn f (Icc a T) :=
    (hc.mono Icc_subset_Ici_self).integrableOn_Icc
  have htail : IntegrableOn f (Ioi T) := by
    apply ((integrableOn_exp_neg_Ioi T).const_mul C).mono_nonneg hm.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact hn s (hT.trans hs.le)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact hb s hs.le
  rw [← Icc_union_Ioi_eq_Ici hT]
  exact hcompact.union htail

theorem weights_exp_majorant : ∃ D U : ℝ, 0 < D ∧ 2 ≤ U ∧ ∀ s : ℝ, U ≤ s →
    phiEven s ≤ D * Real.exp (-s) ∧ phiOdd s ≤ D * Real.exp (-s) := by
  obtain ⟨c, C, hc, hC, hphi⟩ := WeightDickmanComparison.weights_dickman_bounds
  obtain ⟨R, hR, T, hT, hrho⟩ := DickmanDecay.rho_exponential_majorant 1
  refine ⟨C * R * Real.exp 2, T + 2, by positivity, by linarith, ?_⟩
  intro s hs
  have hs2 : 2 ≤ s := by linarith
  have hr := hrho (s - 2) (by linarith)
  have heq : Real.exp (-(s - 2)) = Real.exp 2 * Real.exp (-s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [neg_one_mul, heq] at hr
  have hbound : C * Dickman.rho (s - 2) ≤ (C * R * Real.exp 2) * Real.exp (-s) := by
    have h := mul_le_mul_of_nonneg_left hr hC.le
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  exact ⟨(hphi s hs2).1.2.trans hbound, (hphi s hs2).2.2.trans hbound⟩

theorem phiEven_integrableOn : IntegrableOn phiEven (Ici (2 : ℝ)) := by
  obtain ⟨D, U, _, hU, hb⟩ := weights_exp_majorant
  apply integrableOn_Ici_of_exp_tail phiEven_measurable ?_
    (fun s hs ↦ (phiEven_pos (by linarith)).le) hU (fun s hs ↦ (hb s hs).1)
  intro s hs
  exact (phiEven_continuousAt (by change (2 : ℝ) ≤ s at hs; linarith)).continuousWithinAt

theorem phiOdd_integrableOn : IntegrableOn phiOdd (Ici (1 : ℝ)) := by
  obtain ⟨D, U, _, hU, hb⟩ := weights_exp_majorant
  exact integrableOn_Ici_of_exp_tail phiOdd_continuous.measurable phiOdd_continuous.continuousOn
    (fun s _ ↦ (phiOdd_pos s).le) (show (1 : ℝ) ≤ U by linarith) (fun s hs ↦ (hb s hs).2)

theorem evenDensity_integrable : Integrable InvariantDensities.evenDensity :=
  (integrable_indicator_iff measurableSet_Ici).mpr phiEven_integrableOn

theorem oddDensity_integrable : Integrable InvariantDensities.oddDensity := by
  apply (integrable_indicator_iff measurableSet_Ici).mpr
  apply phiOdd_integrableOn.mono_nonneg
    (oddFactor_measurable.mul phiOdd_continuous.measurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    exact mul_nonneg (oddFactor_bounds hs).1 (phiOdd_pos s).le
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    have h := mul_le_mul_of_nonneg_right (oddFactor_bounds hs).2 (phiOdd_pos s).le
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    simp only [one_mul]

instance evenMeasure_isFiniteMeasure : IsFiniteMeasure evenMeasure := by
  constructor
  rw [evenMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal evenDensity_integrable
      (Filter.Eventually.of_forall InvariantDensities.evenDensity_nonneg)]
  exact ENNReal.ofReal_lt_top

instance oddMeasure_isFiniteMeasure : IsFiniteMeasure oddMeasure := by
  constructor
  rw [oddMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal oddDensity_integrable
      (Filter.Eventually.of_forall InvariantDensities.oddDensity_nonneg)]
  exact ENNReal.ofReal_lt_top

end Erdos970Dependency.InvariantFiniteness

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_StateKernelInvariance
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedPairKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.RegenerativeOddOccupation.ratioVisits_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.CycleOccupation.pairSampling_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedCostKernel_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedCostProcess.pairedDraws_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PairedHitting.pairedOdd_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

instance evenStateMeasure_isFiniteMeasure : IsFiniteMeasure evenStateMeasure := by unfold evenStateMeasure; infer_instance
instance oddStateMeasure_isFiniteMeasure : IsFiniteMeasure oddStateMeasure := by unfold oddStateMeasure; infer_instance

instance stateMeasure_isFiniteMeasure : IsFiniteMeasure stateMeasure := by unfold stateMeasure; infer_instance

end Erdos970Dependency.StateKernelInvariance

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

end Erdos970Dependency.DeficitIntegralValues

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

theorem evenMajor_integrable : Integrable evenMajor :=
  (integrable_indicator_iff measurableSet_Ici).mpr even_majorant_integral.1

theorem evenCost_integrable : Integrable evenCost := by
  apply evenMajor_integrable.mono' (evenDensity_measurable.mul cost_measurable).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun s ↦ by
    change ‖evenCost s‖ ≤ evenMajor s
    rw [Real.norm_of_nonneg (evenCost_nonneg s)]
    exact evenCost_le_major s)

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

end Erdos970Dependency.InvariantCostBound

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_EvenInverseBands
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

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

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_ActualCouplingUpdates
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ActualCouplingUpdates

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualCouplingSupport ContinuousKilledBins
open LowStateHorizon ArrivalKernelGeometry RegeneratingInverseBands
open PrimeTiltGeometry KernelDensityBridge PairedCostGrouping

variable {w ell S : ℝ} {start : Node}

theorem side_set_measurable (i : Side) : MeasurableSet {s : State | stateSide s = i} := by
  cases i <;> apply measurableSet_sum_iff.mpr <;> simp [stateSide]

end NumberTheoryLean.ActualCouplingUpdates

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeOccupationDensity
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeOccupationDensity

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures InvariantInverseWeights
open Erdos970Dependency.StateKernelInvariance Erdos970Dependency.InvariantCostBound

theorem density_nonneg (ell : ℝ) (x : ℝ×State) : 0 ≤ density ell x := by
  unfold density
  split_ifs
  · exact div_nonneg (sq_nonneg _) (mul_pos (stateWeight_pos _) costMass_pos).le
  · exact le_rfl

theorem density_measurable (ell : ℝ) : Measurable (density ell) := by
  have he := Real.measurable_exp.comp (measurable_fst : Measurable (Prod.fst : ℝ×State → ℝ))
  have hs := stateRatio_measurable.comp (measurable_snd : Measurable (Prod.snd : ℝ×State → State))
  exact Measurable.ite (measurableSet_lt hs (he.div_const ell))
    ((he.pow_const 2).div ((stateWeight_measurable.comp measurable_snd).mul_const costMass)) measurable_const

end NumberTheoryLean.PrimeOccupationDensity

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_CompactAnomalyTest
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set
namespace ErdosCorrectionOccupation
open ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PositiveGapMajorant

theorem extendedSignedAnomaly_continuous (i : Side) : Continuous (extendedSignedAnomaly i) := by
  have h := (continuousAnomaly_continuousOn i).comp_continuous
    (continuous_const.max continuous_id) (fun r => le_max_left 2 r)
  exact continuous_const.mul h

end ErdosCorrectionOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CorrectionEnvelope
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology ENNReal
namespace ErdosCorrectionLimit
open ErdosCorrectionOccupation ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.FinitePathMeasures
open NumberTheoryLean.OccupationDensityIntegral
open NumberTheoryLean.ActualCouplingUpdates

theorem fullAnomalyTest_continuous (i : Side) : Continuous (fullAnomalyTest i) :=
  (extendedSignedAnomaly_continuous i).comp continuous_fst

theorem rawTest_measurable {H : Side → ℝ×ℝ → ℝ} (hH : ∀ i, Continuous (H i)) :
    Measurable (rawTest H) := by
  have hp : Measurable (fun x : ℝ×State => (Real.exp x.1,stateRatio x.2)) :=
    (Real.measurable_exp.comp measurable_fst).prodMk (stateRatio_measurable.comp measurable_snd)
  have hs : MeasurableSet {x : ℝ×State | stateSide x.2=.even} :=
    measurable_snd (side_set_measurable .even)
  have he : rawTest H = fun x => if stateSide x.2=.even then H .even (Real.exp x.1,stateRatio x.2)
      else H .odd (Real.exp x.1,stateRatio x.2) := by
    funext x
    rcases x with ⟨u,s⟩
    cases s <;> rfl
  rw [he]
  exact Measurable.ite hs ((hH .even).measurable.comp hp) ((hH .odd).measurable.comp hp)

theorem full_anomaly_exponential :
    ∃ C c : ℝ,0 < C ∧ 0 < c ∧ ∀ i r,|extendedSignedAnomaly i r| ≤ C*Real.exp (-c*r) := by
  obtain ⟨C,c,_w,hC,hc,_hw,_hd,ha⟩ := common_anomaly_exponential_jb247
  refine ⟨C,c,hC,hc,?_⟩
  intro i r
  have hsign : |sideSign i|=1 := by cases i <;> norm_num [sideSign]
  rw [extendedSignedAnomaly,abs_mul,hsign,one_mul]
  apply (ha (max 2 r) (le_max_left _ _) i).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  nlinarith [le_max_right (2:ℝ) r]

theorem exp_gap_moment_integrable (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun u : ℝ => (Real.exp u)^(n+1)*Real.exp (-c*Real.exp u)) := by
  have hg : IntegrableOn (fun r : ℝ => r^n*Real.exp (-c*r)) (Ioi 0) := by
    have hh := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n:ℝ)) (p := 1)
      (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) hc
    simpa only [Real.rpow_natCast,Real.rpow_one] using! hh
  have hd : ∀ u ∈ (univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp u) univ u :=
    fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt
  have him : Real.exp '' (univ : Set ℝ)=Ioi 0 := by rw [image_univ,Real.range_exp]
  have hh := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hd
    Real.exp_injective.injOn (fun r : ℝ => r^n*Real.exp (-c*r))).mp (by rwa [him])
  have hh' : Integrable (fun u : ℝ => Real.exp u*((Real.exp u)^n*Real.exp (-c*Real.exp u))) := by
    simpa only [abs_of_pos (Real.exp_pos _),smul_eq_mul,integrableOn_univ] using! hh
  simpa only [pow_succ',mul_assoc] using! hh'

end ErdosCorrectionLimit

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_CorrectionWeightedIntegral
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology ENNReal
namespace ErdosCorrectionLimit
open ErdosCorrectionOccupation
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.InvariantInverseWeights
open NumberTheoryLean.PrimeOccupationDensity NumberTheoryLean.OccupationDensityIntegral
open Erdos970Dependency.StateKernelInvariance Erdos970Dependency.InvariantCostBound

theorem densityEnvelope_nonneg (c : ℝ) (x : ℝ×State) : 0 ≤ densityEnvelope c x :=
  mul_nonneg (density_nonneg 2 x) (Real.exp_pos _).le

theorem densityEnvelope_measurable (c : ℝ) : Measurable (densityEnvelope c) :=
  (density_measurable 2).mul (Real.measurable_exp.comp
    (measurable_const.mul (Real.measurable_exp.comp measurable_fst)))

theorem densityEnvelope_factor (c u : ℝ) (s : State) :
    ENNReal.ofReal (densityEnvelope c (u,s))=
      ENNReal.ofReal ((Real.exp u)^2*Real.exp (-c*Real.exp u)/costMass)*
        inverseWeightCutoff (Real.exp u/2) s := by
  classical
  by_cases h : stateRatio s < Real.exp u/2
  · rw [inverseWeightCutoff,indicator_of_mem (show s ∈ {s | stateRatio s < Real.exp u/2} from h)]
    unfold densityEnvelope density
    rw [ite_eq_left h]
    have he : (Real.exp u)^2/(stateWeight s*costMass)*Real.exp (-c*Real.exp u)=
        ((Real.exp u)^2*Real.exp (-c*Real.exp u)/costMass)/stateWeight s := by ring
    rw [he,ENNReal.ofReal_div_of_pos (stateWeight_pos s),div_eq_mul_inv]
  · rw [inverseWeightCutoff,indicator_of_notMem (show s ∉ {s | stateRatio s < Real.exp u/2} from h),mul_zero]
    simp only [densityEnvelope,density,ite_eq_right h,zero_mul,ENNReal.ofReal_zero]

theorem densityEnvelope_section_le (c u : ℝ) :
    (∫⁻ s : State,ENNReal.ofReal (densityEnvelope c (u,s)) ∂stateMeasure) ≤
      ENNReal.ofReal ((Real.exp u)^3*Real.exp (-c*Real.exp u)/costMass) := by
  simp_rw [densityEnvelope_factor]
  rw [lintegral_const_mul _ (inverseWeightCutoff_measurable _)]
  have hb := inverseWeightCutoff_mass_le (L := Real.exp u/2) (by positivity)
  have hc : 0 ≤ (Real.exp u)^2*Real.exp (-c*Real.exp u)/costMass :=
    div_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) costMass_pos.le
  calc
    _ ≤ ENNReal.ofReal ((Real.exp u)^2*Real.exp (-c*Real.exp u)/costMass)*
        ENNReal.ofReal (2*(Real.exp u/2)) := mul_le_mul le_rfl hb (by positivity) (by positivity)
    _ = _ := by rw [← ENNReal.ofReal_mul hc]; congr 1; ring

theorem densityEnvelope_integrable {c : ℝ} (hc : 0 < c) :
    Integrable (densityEnvelope c) baseMeasure := by
  have hgn : ∀ u : ℝ,0 ≤ (Real.exp u)^3*Real.exp (-c*Real.exp u)/costMass :=
    fun u => div_nonneg (mul_nonneg (pow_nonneg (Real.exp_pos _).le _) (Real.exp_pos _).le) costMass_pos.le
  have hgi : Integrable (fun u : ℝ => (Real.exp u)^3*Real.exp (-c*Real.exp u)/costMass) := by
    simpa only [Nat.reduceAdd] using (exp_gap_moment_integrable 2 hc).div_const costMass
  refine ⟨(densityEnvelope_measurable c).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (densityEnvelope_nonneg c))).mpr
  have hm : Measurable (fun x => ENNReal.ofReal (densityEnvelope c x)) :=
    ENNReal.measurable_ofReal.comp (densityEnvelope_measurable c)
  rw [baseMeasure,lintegral_prod _ hm.aemeasurable]
  exact (lintegral_mono (densityEnvelope_section_le c)).trans_lt
    ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall hgn)).mp hgi.hasFiniteIntegral)

theorem fullRaw_integrable : Integrable (rawTest fullAnomalyTest) (limitingMeasure 2) := by
  obtain ⟨C,c,hC,hc,ha⟩ := full_anomaly_exponential
  have hm := rawTest_measurable fullAnomalyTest_continuous
  have hD := ENNReal.measurable_ofReal.comp (density_measurable 2)
  have ht : ∀ᵐ x ∂baseMeasure,ENNReal.ofReal (density 2 x)<∞ :=
    Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  apply (integrable_withDensity_iff_integrable_smul' hD ht).mpr
  have hi : Integrable (fun x => density 2 x*rawTest fullAnomalyTest x) baseMeasure := by
    apply ((densityEnvelope_integrable hc).const_mul C).mono'
      ((density_measurable 2).mul hm).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    change ‖density 2 x*rawTest fullAnomalyTest x‖ ≤ C*densityEnvelope c x
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (density_nonneg 2 x)]
    have hb := mul_le_mul_of_nonneg_left (ha (stateSide x.2) (Real.exp x.1)) (density_nonneg 2 x)
    change density 2 x*|extendedSignedAnomaly (stateSide x.2) (Real.exp x.1)| ≤ _
    unfold densityEnvelope
    nlinarith
  apply hi.congr
  filter_upwards with x
  change density 2 x*rawTest fullAnomalyTest x = (ENNReal.ofReal (density 2 x)).toReal • rawTest fullAnomalyTest x
  rw [ENNReal.toReal_ofReal (density_nonneg 2 x),smul_eq_mul]

end ErdosCorrectionLimit

end

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology ENNReal
namespace ErdosCorrectionLimit
open ErdosCorrectionOccupation
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PrimeOccupationDensity
open NumberTheoryLean.OccupationDensityIntegral
open Erdos970Dependency.StateKernelInvariance

theorem fullWeighted_integrable : Integrable fullWeighted baseMeasure := by
  have hD : Measurable (fun x => ENNReal.ofReal (density 2 x)) :=
    ENNReal.measurable_ofReal.comp (density_measurable 2)
  have ht : ∀ᵐ x ∂baseMeasure,ENNReal.ofReal (density 2 x)<∞ :=
    Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have hi := (integrable_withDensity_iff_integrable_smul' hD ht).mp fullRaw_integrable
  apply hi.congr
  filter_upwards with x
  change (ENNReal.ofReal (density 2 x)).toReal • rawTest fullAnomalyTest x=fullWeighted x
  rw [ENNReal.toReal_ofReal (density_nonneg 2 x),smul_eq_mul]
  rfl

theorem full_limiting_integral_fubini :
    (∫ x,rawTest fullAnomalyTest x ∂limitingMeasure 2)=
      ∫ u : ℝ,∫ s : State,fullWeighted (u,s) ∂stateMeasure := by
  have hD : Measurable (fun x => ENNReal.ofReal (density 2 x)) :=
    ENNReal.measurable_ofReal.comp (density_measurable 2)
  have ht : ∀ᵐ x ∂baseMeasure,ENNReal.ofReal (density 2 x)<∞ :=
    Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  rw [limitingMeasure,integral_withDensity_eq_integral_toReal_smul hD ht]
  have he : (fun x => (ENNReal.ofReal (density 2 x)).toReal • rawTest fullAnomalyTest x)=fullWeighted := by
    funext x
    rw [ENNReal.toReal_ofReal (density_nonneg 2 x),smul_eq_mul]
    rfl
  rw [he]
  exact integral_prod fullWeighted fullWeighted_integrable

end ErdosCorrectionLimit

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_ContinuousCorrectionLimit
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology ENNReal
namespace ErdosCorrectionLimit
open ErdosContinuousAnomaly ErdosBoundaryIntegral
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PrimeOccupationDensity
open NumberTheoryLean.OccupationDensityIntegral
open Erdos970Dependency.InvariantCostBound

theorem anomaly_moment_integrable (i : Side) (n : ℕ) :
    IntegrableOn (fun r : ℝ => r^n*continuousAnomaly i r) (Ioi 2) := by
  obtain ⟨C,c,_w,hC,hc,_hw,_hd,ha⟩ := common_anomaly_exponential_jb247
  have hg : IntegrableOn (fun r : ℝ => r^n*Real.exp (-c*r)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n:ℝ)) (p := 1)
      (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) hc
    simpa only [Real.rpow_natCast,Real.rpow_one] using! h
  have hm : ContinuousOn (fun r : ℝ => r^n*continuousAnomaly i r) (Ioi 2) :=
    (continuous_id.pow n).continuousOn.mul ((continuousAnomaly_continuousOn i).mono Ioi_subset_Ici_self)
  apply ((hg.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤2))).const_mul C).mono'
    (hm.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr2 : 2 < r := hr
  change ‖r^n*continuousAnomaly i r‖ ≤ C*(r^n*Real.exp (-c*r))
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg (by linarith) n)]
  have hb := mul_le_mul_of_nonneg_left (ha r hr2.le i) (pow_nonneg (by linarith : 0 ≤ r) n)
  nlinarith

theorem exp_cutoff_integral {a : ℝ} (ha : 0 < a) (g : ℝ → ℝ) :
    ((∫ u : ℝ,if a < Real.exp u then Real.exp u*g (Real.exp u) else 0)=∫ r in Ioi a,g r) ∧
    (Integrable (fun u : ℝ => if a < Real.exp u then Real.exp u*g (Real.exp u) else 0) ↔
      IntegrableOn g (Ioi a)) := by
  have him : Real.exp '' Ioi (Real.log a)=Ioi a := by
    ext r
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact (Real.log_lt_iff_lt_exp ha).mp hu
    · intro hr
      have hra : a < r := hr
      have hr0 : 0 < r := ha.trans hra
      exact ⟨Real.log r,Real.log_lt_log ha hra,Real.exp_log hr0⟩
  have hd : ∀ u ∈ Ioi (Real.log a), HasDerivWithinAt Real.exp (Real.exp u) (Ioi (Real.log a)) u :=
    fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt
  have hf : (fun u : ℝ => if a < Real.exp u then Real.exp u*g (Real.exp u) else 0)=
      (Ioi (Real.log a)).indicator (fun u => Real.exp u*g (Real.exp u)) := by
    funext u
    simp only [indicator_apply,mem_Ioi,Real.log_lt_iff_lt_exp ha]
  constructor
  · rw [hf,integral_indicator measurableSet_Ioi]
    have hh := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd Real.exp_injective.injOn g
    simpa only [him,abs_of_pos (Real.exp_pos _),smul_eq_mul] using! hh.symm
  · rw [hf,integrable_indicator_iff measurableSet_Ioi]
    have hh := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd Real.exp_injective.injOn g
    simpa only [him,abs_of_pos (Real.exp_pos _),smul_eq_mul] using! hh.symm

theorem radial_parts_integrable : IntegrableOn evenRadial (Ioi 4) ∧ IntegrableOn oddRadial (Ioi 2) := by
  have h1 (i : Side) : IntegrableOn (fun r : ℝ => r*continuousAnomaly i r) (Ioi 2) := by
    simpa only [pow_one] using anomaly_moment_integrable i 1
  have h0 (i : Side) : IntegrableOn (continuousAnomaly i) (Ioi 2) := by
    simpa only [pow_zero,one_mul] using anomaly_moment_integrable i 0
  constructor
  · have hh : IntegrableOn (fun r : ℝ => (r^2*continuousAnomaly .even r)/2-2*(r*continuousAnomaly .even r)) (Ioi 2) :=
      ((anomaly_moment_integrable .even 2).div_const 2).sub ((h1 .even).const_mul 2)
    apply (hh.mono_set (Ioi_subset_Ioi (by norm_num : (2:ℝ)≤4))).congr_fun _ measurableSet_Ioi
    intro r _
    dsimp only [evenRadial]
    ring
  · have hh : IntegrableOn (fun r : ℝ => ((r^2*continuousAnomaly .odd r)/2-2*(r*continuousAnomaly .odd r))+2*continuousAnomaly .odd r) (Ioi 2) :=
      (((anomaly_moment_integrable .odd 2).div_const 2).sub ((h1 .odd).const_mul 2)).add ((h0 .odd).const_mul 2)
    apply hh.congr_fun _ measurableSet_Ioi
    intro r _
    dsimp only [oddRadial]
    ring

theorem full_limiting_integral_eq_jb247_oai :
    (∫ x,rawTest fullAnomalyTest x ∂limitingMeasure 2)=2*signedCoefficientI/costMass := by
  have he := exp_cutoff_integral (by norm_num : (0:ℝ)<4) evenRadial
  have ho := exp_cutoff_integral (by norm_num : (0:ℝ)<2) oddRadial
  have hie := he.2.mpr radial_parts_integrable.1
  have hio := ho.2.mpr radial_parts_integrable.2
  rw [full_limiting_integral_fubini]
  simp_rw [fullWeighted_section_radial_jb247]
  have hfun : (fun u : ℝ => Real.exp u/costMass*radialNumerator (Real.exp u))=
      (fun u => ((if 4 < Real.exp u then Real.exp u*evenRadial (Real.exp u) else 0)-
        (if 2 < Real.exp u then Real.exp u*oddRadial (Real.exp u) else 0))/costMass) := by
    funext u
    unfold radialNumerator evenRadial oddRadial
    split_ifs <;> ring
  rw [hfun,integral_div,integral_sub hie hio,he.1,ho.1]
  have hh : (∫ r in Ioi 4,evenRadial r)-(∫ r in Ioi 2,oddRadial r)=2*signedCoefficientI :=
    radial_coefficient_eq_twice_I
  rw [hh]

end ErdosCorrectionLimit

end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.ErdosCorrectionLimit.full_limiting_integral_eq_jb247_oai := @OAI.Erdos970.ErdosCorrectionLimit.full_limiting_integral_eq_jb247_oai
