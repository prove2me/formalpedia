-- Prove2me | solution 1 for OAI.Erdos970.ErdosOmissionBindings.third_loss_bounded_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:56:25.69719+00:00
-- url     : https://prove2.me/submissions/d44c40b0-dc9d-4622-abca-b06a46063643

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
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
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
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
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Tactic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Definitions.Def_OAIQ247J007
import Theorems.Thm_OAI_Erdos970_ErdosContinuousAnomaly_common_anomaly_exponential_jb247

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
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open _root_.Erdos970.Set _root_.Erdos970.Filter _root_.Erdos970.MeasureTheory
open scoped Topology
namespace ErdosBoundaryIntegral
open ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry

theorem shiftedAnomaly_continuousOn (i : Side) : ContinuousOn (shiftedAnomaly i) (Ici 0) := by
  have hc : Continuous (fun y : ℝ => 2*y+2) := continuous_const.mul continuous_id |>.add continuous_const
  exact (continuousAnomaly_continuousOn i).comp' hc.continuousOn (by
    intro y hy; change 0 ≤ y at hy; change 2 ≤ 2*y+2; linarith)

theorem shifted_anomaly_moment_integrable (i : Side) (n : ℕ) :
    IntegrableOn (fun y : ℝ => y^n*shiftedAnomaly i y) (Ioi 0) := by
  obtain ⟨C,c,_w₀,hC,hc,_hw₀,_hD,hA⟩ := common_anomaly_exponential_jb247
  have hg : IntegrableOn (fun y : ℝ => y^n*Real.exp (-c*y)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n:ℝ)) (p := 1)
      (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) hc
    simpa only [Real.rpow_natCast,Real.rpow_one] using! h
  have hcont : ContinuousOn (fun y : ℝ => y^n*shiftedAnomaly i y) (Ioi 0) :=
    (continuous_id.pow n).continuousOn.mul ((shiftedAnomaly_continuousOn i).mono Ioi_subset_Ici_self)
  apply (hg.const_mul C).mono' (hcont.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hy0 : 0 < y := hy
  have ha : |shiftedAnomaly i y| ≤ C*Real.exp (-c*y) := by
    apply (hA (2*y+2) (by linarith) i).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg hy0.le n)]
  calc
    _ ≤ y^n*(C*Real.exp (-c*y)) := mul_le_mul_of_nonneg_left ha (pow_nonneg hy0.le n)
    _ = C*(y^n*Real.exp (-c*y)) := by ring

end ErdosBoundaryIntegral

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

theorem lower_coefficient_integrable :
    IntegrableOn (fun y : ℝ => (y^2-1)*(lowerReference y-f sieveA (y+1))) (Ioi 1) := by
  have h0 : IntegrableOn (shiftedAnomaly .even) (Ioi 0) := by
    simpa only [pow_zero,one_mul] using shifted_anomaly_moment_integrable .even 0
  have h2 := shifted_anomaly_moment_integrable .even 2
  have hh : IntegrableOn (fun y : ℝ => 2*(y^2*shiftedAnomaly .even y-shiftedAnomaly .even y)) (Ioi 1) volume :=
    ((h2.sub h0).mono_set (by intro y hy; change 0 < y; change 1 < y at hy; linarith)).const_mul (2:ℝ)
  apply hh.congr_fun _ measurableSet_Ioi
  intro y _hy
  dsimp only
  rw [lower_reference_deviation]
  ring

theorem upper_coefficient_integrable :
    IntegrableOn (fun y : ℝ => y^2*(upperReference y-F sieveA (y+1))) (Ioi 0) := by
  have hh : IntegrableOn (fun y : ℝ => 2*(y^2*shiftedAnomaly .odd y)) (Ioi 0) volume :=
    (shifted_anomaly_moment_integrable .odd 2).const_mul (2:ℝ)
  apply hh.congr_fun _ measurableSet_Ioi
  intro y _hy
  dsimp only
  rw [upper_reference_deviation]
  ring

end ErdosBoundaryIntegral

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

theorem gate_add {H G : Profile} (hH : JointContinuous H) (hG : JointContinuous G)
    (i : Side) (r b : ℝ) :
    gate (fun j s t => H j s t+G j s t) i r b=gate H i r b+gate G i r b := by
  simp only [gate,add_div]
  exact intervalIntegral.integral_add
    ((gate_integrand_continuous hH i r).intervalIntegrable 1 _) ((gate_integrand_continuous hG i r).intervalIntegrable 1 _)

theorem gate_mul (c : ℝ) (H : Profile) (i : Side) (r b : ℝ) :
    gate (fun j s t => c*H j s t) i r b=c*gate H i r b := by
  simp only [gate,mul_div_assoc,intervalIntegral.integral_const_mul]

theorem gate_sum (N : ℕ) (H : ℕ → Profile) (hH : ∀ n,JointContinuous (H n))
    (i : Side) (r b : ℝ) :
    gate (fun j s t => ∑ n ∈ Finset.range N,H n j s t) i r b=
      ∑ n ∈ Finset.range N,gate (H n) i r b := by
  simp only [gate,Finset.sum_div]
  exact intervalIntegral.integral_finsetSum (fun n _ => (gate_integrand_continuous (hH n) i r).intervalIntegrable 1 _)

theorem gate_nonnegative {H : Profile} (hH : ∀ i r b,0 ≤ H i r b) (i : Side) (r b : ℝ) :
    0 ≤ gate H i r b := by
  apply intervalIntegral.integral_nonneg_of_forall (upperCutoff_bounds i r b).1
  intro x
  exact div_nonneg (hH i.flip (r-x) x) (zero_le_one.trans (le_max_left 1 x))

theorem gate_odd_small (H : Profile) {r b : ℝ} (hr : r ≤ 4) : gate H .odd r b=0 := by
  rw [gate,upperCutoff_odd_small hr,intervalIntegral.integral_same]

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

theorem gateIterate_depth_zero (H : Profile) (n : ℕ) (i : Side) {r b : ℝ}
    (hr : r ≤ (n:ℝ)+1) : gateIterate (n+2) H i r b=0 := by
  induction n generalizing i r b with
  | zero =>
    cases i with
    | odd => exact gate_odd_small (gateIterate 1 H) (by norm_num at hr <;> linarith)
    | even =>
      change (∫ x in (1:ℝ)..upperCutoff .even r b,gate H .odd (r-x) x/(max 1 x))=0
      calc
        _ = ∫ _x in (1:ℝ)..upperCutoff .even r b,(0:ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_le (upperCutoff_bounds .even r b).1] at hx
          dsimp only
          rw [gate_odd_small H (by norm_num at hr <;> linarith [hx.1]),zero_div]
        _ = 0 := by simp
  | succ n ih =>
    rw [show n+1+2=(n+2)+1 by omega,gateIterate,gate]
    calc
      _ = ∫ _x in (1:ℝ)..upperCutoff i r b,(0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (upperCutoff_bounds i r b).1] at hx
        dsimp only
        have hchild : r-x ≤ (n:ℝ)+1 := by push_cast at hr <;> linarith [hx.1]
        rw [ih i.flip hchild,zero_div]
      _ = 0 := by simp

theorem gateIterate_zero_of_index (H : Profile) {N : ℕ} (hN : 2 ≤ N) (i : Side)
    {r b : ℝ} (hr : r ≤ (N:ℝ)-1) : gateIterate N H i r b=0 := by
  have he : N=(N-2)+2 := by omega
  rw [he]
  apply gateIterate_depth_zero
  have hc : ((N-2:ℕ):ℝ)=(N:ℝ)-2 := by rw [Nat.cast_sub hN]; norm_num
  linarith

theorem gateIterate_add {H G : Profile} (hH : JointContinuous H) (hG : JointContinuous G)
    (n : ℕ) (i : Side) (r b : ℝ) :
    gateIterate n (fun j s t => H j s t+G j s t) i r b=
      gateIterate n H i r b+gateIterate n G i r b := by
  induction n generalizing i r b with
  | zero => rfl
  | succ n ih =>
    have he : gateIterate n (fun j s t => H j s t+G j s t)=
        (fun j s t => gateIterate n H j s t+gateIterate n G j s t) := by funext j s t; exact ih j s t
    rw [gateIterate,he]
    exact gate_add (gateIterate_continuous hH n) (gateIterate_continuous hG n) i r b

theorem gateIterate_gate (n : ℕ) (H : Profile) : gateIterate n (gate H)=gateIterate (n+1) H := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [gateIterate,ih]

theorem finite_forcing_expansion {H F : Profile} (hH : JointContinuous H) (hF : JointContinuous F)
    (heq : ∀ i r b,H i r b=F i r b+gate H i r b) (N : ℕ) (i : Side) (r b : ℝ) :
    H i r b=(∑ n ∈ Finset.range N,gateIterate n F i r b)+gateIterate N H i r b := by
  have hf : H=(fun j s t => F j s t+gate H j s t) := by funext j s t; exact heq j s t
  have hs (n : ℕ) : gateIterate n H i r b=gateIterate n F i r b+gateIterate (n+1) H i r b := by
    calc
      _ = gateIterate n (fun j s t => F j s t+gate H j s t) i r b := congrArg (fun G => gateIterate n G i r b) hf
      _ = gateIterate n F i r b+gateIterate n (gate H) i r b := gateIterate_add hF (gate_continuous hH) n i r b
      _ = _ := by rw [gateIterate_gate]
  induction N with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,zero_add,gateIterate]
  | succ n ih =>
    rw [Finset.sum_range_succ,add_assoc,← hs n]
    exact ih

end ErdosContinuousOmission

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_ContinuousQRecurrence
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

theorem gate_truncatedReference (N : ℕ) (i : Side) (r b : ℝ) :
    gate (truncatedReference N) i r b=
      ∑ n ∈ Finset.range N,(-1:ℝ)^n*boundaryTerm (n+1) i r b := by
  change gate (fun j s t => ∑ n ∈ Finset.range N,(-1:ℝ)^n*boundaryTerm n j s t) i r b=_
  rw [gate_sum N (fun n j s t => (-1:ℝ)^n*boundaryTerm n j s t)
    (fun n j => continuous_const.mul (boundaryTerm_continuous n j))]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [gate_mul]
  rfl

theorem truncatedReference_recurrence (N : ℕ) (i : Side) (r b : ℝ) :
    truncatedReference (N+1) i r b=1-gate (truncatedReference N) i r b := by
  have hfirst : truncatedReference (N+1) i r b=
      (∑ n ∈ Finset.range N,(-1:ℝ)^(n+1)*boundaryTerm (n+1) i r b)+1 := by
    rw [truncatedReference,Finset.sum_range_succ']
    simp only [pow_zero,show boundaryTerm 0 i r b=(1:ℝ) by rfl,one_mul]
  have hs (n : ℕ) : (-1:ℝ)^(n+1)*boundaryTerm (n+1) i r b=
      -((-1:ℝ)^n*boundaryTerm (n+1) i r b) := by rw [pow_succ]; ring
  rw [hfirst]
  simp_rw [hs]
  rw [Finset.sum_neg_distrib,← gate_truncatedReference]
  ring

theorem boundaryReference_recurrence (i : Side) (r b : ℝ) :
    boundaryReference i r b=1-gate boundaryReference i r b := by
  let N := referenceDepth r
  have hN : 2 ≤ N := (referenceDepth_bounds r).1
  have hrN : r ≤ (N:ℝ)-1 := (referenceDepth_bounds r).2
  have hq : boundaryReference i r b=truncatedReference (N+1) i r b :=
    boundaryReference_eq_truncated (N+1) (by omega) i (by push_cast <;> linarith)
  have hchild : gate boundaryReference i r b=gate (truncatedReference N) i r b := by
    unfold gate
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (upperCutoff_bounds i r b).1] at hx
    dsimp only
    rw [boundaryReference_eq_truncated N hN i.flip (by linarith [hx.1] : r-x ≤ (N:ℝ)-1)]
  rw [hq,truncatedReference_recurrence,← hchild]

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

theorem baseline_profile_continuous : JointContinuous (fun _ _ b => survivorBaseline b) :=
  fun _ => survivorBaseline_continuous.comp continuous_snd

theorem gate_survivorBaseline (i : Side) (r b : ℝ) :
    gate (fun _ _ t => survivorBaseline t) i r b=1-(upperCutoff i r b)⁻¹ := by
  let a := upperCutoff i r b
  have ha : 1 ≤ a := (upperCutoff_bounds i r b).1
  have hne : ∀ x ∈ uIcc (1:ℝ) a,x ≠ 0 := by
    intro x hx
    rw [uIcc_of_le ha] at hx
    linarith [hx.1]
  have hc : ContinuousOn (fun x : ℝ => (x^2)⁻¹) (uIcc (1:ℝ) a) :=
    (continuous_id.pow 2).continuousOn.inv₀ (fun x hx => pow_ne_zero 2 (hne x hx))
  have hd : ∀ x ∈ uIcc (1:ℝ) a,HasDerivAt (fun t : ℝ => -t⁻¹) ((x^2)⁻¹) x := by
    intro x hx
    simpa only [neg_neg] using! (hasDerivAt_inv (hne x hx)).neg
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable (μ := volume))
  calc
    gate (fun _ _ t => survivorBaseline t) i r b=∫ x in (1:ℝ)..a,(x^2)⁻¹ := by
      unfold gate
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le ha] at hx
      dsimp only
      have hx2 : x ≤ 2 := hx.2.trans (upperCutoff_bounds i r b).2
      rw [survivorBaseline,baseCutoff_on hx.1 hx2,max_eq_right hx.1]
      ring
    _ = 1-a⁻¹ := by rw [h]; simp only [inv_one] <;> ring

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

section

open _root_.MeasureTheory _root_.Set
namespace ErdosContinuousOmission
open ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

theorem omissionDefect_continuous : JointContinuous omissionDefect := by
  intro i
  cases i with
  | even => exact (baseline_profile_continuous .even).sub (boundaryReference_continuous .even)
  | odd => exact (boundaryReference_continuous .odd).sub (baseline_profile_continuous .odd)

theorem gate_sub {H G : Profile} (hH : JointContinuous H) (hG : JointContinuous G)
    (i : Side) (r b : ℝ) :
    gate (fun j s t => H j s t-G j s t) i r b=gate H i r b-gate G i r b := by
  simp only [gate,sub_div]
  exact intervalIntegral.integral_sub
    ((gate_integrand_continuous hH i r).intervalIntegrable 1 _) ((gate_integrand_continuous hG i r).intervalIntegrable 1 _)

theorem gate_defect_even (r b : ℝ) :
    gate omissionDefect .even r b=gate boundaryReference .even r b-gate (fun _ _ t => survivorBaseline t) .even r b := by
  change gate (fun j s t => boundaryReference j s t-survivorBaseline t) .even r b=_
  exact gate_sub boundaryReference_continuous baseline_profile_continuous .even r b

theorem gate_defect_odd (r b : ℝ) :
    gate omissionDefect .odd r b=gate (fun _ _ t => survivorBaseline t) .odd r b-gate boundaryReference .odd r b := by
  change gate (fun j s t => survivorBaseline t-boundaryReference j s t) .odd r b=_
  exact gate_sub baseline_profile_continuous boundaryReference_continuous .odd r b

theorem actual_defect_forcing (i : Side) (r b : ℝ) :
    omissionDefect i r b=omissionForce i r b+gate omissionDefect i r b := by
  cases i with
  | even =>
    change survivorBaseline b-boundaryReference .even r b=0+gate omissionDefect .even r b
    rw [gate_defect_even,gate_survivorBaseline,boundaryReference_recurrence .even r b]
    change survivorBaseline b-(1-gate boundaryReference .even r b)=0+(gate boundaryReference .even r b-(1-survivorBaseline b))
    ring
  | odd =>
    change boundaryReference .odd r b-survivorBaseline b=
      (upperCutoff .odd r b)⁻¹-survivorBaseline b+gate omissionDefect .odd r b
    rw [gate_defect_odd,gate_survivorBaseline,boundaryReference_recurrence .odd r b]
    ring

theorem actual_finite_omission_expansion (N : ℕ) (hN : 2 ≤ N) (i : Side)
    {r b : ℝ} (hr : r ≤ (N:ℝ)-1) :
    omissionDefect i r b=∑ n ∈ Finset.range N,gateIterate n omissionForce i r b := by
  have h := finite_forcing_expansion omissionDefect_continuous omissionForce_continuous actual_defect_forcing N i r b
  rw [gateIterate_zero_of_index omissionDefect hN i hr,add_zero] at h
  exact h

end ErdosContinuousOmission

end

section

open _root_.Set _root_.Filter
open scoped Topology
namespace ErdosContinuousOmission
open ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

theorem omission_terms_vanish (i : Side) (r b : ℝ) :
    ∀ n : ℕ,referenceDepth r ≤ n → gateIterate n omissionForce i r b=0 := by
  intro n hn
  apply gateIterate_zero_of_index omissionForce ((referenceDepth_bounds r).1.trans hn) i
  have hh : (referenceDepth r:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  exact (referenceDepth_bounds r).2.trans (by linarith)

theorem actual_omission_hasSum (i : Side) (r b : ℝ) :
    HasSum (fun n : ℕ => gateIterate n omissionForce i r b) (omissionDefect i r b) := by
  rw [actual_finite_omission_expansion (referenceDepth r) (referenceDepth_bounds r).1 i (referenceDepth_bounds r).2]
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  apply omission_terms_vanish i r b n
  exact le_of_not_gt (by simpa only [Finset.mem_range] using hn)

end ErdosContinuousOmission

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_DickmanMoments
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set Filter MeasureTheory
open scoped Topology
namespace Erdos970Dependency.StandardBoundary
open NumberTheoryLean.Dickman NumberTheoryLean.DickmanDecay

theorem rho_exp_bound {x : ℝ} (hx : 0 ≤ x) : rho x ≤ Real.exp 2 * Real.exp (-x) := by
  have hle (y : ℝ) (hy : 0 ≤ y) : rho y ≤ 1 := by
    simpa only [rho_initial (by norm_num : (0:ℝ) ≤ 1)] using rho_antitone hy
  by_cases h2 : 2 ≤ x
  · have h := rho_exponential_comparison 2 1 2 x le_rfl
      (fun t ht => hazard_ge_one ht) le_rfl h2
    have h' := mul_le_mul_of_nonneg_right (hle 2 (by norm_num)) (Real.exp_pos (-(1:ℝ)*(x-2))).le
    have he : Real.exp (-(1:ℝ)*(x-2)) = Real.exp 2 * Real.exp (-x) := by
      rw [← Real.exp_add]; congr 1; ring
    simpa only [one_mul, he] using h.trans h'
  · apply (hle x hx).trans
    rw [← Real.exp_add]
    exact Real.one_le_exp (by linarith)

theorem rho_moment_integrable (n : ℕ) :
    IntegrableOn (fun x : ℝ => x^n*rho x) (Ioi 0) := by
  have hg : IntegrableOn (fun x : ℝ => x^n*Real.exp (-x)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n:ℝ)) (p := 1)
      (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) (by norm_num : (0:ℝ)<1)
    simpa only [Real.rpow_natCast,Real.rpow_one,neg_one_mul] using! h
  apply (hg.const_mul (Real.exp 2)).mono'
    (((continuous_id.pow n).mul rho_continuous).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := le_of_lt hx
  change ‖x^n*rho x‖ ≤ Real.exp 2*(x^n*Real.exp (-x))
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg hx0 n),abs_of_nonneg (rho_nonneg x)]
  calc
    _ ≤ x^n*(Real.exp 2*Real.exp (-x)) := mul_le_mul_of_nonneg_left (rho_exp_bound hx0) (pow_nonneg hx0 n)
    _ = Real.exp 2*(x^n*Real.exp (-x)) := by ring

theorem rho_moment_tendsto_zero (n : ℕ) :
    Tendsto (fun x : ℝ => x^n*rho x) atTop (𝓝 0) := by
  have hl := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).const_mul (Real.exp 2)
  simp only [mul_zero] at hl
  apply squeeze_zero' ?_ ?_ hl
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    exact mul_nonneg (pow_nonneg hx n) (rho_nonneg x)
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    calc
      _ ≤ x^n*(Real.exp 2*Real.exp (-x)) := mul_le_mul_of_nonneg_left (rho_exp_bound hx) (pow_nonneg hx n)
      _ = Real.exp 2*(x^n*Real.exp (-x)) := by ring

theorem halfline_shift (a b : ℝ) (g : ℝ → ℝ) :
    ((∫ x in Ioi (a+b),g x) = ∫ x in Ioi a,g (x+b)) ∧
    (IntegrableOn g (Ioi (a+b)) ↔ IntegrableOn (fun x => g (x+b)) (Ioi a)) := by
  have hd : ∀ x ∈ Ioi a, HasDerivWithinAt (fun y : ℝ => y+b) 1 (Ioi a) x :=
    fun x _ => ((hasDerivAt_id x).add_const b).hasDerivWithinAt
  have hinj : InjOn (fun y : ℝ => y+b) (Ioi a) := fun x _ y _ h => by linarith
  have him : (fun y : ℝ => y+b) '' Ioi a = Ioi (a+b) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; change a < y at hy; change a+b < y+b; linarith
    · intro hx; refine ⟨x-b,?_,by ring⟩; change a+b < x at hx; change a < x-b; linarith
  constructor
  · have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj g
    simpa only [him,abs_one,one_smul] using h
  · have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd hinj g
    simpa only [him,abs_one,one_smul] using h

end Erdos970Dependency.StandardBoundary

end

section

open Set Filter MeasureTheory
open scoped Topology
namespace Erdos970Dependency.StandardBoundary
open NumberTheoryLean.Dickman NumberTheoryLean.DickmanDecay

theorem rho_quotient_integral :
    IntegrableOn (fun y : ℝ => rho y/(y+1)) (Ioi 0) ∧
    (∫ y in Ioi 0,rho y/(y+1)) = 1 := by
  have hc : Continuous (fun y : ℝ => rho (y+1)) := rho_continuous.comp (continuous_id.add continuous_const)
  have hd : ∀ y ∈ Ioi (0:ℝ), HasDerivAt (fun x : ℝ => rho (x+1)) (-(rho y/(y+1))) y := by
    intro y hy
    have hh := (rho_hasDerivAt (u := y+1) (by change 0 < y at hy; linarith)).comp y ((hasDerivAt_id y).add_const 1)
    simpa only [add_sub_cancel_right,mul_one,neg_div] using! hh
  have hn : ∀ y ∈ Ioi (0:ℝ), -(rho y/(y+1)) ≤ 0 := by
    intro y hy
    exact neg_nonpos.mpr (div_nonneg (rho_nonneg y) (by change 0 < y at hy; linarith))
  have hl : Tendsto (fun x : ℝ => rho (x+1)) atTop (𝓝 0) :=
    rho_tendsto_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_id)
  have hi := integrableOn_Ioi_deriv_of_nonpos hc.continuousWithinAt hd hn hl
  have he := integral_Ioi_of_hasDerivAt_of_nonpos hc.continuousWithinAt hd hn hl
  refine ⟨integrable_neg_iff.mp hi,?_⟩
  simp only [integral_neg,zero_add,rho_initial le_rfl,zero_sub] at he
  linarith

theorem rho_first_moment :
    (∫ y in Ioi 0,y*rho y) = ∫ y in Ioi 0,rho y := by
  have h0 : IntegrableOn rho (Ioi 0) := by simpa only [pow_zero,one_mul] using rho_moment_integrable 0
  have h1 : IntegrableOn (fun y : ℝ => y*rho y) (Ioi 0) := by simpa only [pow_one] using rho_moment_integrable 1
  have h1tail := h1.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  have hadd : IntegrableOn (fun y : ℝ => (y+1)*rho y) (Ioi 0) := by
    apply (h1.add h0).congr_fun _ measurableSet_Ioi
    intro y _
    change y*rho y+rho y = (y+1)*rho y
    ring
  have hshift := halfline_shift 1 (-1) (fun y : ℝ => (y+1)*rho y)
  simp only [← sub_eq_add_neg,sub_add_cancel,sub_self] at hshift
  have hst : IntegrableOn (fun y : ℝ => y*rho (y-1)) (Ioi 1) := by
    exact hshift.2.mp hadd
  have hseq : (∫ y in Ioi 1,y*rho (y-1)) =
      (∫ y in Ioi 0,y*rho y)+(∫ y in Ioi 0,rho y) := by
    have hp (y : ℝ) : (y+1)*rho y = y*rho y+rho y := by ring
    simpa only [hp,integral_add h1 h0] using hshift.1.symm
  have hder : ∀ y ∈ Ioi (1:ℝ), HasDerivAt (fun x : ℝ => x^2*rho x)
      (2*y*rho y-y*rho (y-1)) y := by
    intro y hy
    have hd := ((hasDerivAt_id y).pow 2).mul (rho_hasDerivAt hy)
    change HasDerivAt (fun x : ℝ => x^2*rho x) (2*y^1*1*rho y+y^2*(-rho (y-1)/y)) y at hd
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
    have hy0 : y ≠ 0 := by change 1 < y at hy; linarith
    field_simp
    ring
  have hint : IntegrableOn (fun y : ℝ => 2*y*rho y-y*rho (y-1)) (Ioi 1) := by
    have hh : IntegrableOn (fun y : ℝ => 2*(y*rho y)-y*rho (y-1)) (Ioi 1) :=
      (h1tail.const_mul 2).sub hst
    apply hh.congr_fun _ measurableSet_Ioi
    intro y _
    dsimp only
    ring
  have hcont : Continuous (fun x : ℝ => x^2*rho x) := (continuous_id.pow 2).mul rho_continuous
  have he := integral_Ioi_of_hasDerivAt_of_tendsto
    hcont.continuousWithinAt hder hint (rho_moment_tendsto_zero 2)
  have hp (y : ℝ) : 2*y*rho y-y*rho (y-1)=2*(y*rho y)-y*rho (y-1) := by ring
  simp only [hp,integral_sub (h1tail.const_mul 2) hst,integral_const_mul,
    one_pow,rho_initial le_rfl,one_mul,zero_sub,hseq] at he
  have hunit : (∫ y : ℝ in 0..1,y*rho y) = (1:ℝ)/2 := by
    calc
      _ = ∫ y : ℝ in 0..1,y := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hy
        change y*rho y = y
        rw [rho_initial hy.2,mul_one]
      _ = _ := by norm_num
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi h1 (by norm_num : (0:ℝ) ≤ 1)
  rw [hunit] at hsplit
  linarith

theorem rho_quadratic_quotient :
    IntegrableOn (fun y : ℝ => y^2*rho y/(y+1)) (Ioi 0) ∧
    (∫ y in Ioi 0,y^2*rho y/(y+1)) = 1 := by
  have h0 : IntegrableOn rho (Ioi 0) := by simpa only [pow_zero,one_mul] using rho_moment_integrable 0
  have h1 : IntegrableOn (fun y : ℝ => y*rho y) (Ioi 0) := by simpa only [pow_one] using rho_moment_integrable 1
  have heq : EqOn (fun y : ℝ => y^2*rho y/(y+1))
      (fun y => y*rho y-rho y+rho y/(y+1)) (Ioi 0) := by
    intro y hy
    have hn : y+1 ≠ 0 := by change 0 < y at hy; linarith
    field_simp
    ring
  refine ⟨((h1.sub h0).add rho_quotient_integral.1).congr_fun (fun y hy => (heq hy).symm) measurableSet_Ioi,?_⟩
  have hs : IntegrableOn (fun y : ℝ => y*rho y-rho y) (Ioi 0) := h1.sub h0
  rw [setIntegral_congr_fun measurableSet_Ioi heq,
    integral_add hs rho_quotient_integral.1,integral_sub h1 h0,
    rho_first_moment,rho_quotient_integral.2]
  ring

end Erdos970Dependency.StandardBoundary

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_StandardDeficitMoments
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
namespace Erdos970Dependency.StandardBoundary
open NumberTheoryLean.LinearSieveFunctions NumberTheoryLean.BuchstabBridge
open NumberTheoryLean.NormalizedDeficits NumberTheoryLean.DeficitFutureIntegrals
open NumberTheoryLean.Dickman

theorem lower_deficit_total :
    IntegrableOn lowerDeficit (Ioi 0) ∧ (∫ t in Ioi 0,lowerDeficit t)=sieveA-1 := by
  have h := upper_future_integral (s := 1) le_rfl
  norm_num only [sub_self,one_mul] at h
  refine ⟨h.1,?_⟩
  rw [← h.2]
  simp only [upperDeficit,F_initial sieveA (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)≤3),div_one]

theorem lower_deficit_shift_tail :
    IntegrableOn (fun y : ℝ => lowerDeficit (y+1)) (Ioi 1) ∧
    (∫ y in Ioi 1,lowerDeficit (y+1))=sieveA-3 := by
  have ht := lower_deficit_total.1.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤2))
  have hs := halfline_shift 1 1 lowerDeficit
  norm_num only [one_add_one_eq_two] at hs
  refine ⟨hs.2.mp ht,?_⟩
  rw [← hs.1]
  have hu : (∫ t : ℝ in 0..2,lowerDeficit t)=2 := by
    calc
      _ = ∫ _t : ℝ in 0..2,(1:ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by norm_num : (0:ℝ)≤2)] at ht
        simp only [lowerDeficit,f_initial sieveA ht.2,sub_zero]
      _ = _ := by norm_num
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi lower_deficit_total.1 (by norm_num : (0:ℝ)≤2)
  rw [hu,lower_deficit_total.2] at hsplit
  linarith

theorem shifted_deficit_moments_integrable :
    IntegrableOn (fun y : ℝ => y^2*lowerDeficit (y+1)) (Ioi 0) ∧
    IntegrableOn (fun y : ℝ => y^2*upperDeficit (y+1)) (Ioi 0) := by
  have bound (b : ℝ → ℝ) (hb : ∀ y, 0 < y → 0 ≤ b (y+1) ∧ b (y+1) ≤ sieveA*rho y/(y+1))
      (hc : ContinuousOn (fun y : ℝ => b (y+1)) (Ioi 0)) :
      IntegrableOn (fun y : ℝ => y^2*b (y+1)) (Ioi 0) := by
    apply (rho_quadratic_quotient.1.const_mul sieveA).mono'
      (((continuous_id.pow 2).continuousOn.mul hc).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hy
    change ‖y^2*b (y+1)‖ ≤ sieveA*(y^2*rho y/(y+1))
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg y) (hb y hy0).1)]
    calc
      _ ≤ y^2*(sieveA*rho y/(y+1)) := mul_le_mul_of_nonneg_left (hb y hy0).2 (sq_nonneg y)
      _ = _ := by ring
  have hbound (y : ℝ) (hy : 0 < y) :
      (0 ≤ lowerDeficit (y+1) ∧ lowerDeficit (y+1) ≤ sieveA*rho y/(y+1)) ∧
      (0 ≤ upperDeficit (y+1) ∧ upperDeficit (y+1) ≤ sieveA*rho y/(y+1)) := by
    have hy1 : 1 ≤ y+1 := by linarith
    have hp := deficits_pos hy1
    have he := deficit_sum (y+1)
    rw [gap_eq_rho hy1,add_sub_cancel_right] at he
    exact ⟨⟨hp.1.le,by linarith⟩,⟨hp.2.le,by linarith⟩⟩
  constructor
  · exact bound lowerDeficit (fun y hy => (hbound y hy).1)
      (lowerDeficit_continuous.comp (continuous_id.add continuous_const)).continuousOn
  · apply bound upperDeficit (fun y hy => (hbound y hy).2)
    apply upperDeficit_continuousOn.comp (continuous_id.add continuous_const).continuousOn
    intro y hy
    change 1 ≤ y+1
    change 0 < y at hy
    linarith

end Erdos970Dependency.StandardBoundary

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_StandardBoundaryCoefficient
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
namespace Erdos970Dependency.StandardBoundary
open NumberTheoryLean.LinearSieveFunctions NumberTheoryLean.BuchstabBridge
open NumberTheoryLean.NormalizedDeficits

theorem standard_coefficient_integrable :
    IntegrableOn (fun y : ℝ => (y^2-1)*(1-f sieveA (y+1))) (Ioi 1) ∧
    IntegrableOn (fun y : ℝ => y^2*(1-F sieveA (y+1))) (Ioi 0) := by
  have h2 := shifted_deficit_moments_integrable.1.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))
  constructor
  · apply (h2.sub lower_deficit_shift_tail.1).congr_fun _ measurableSet_Ioi
    intro y _
    change y^2*lowerDeficit (y+1)-lowerDeficit (y+1) = (y^2-1)*(1-f sieveA (y+1))
    unfold lowerDeficit
    ring
  · apply shifted_deficit_moments_integrable.2.neg.congr_fun _ measurableSet_Ioi
    intro y _
    change -(y^2*upperDeficit (y+1))=y^2*(1-F sieveA (y+1))
    unfold upperDeficit
    ring

end Erdos970Dependency.StandardBoundary

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_ActualLossDensity
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
namespace ErdosContinuousOmission
open ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.LinearSieveFunctions NumberTheoryLean.BuchstabBridge
open ErdosBoundaryIntegral Erdos970Dependency.StandardBoundary

theorem sourceWeight_nonnegative (i : Side) {y : ℝ} (hy : y ∈ sourceDomain i) :
    0 ≤ sourceWeight i y := by
  cases i with
  | even => change 1 < y at hy; change 0 ≤ y^2-1; nlinarith
  | odd => exact sq_nonneg y

theorem omissionDensity_continuous (n : ℕ) (i : Side) : Continuous (omissionDensity n i) := by
  have hw : Continuous (sourceWeight i) := by cases i <;> unfold sourceWeight <;> fun_prop
  have hc : Continuous (fun y : ℝ => gateIterate n omissionForce i (2*y+2) 2) :=
    (gateIterate_continuous omissionForce_continuous n i).comp
    (((continuous_const.mul continuous_id).add continuous_const).prodMk continuous_const)
  exact (continuous_const.mul hw).mul hc

theorem omissionDensity_nonnegative (n : ℕ) (i : Side) {y : ℝ} (hy : y ∈ sourceDomain i) :
    0 ≤ omissionDensity n i y :=
  mul_nonneg (mul_nonneg (by norm_num) (sourceWeight_nonnegative i hy))
    (gateIterate_nonnegative omissionForce_nonnegative n i (2*y+2) 2)

theorem lossDensity_hasSum (i : Side) (y : ℝ) :
    HasSum (fun n : ℕ => omissionDensity n i y) (lossDensity i y) :=
  (actual_omission_hasSum i (2*y+2) 2).mul_left (2*sourceWeight i y)

theorem lossDensity_even (y : ℝ) : lossDensity .even y=
    (y^2-1)*(1-f sieveA (y+1))-(y^2-1)*(lowerReference y-f sieveA (y+1)) := by
  norm_num [lossDensity,sourceWeight,omissionDefect,survivorBaseline,baseCutoff,lowerReference]
  ring

theorem lossDensity_odd (y : ℝ) : lossDensity .odd y=
    y^2*(upperReference y-F sieveA (y+1))-y^2*(1-F sieveA (y+1)) := by
  norm_num [lossDensity,sourceWeight,omissionDefect,survivorBaseline,baseCutoff,upperReference]
  ring

theorem lossDensity_integrable (i : Side) : IntegrableOn (lossDensity i) (sourceDomain i) := by
  cases i with
  | even =>
    have h := standard_coefficient_integrable.1.sub lower_coefficient_integrable
    apply h.congr_fun _ measurableSet_Ioi
    intro y _
    exact (lossDensity_even y).symm
  | odd =>
    have h := upper_coefficient_integrable.sub standard_coefficient_integrable.2
    apply h.congr_fun _ measurableSet_Ioi
    intro y _
    exact (lossDensity_odd y).symm

end ErdosContinuousOmission

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ScalarFreeGate
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
open _root_.Filter _root_.Erdos970.Filter
namespace ErdosContinuousOmission
open ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

theorem omissionDensity_integrable (n : ℕ) (i : Side) :
    IntegrableOn (omissionDensity n i) (sourceDomain i) := by
  have hm : MeasurableSet (sourceDomain i) := by cases i <;> exact measurableSet_Ioi
  apply (lossDensity_integrable i).mono' (omissionDensity_continuous n i).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem hm] with y hy
  rw [Real.norm_eq_abs,abs_of_nonneg (omissionDensity_nonnegative n i hy)]
  have h := (lossDensity_hasSum i y).summable.sum_le_tsum ({n}:Finset ℕ)
    (fun k _ => omissionDensity_nonnegative k i hy)
  simpa only [Finset.sum_singleton,(lossDensity_hasSum i y).tsum_eq] using h

end ErdosContinuousOmission

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

theorem omissionDensity_high_zero (n : ℕ) (i : Side) {y : ℝ} (hy : (n:ℝ)+2 ≤ y) :
    omissionDensity n i y=0 := by
  rw [omissionDensity,iterated_force_high_zero n i (by linarith : 2*(n:ℝ)+6 ≤ 2*y+2),mul_zero]

end ErdosOmissionBindings

end

section

open _root_.Set _root_.Erdos970.Set _root_.MeasureTheory _root_.Erdos970.MeasureTheory
namespace ErdosOmissionBindings
open ErdosContinuousOmission

theorem third_loss_bounded_jb247_oai : omissionLossTerm 2=∫ y : ℝ in 0..4,omissionDensity 2 .odd y := by
  have he : (∫ y in sourceDomain .even,omissionDensity 2 .even y)=0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y _hy
    have h := (omission_wrong_parity_zero 1).1 (2*y+2) 2
    norm_num only [Nat.mul_one] at h
    rw [omissionDensity,h,mul_zero]
  have hz : (∫ y in Ioi 4,omissionDensity 2 .odd y)=0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    exact omissionDensity_high_zero 2 .odd (by norm_num; change 4<y at hy; linarith)
  have h := intervalIntegral.integral_Ioi_sub_Ioi (omissionDensity_integrable 2 .odd) (by norm_num : (0:ℝ)≤4)
  rw [hz,sub_zero] at h
  rw [omissionLossTerm,he,zero_add]
  exact h

end ErdosOmissionBindings

end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.ErdosOmissionBindings.third_loss_bounded_jb247_oai := @OAI.Erdos970.ErdosOmissionBindings.third_loss_bounded_jb247_oai
