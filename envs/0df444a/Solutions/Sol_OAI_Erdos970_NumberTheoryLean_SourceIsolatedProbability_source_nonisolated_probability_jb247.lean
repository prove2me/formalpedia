-- Prove2me | solution 1 for OAI.Erdos970.NumberTheoryLean.SourceIsolatedProbability.source_nonisolated_probability_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:07:48.472295+00:00
-- url     : https://prove2.me/submissions/0d05fa44-c8ae-40bc-b241-42ba161c9778

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.GroupTheory.Index
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.CircleAverage
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
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Order.SuccPred.IntervalSucc
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
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UrysohnsLemma
import Definitions.Def_OAIQ247J010
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_RegenerationBandBounds_regeneration_uniform_band_jb247
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_SourceCouplingRate_source_coupling_rate_jb247

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FiniteHistorySupport
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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



namespace NumberTheoryLean.FiniteHistoryTransport

open Set MeasureTheory ProbabilityTheory MeasurableEquiv
open scoped ENNReal

theorem extend_measurable {X : Type*} [MeasurableSpace X] (n : ℕ) :
    Measurable (fun p : Hist X n × X => extend n p.1 p.2) := by
  exact (measurable_IicProdIoc (X := fun _ => X) (m := n) (n := n+1)).comp
    (measurable_fst.prodMk ((piSingleton (X := fun _ => X) n).measurable.comp measurable_snd))

theorem mapHist_extend {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (n : ℕ) (h : Hist X n) (x : X) :
    mapHist f (n+1) (extend n h x) = extend n (mapHist f n h) (f x) := by
  ext k
  simp only [mapHist, extend, IicProdIoc_def, piSingleton,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
  split_ifs <;> simp

theorem lintegral_pathKernel_succ {X : Type*} [MeasurableSpace X]
    (K : Kernel X X) [IsSFiniteKernel K] (n : ℕ) (h₀ : Hist X 0)
    {F : Hist X (n+1) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ h, F h ∂pathKernel K (n+1) h₀ =
      ∫⁻ h, ∫⁻ x, F (extend n h x) ∂K (last n h) ∂pathKernel K n h₀ := by
  rw [pathKernel, Kernel.partialTraj_succ_of_le (Nat.zero_le n),
    Kernel.lintegral_map _ (measurable_IicProdIoc (X := fun _ => X) (m := n) (n := n+1)) _ hF,
    Kernel.lintegral_comp _ _ _ (by exact hF.comp measurable_IicProdIoc)]
  congr 1
  funext h
  rw [Kernel.lintegral_id_prod (by exact hF.comp measurable_IicProdIoc),
    Kernel.lintegral_map _ (piSingleton (X := fun _ => X) n).measurable _
      (by exact (hF.comp measurable_IicProdIoc).comp measurable_prodMk_left)]
  rw [pastKernel, Kernel.comap_apply]
  rfl

end NumberTheoryLean.FiniteHistoryTransport



namespace NumberTheoryLean.FiniteHistoryTransport

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (K : Kernel X X) (L : Kernel Y Y) [IsSFiniteKernel K] [IsSFiniteKernel L]
variable {f : X → Y} (hf : Measurable f)
variable (hstep : ∀ x, (K x).map f = L (f x))

include hf hstep

theorem lintegral_mapHist (n : ℕ) (h₀ : Hist X 0)
    {F : Hist Y n → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ h, F (mapHist f n h) ∂pathKernel K n h₀ =
      ∫⁻ h, F h ∂pathKernel L n (mapHist f 0 h₀) := by
  induction n with
  | zero =>
    simp only [pathKernel, Kernel.partialTraj_self, Kernel.id_apply]
    rw [lintegral_dirac' _ (by exact hF.comp (mapHist_measurable hf 0)), lintegral_dirac' _ hF]
  | succ n ih =>
    rw [lintegral_pathKernel_succ K n h₀ (by exact hF.comp (mapHist_measurable hf (n+1))),
      lintegral_pathKernel_succ L n (mapHist f 0 h₀) hF]
    have hG : Measurable (fun h : Hist Y n =>
        ∫⁻ y, F (extend n h y) ∂L (last n h)) := by
      have hm : Measurable (Function.uncurry (fun h : Hist Y n => fun y : Y =>
          F (extend n h y))) := hF.comp (extend_measurable n)
      simpa only [pastKernel, Kernel.comap_apply] using
        (hm.lintegral_kernel_prod_right (κ := pastKernel L n))
    calc
      _ = ∫⁻ h, ∫⁻ y, F (extend n (mapHist f n h) y)
          ∂L (last n (mapHist f n h)) ∂pathKernel K n h₀ := by
        apply lintegral_congr
        intro h
        simp only [mapHist_extend]
        change (∫⁻ x, F (extend n (mapHist f n h) (f x)) ∂K (last n h)) =
          ∫⁻ y, F (extend n (mapHist f n h) y) ∂L (f (last n h))
        rw [← hstep (last n h), lintegral_map]
        · exact hF.comp ((extend_measurable n).comp measurable_prodMk_left)
        · exact hf
      _ = _ := ih hG

theorem pathKernel_mapHist (n : ℕ) :
    (pathKernel K n).map (mapHist f n) =
      (pathKernel L n).comap (mapHist f 0) (mapHist_measurable hf 0) := by
  apply Kernel.ext_fun
  intro h₀ F hF
  rw [Kernel.lintegral_map _ (mapHist_measurable hf n) _ hF, Kernel.comap_apply]
  exact lintegral_mapHist K L hf hstep n h₀ hF

theorem pathMeasure_mapHist (n : ℕ) (h₀ : Hist X 0) :
    (pathKernel K n h₀).map (mapHist f n) =
      pathKernel L n (mapHist f 0 h₀) := by
  rw [← Kernel.map_apply _ (mapHist_measurable hf n), pathKernel_mapHist K L hf hstep,
    Kernel.comap_apply]

end NumberTheoryLean.FiniteHistoryTransport



namespace NumberTheoryLean.FiniteHistoryTransport

open Set MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

theorem extend_last (n : ℕ) (h : Hist X n) (x : X) : last (n+1) (extend n h x) = x := by
  simp [last, extend, IicProdIoc_def, MeasurableEquiv.piSingleton]

variable (K : Kernel X X) [IsSFiniteKernel K]

theorem lintegral_endpoint (n : ℕ) (h₀ : Hist X 0) {F : X → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ h, F (last n h) ∂pathKernel K n h₀ = ∫⁻ x, F x ∂(K^n) (last 0 h₀) := by
  induction n generalizing F with
  | zero =>
    change (∫⁻ h, F (last 0 h) ∂Kernel.id h₀) = ∫⁻ x, F x ∂Kernel.id (last 0 h₀)
    simp only [Kernel.id_apply]
    rw [lintegral_dirac' _ (by exact hF.comp (measurable_pi_apply _)), lintegral_dirac' _ hF]
  | succ n ih =>
    rw [lintegral_pathKernel_succ K n h₀ (by exact hF.comp (measurable_pi_apply _))]
    simp only [extend_last]
    have hp : K^(n+1) = K ∘ₖ (K^n) := by
      simpa only [Nat.add_comm, pow_one] using Kernel.pow_add K 1 n
    rw [hp, Kernel.lintegral_comp _ _ _ hF]
    exact ih (hF.lintegral_kernel (κ := K))

theorem pathKernel_endpoint (n : ℕ) :
    (pathKernel K n).map (last n) = (K^n).comap (last 0) (last_measurable 0) := by
  apply Kernel.ext_fun
  intro h₀ F hF
  rw [Kernel.lintegral_map _ (last_measurable n) _ hF, Kernel.comap_apply]
  exact lintegral_endpoint K n h₀ hF

theorem pathMeasure_endpoint (n : ℕ) (h₀ : Hist X 0) :
    (pathKernel K n h₀).map (last n) = (K^n) (last 0 h₀) := by
  rw [← Kernel.map_apply _ (last_measurable n), pathKernel_endpoint, Kernel.comap_apply]

theorem pathMeasure_coordinate [IsMarkovKernel K] (n k : ℕ) (hk : k ≤ n) (h₀ : Hist X 0) :
    (pathKernel K n h₀).map (fun h => h ⟨k, by simpa using hk⟩) =
      (K^k) (last 0 h₀) := by
  have hrestriction : (pathKernel K n h₀).map (frestrictLe₂ (π := fun _ => X) hk) = pathKernel K k h₀ :=
    Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ => X) (κ := pastKernel K) h₀ hk
  calc
    _ = ((pathKernel K n h₀).map (frestrictLe₂ (π := fun _ => X) hk)).map (last k) := by
      rw [Measure.map_map (last_measurable k) (measurable_frestrictLe₂ hk)]
      rfl
    _ = _ := by rw [hrestriction, pathMeasure_endpoint]

end NumberTheoryLean.FiniteHistoryTransport



namespace NumberTheoryLean.FiniteHistoryTransport

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

theorem ae_pathKernel_succ (K : Kernel X X) [IsSFiniteKernel K]
    (n : ℕ) (h₀ : Hist X 0) {P : Hist X (n+1) → Prop}
    (hP : MeasurableSet {h | P h})
    (hstep : ∀ᵐ h ∂pathKernel K n h₀, ∀ᵐ x ∂K (last n h), P (extend n h x)) :
    ∀ᵐ h ∂pathKernel K (n+1) h₀, P h := by
  classical
  rw [ae_iff]
  change pathKernel K (n+1) h₀ ({h | P h}ᶜ) = 0
  rw [← lintegral_indicator_one hP.compl,
    lintegral_pathKernel_succ K n h₀ (by exact measurable_const.indicator hP.compl)]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hstep] with h hh
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hh] with x hx
  simp [hx]

theorem extend_previous (n : ℕ) (h : Hist X n) (x : X) (k : Finset.Iic n) :
    extend n h x ⟨k,by exact Finset.mem_Iic.mpr ((Finset.mem_Iic.mp k.2).trans n.le_succ)⟩ = h k := by
  simp [extend,IicProdIoc_def,show (k:ℕ) ≤ n from Finset.mem_Iic.mp k.2]

end NumberTheoryLean.FiniteHistoryTransport


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_WeightIntegrals
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

instance evenStateMeasure_isFiniteMeasure : IsFiniteMeasure evenStateMeasure := by unfold evenStateMeasure; infer_instance
instance oddStateMeasure_isFiniteMeasure : IsFiniteMeasure oddStateMeasure := by unfold oddStateMeasure; infer_instance

instance stateMeasure_isFiniteMeasure : IsFiniteMeasure stateMeasure := by unfold stateMeasure; infer_instance

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

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
namespace ErdosHighRatioBandTail
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.TransitionKernels
open NumberTheoryLean.RegenerationBandBounds NumberTheoryLean.BandShiftTransport
open NumberTheoryLean.CostPrefixTransport NumberTheoryLean.EvenBandBounds
open Erdos970Dependency.StateKernelInvariance

theorem highStates_measurable (T : ℝ) : MeasurableSet (highStates T) :=
  measurableSet_le measurable_const stateRatio_measurable

theorem highReward_measurable (T : ℝ) : Measurable (highReward T) :=
  measurable_const.indicator (highStates_measurable T)

theorem highBand_measurable (T v h : ℝ) : MeasurableSet (highBand T v h) :=
  (measurableSet_le measurable_const (stateRatio_measurable.comp measurable_fst)).inter
    (measurable_snd measurableSet_Icc)

theorem highReward_integral (μ : Measure State) (T : ℝ) :
    (∫⁻ s, highReward T s ∂μ) = μ (highStates T) := by
  rw [highReward, lintegral_indicator (highStates_measurable T)]
  simp

theorem highBand_integral (μ : Measure CostState) (T v h : ℝ) :
    (∫⁻ z, stateBandReward (highReward T) v h z ∂μ) = μ (highBand T v h) := by
  have he : stateBandReward (highReward T) v h =
      (highBand T v h).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext z
    by_cases ht : T ≤ stateRatio z.1 <;> by_cases hc : z.2 ∈ Icc v (v+h) <;>
      simp_all [stateBandReward, highReward, highStates, highBand, Set.indicator_apply]
  rw [he, lintegral_indicator (highBand_measurable T v h)]
  simp

theorem stateMeasure_tail_tendsto :
    Tendsto (fun T : ℝ => stateMeasure (highStates T)) atTop (𝓝 0) := by
  have hm : Antitone highStates := by
    intro T U hTU s hs
    exact hTU.trans hs
  have he : (⋂ T : ℝ, highStates T) = ∅ := by
    ext s
    simp only [mem_iInter, highStates, Set.mem_ofPred_eq, mem_empty_iff_false, iff_false]
    intro hs
    have h := hs (stateRatio s+1)
    linarith
  have ht := tendsto_measure_iInter_atTop
    (fun T => (highStates_measurable T).nullMeasurableSet (μ := stateMeasure)) hm
    (show ∃ T : ℝ, stateMeasure (highStates T) ≠ ∞ from ⟨0, measure_ne_top _ _⟩)
  simpa only [he, measure_empty, Function.comp_def] using ht

theorem later_band_tail_bound (h : ℝ) : ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ T v : ℝ, ∀ s : EvenState, 199/100 ≤ s.1 → s.1 ≤ 23/10 →
      prefixOccupation 2 (.inl s,0) (highBand T v h) ≤ C*stateMeasure (highStates T) := by
  obtain ⟨C,hC,hb⟩ := even_uniform_band h
  refine ⟨C,hC,?_⟩
  intro T v s hsL hsU
  have ht := hb (highReward T) (highReward_measurable T) v s hsL hsU
  simpa only [highBand_integral, highReward_integral] using ht

end ErdosHighRatioBandTail

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
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.PrimeChainHorizon

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain LowStateHorizon

variable {w ell S : ℝ} {start : Node}

theorem stage_measurable (n : ℕ) : MeasurableSet {z : ChainState w ell S start | stage n z} := trivial

theorem next_stage (n : ℕ) (z : ChainState w ell S start) (hz : stage n z) :
    ∀ᵐ y ∂chain w ell S start z, stage (n+1) y := by
  classical
  cases z with
  | none =>
    rw [chain_none]
    exact (ae_dirac_iff (stage_measurable (n+1))).mpr trivial
  | some h =>
    have hlen : h.primes.length = n := hz
    apply ae_iff.mpr
    simp [chain_some, completedLaw, liveLaw, stage, History.append_primes, hlen]

theorem pathLaw_stage (n : ℕ) : ∀ᵐ z ∂pathLaw w ell S start n, stage n z := by
  induction n with
  | zero =>
    change ∀ᵐ z ∂Measure.dirac (some (History.empty : History w ell S start)), stage 0 z
    exact (ae_dirac_iff (stage_measurable 0)).mpr rfl
  | succ n ih =>
    have hp : (chain w ell S start)^(n+1) = (chain w ell S start) ∘ₖ ((chain w ell S start)^n) := pow_succ' _ _
    change ∀ᵐ z ∂((chain w ell S start)^(n+1)) (some History.empty), stage (n+1) z
    rw [hp]
    apply Kernel.ae_comp_of_ae_ae (stage_measurable (n+1))
    filter_upwards [ih] with z hz
    exact next_stage n z hz

end NumberTheoryLean.PrimeChainHorizon



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_CemeteryHistoryLaw
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
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

namespace NumberTheoryLean.CemeteryHistoryMap

open Set MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal
open FiniteHistoryTransport CemeteryKernel

variable {X : Type*} [MeasurableSpace X]

theorem live_measurable : MeasurableSet {z : Space X | live z} :=
  measurableSet_sum_iff.mpr ⟨MeasurableSet.univ,MeasurableSet.empty⟩

theorem killStep_measurable {E : Set X} (hE : MeasurableSet E) :
    Measurable (fun p : Space X × X => killStep E p.1 p.2) := by
  classical
  exact Measurable.ite ((measurable_fst live_measurable).inter (measurable_snd hE))
    (measurable_inl.comp measurable_snd) measurable_const

omit [MeasurableSpace X] in
theorem killStep_eq_or_dead (E : Set X) (z : Space X) (x : X) :
    killStep E z x = Sum.inl x ∨ killStep E z x = dead := by
  classical
  unfold killStep
  split_ifs <;> simp

theorem extend_restrict (n : ℕ) (h : Hist X n) (x : X) :
    frestrictLe₂ (π := fun _ => X) n.le_succ (extend n h x) = h := by
  ext k
  simp [frestrictLe₂, FiniteHistoryTransport.extend, IicProdIoc_def,
    show (k:ℕ) ≤ n from Finset.mem_Iic.mp k.2]

theorem killHist_measurable {E : Set X} (hE : MeasurableSet E) (n : ℕ) :
    Measurable (killHist E n) := by
  induction n with
  | zero => exact mapHist_measurable (measurable_inl (α := X) (β := Unit)) 0
  | succ n ih =>
    have hp := ih.comp (measurable_frestrictLe₂ (X := fun _ => X) n.le_succ)
    exact (extend_measurable n).comp (hp.prodMk ((killStep_measurable hE).comp
      (((last_measurable n).comp hp).prodMk (last_measurable (n+1)))))

theorem killHist_extend (E : Set X) (n : ℕ) (h : Hist X n) (x : X) :
    killHist E (n+1) (extend n h x) =
      extend n (killHist E n h) (killStep E (last n (killHist E n h)) x) := by
  simp only [killHist, extend_restrict, extend_last]

theorem killHist_last (E : Set X) (n : ℕ) (h : Hist X n) :
    last n (killHist E n h) = Sum.inl (last n h) ∨ last n (killHist E n h) = dead := by
  cases n with
  | zero => exact Or.inl rfl
  | succ n =>
    simp only [killHist, extend_last]
    exact killStep_eq_or_dead _ _ _

end NumberTheoryLean.CemeteryHistoryMap

end

section

namespace NumberTheoryLean.CemeteryHistoryMap

open Set MeasureTheory ProbabilityTheory Preorder
open FiniteHistoryTransport CemeteryKernel

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem aliveThrough_succ (E : Set X) (n : ℕ) (h : Hist X (n+1)) :
    aliveThrough E (n+1) h ↔
      aliveThrough E n (frestrictLe₂ (π := fun _ => X) n.le_succ h) ∧ last (n+1) h ∈ E := by
  constructor
  · intro ha
    refine ⟨?_,ha ⟨n+1,by simp⟩ (Nat.succ_pos n)⟩
    intro j hj
    exact ha ⟨j,by have := Finset.mem_Iic.mp j.2; simp; omega⟩ hj
  · rintro ⟨ha,hx⟩ ⟨j,hj⟩ hpos
    have hj' := Finset.mem_Iic.mp hj
    by_cases hle : j ≤ n
    · exact ha ⟨j,by simpa using hle⟩ hpos
    · have heq : j = n+1 := by omega
      subst j
      exact hx

theorem killHist_restrict (E : Set X) (n k : ℕ) (hk : k ≤ n) (h : Hist X n) :
    frestrictLe₂ (π := fun _ => Space X) hk (killHist E n h) =
      killHist E k (frestrictLe₂ (π := fun _ => X) hk h) := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst k
    rfl
  | succ n ih =>
    by_cases hkn : k ≤ n
    · calc
        _ = frestrictLe₂ (π := fun _ => Space X) hkn
            (frestrictLe₂ (π := fun _ => Space X) n.le_succ (killHist E (n+1) h)) := rfl
        _ = frestrictLe₂ (π := fun _ => Space X) hkn
            (killHist E n (frestrictLe₂ (π := fun _ => X) n.le_succ h)) := by
          rw [killHist,extend_restrict]
        _ = _ := ih k hkn _
    · have heq : k = n+1 := by omega
      subst k
      rfl

theorem killHist_last_exact (E : Set X) (n : ℕ) (h : Hist X n) :
    last n (killHist E n h) = if aliveThrough E n h then Sum.inl (last n h) else dead := by
  classical
  induction n with
  | zero =>
    have ha : aliveThrough E 0 h := by
      intro j hj
      have := Finset.mem_Iic.mp j.2
      omega
    simp only [ite_eq_left ha]
    rfl
  | succ n ih =>
    rw [killHist,extend_last,ih]
    simp only [aliveThrough_succ]
    by_cases hp : aliveThrough E n (frestrictLe₂ (π := fun _ => X) n.le_succ h) <;>
      by_cases hx : last (n+1) h ∈ E <;> simp [hp,hx,killStep,live,dead]

theorem killHist_coordinate (E : Set X) (n k : ℕ) (hk : k ≤ n) (h : Hist X n) :
    (killHist E n h) ⟨k,by simpa using hk⟩ =
      if aliveThrough E k (frestrictLe₂ (π := fun _ => X) hk h)
      then Sum.inl (h ⟨k,by simpa using hk⟩) else dead := by
  classical
  have heq := congrArg (last k) (killHist_restrict E n k hk h)
  rw [killHist_last_exact] at heq
  exact heq

end NumberTheoryLean.CemeteryHistoryMap

end

section

namespace NumberTheoryLean.CemeteryHistoryMap

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open CemeteryKernel FiniteHistoryTransport

variable {X : Type*} [MeasurableSpace X]
variable (K : Kernel X X) [IsMarkovKernel K] {E : Set X} (hE : MeasurableSet E)

theorem killStep_live_map (x : X) :
    (K x).map (killStep E (Sum.inl x)) = complete (K.restrict hE) (Sum.inl x) := by
  classical
  have hf : Measurable (killStep E (Sum.inl x)) :=
    (killStep_measurable hE).comp measurable_prodMk_left
  have hA : ((K x).restrict E).map (killStep E (Sum.inl x)) = ((K x).restrict E).map Sum.inl := by
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem hE] with y hy
    simp [killStep,live,hy]
  have hB : ((K x).restrict Eᶜ).map (killStep E (Sum.inl x)) =
      ((K x).restrict Eᶜ).map (fun _ => (dead : Space X)) := by
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem hE.compl] with y hy
    change y ∉ E at hy
    simp [killStep,live,hy]
  calc
    _ = (((K x).restrict E)+((K x).restrict Eᶜ)).map (killStep E (Sum.inl x)) := by
      rw [Measure.restrict_add_restrict_compl hE]
    _ = ((K x).restrict E).map Sum.inl + (1-K x E) • Measure.dirac dead := by
      rw [Measure.map_add _ _ hf, hA, hB, Measure.map_const, Measure.restrict_apply_univ,
        measure_compl hE (measure_ne_top _ _), measure_univ]
    _ = _ := by
      rw [complete_live,liveRow_apply,Kernel.restrict_apply,Measure.restrict_apply_univ]

theorem killStep_dead_map (x : X) :
    (K x).map (killStep E dead) = complete (K.restrict hE) dead := by
  classical
  have hf : killStep E (dead : Space X) = fun _ => dead := by
    funext y
    simp [killStep,live,dead]
  rw [hf,Measure.map_const,measure_univ,one_smul,complete_dead]

theorem killHist_step_map (n : ℕ) (h : Hist X n) :
    (K (last n h)).map (killStep E (last n (killHist E n h))) =
      complete (K.restrict hE) (last n (killHist E n h)) := by
  rcases killHist_last E n h with hl | hd
  · rw [hl]
    exact killStep_live_map K hE _
  · rw [hd]
    exact killStep_dead_map K hE _

instance restricted_complete_markov : IsMarkovKernel (complete (K.restrict hE)) := by
  apply complete_isMarkov
  intro x
  rw [Kernel.restrict_apply,Measure.restrict_apply_univ]
  exact (measure_mono (subset_univ E)).trans_eq (measure_univ (μ := K x))

end NumberTheoryLean.CemeteryHistoryMap

end

section

namespace NumberTheoryLean.CemeteryHistoryMap

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open CemeteryKernel FiniteHistoryTransport

variable {X : Type*} [MeasurableSpace X]
variable (K : Kernel X X) [IsMarkovKernel K] {E : Set X} (hE : MeasurableSet E)

theorem lintegral_killHist (n : ℕ) (h₀ : Hist X 0)
    {F : Hist (Space X) n → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ h, F (killHist E n h) ∂pathKernel K n h₀ =
      ∫⁻ h, F h ∂pathKernel (complete (K.restrict hE)) n (mapHist Sum.inl 0 h₀) := by
  induction n with
  | zero =>
    simp only [pathKernel,Kernel.partialTraj_self,Kernel.id_apply]
    rw [lintegral_dirac' _ (by exact hF.comp (killHist_measurable hE 0)),lintegral_dirac' _ hF]
    rfl
  | succ n ih =>
    rw [lintegral_pathKernel_succ K n h₀ (by exact hF.comp (killHist_measurable hE (n+1))),
      lintegral_pathKernel_succ (complete (K.restrict hE)) n (mapHist Sum.inl 0 h₀) hF]
    have hG : Measurable (fun h : Hist (Space X) n =>
        ∫⁻ y, F (FiniteHistoryTransport.extend n h y) ∂complete (K.restrict hE) (last n h)) := by
      have hm : Measurable (Function.uncurry (fun h : Hist (Space X) n => fun y : Space X =>
          F (FiniteHistoryTransport.extend n h y))) := hF.comp (extend_measurable n)
      simpa only [pastKernel,Kernel.comap_apply] using
        (hm.lintegral_kernel_prod_right (κ := pastKernel (complete (K.restrict hE)) n))
    calc
      _ = ∫⁻ h, ∫⁻ y, F (FiniteHistoryTransport.extend n (killHist E n h) y)
          ∂complete (K.restrict hE) (last n (killHist E n h)) ∂pathKernel K n h₀ := by
        apply lintegral_congr
        intro h
        simp only [killHist_extend]
        rw [← killHist_step_map K hE n h,lintegral_map]
        · exact hF.comp ((extend_measurable n).comp measurable_prodMk_left)
        · exact (killStep_measurable hE).comp measurable_prodMk_left
      _ = _ := ih hG

theorem pathMeasure_killHist (n : ℕ) (h₀ : Hist X 0) :
    (pathKernel K n h₀).map (killHist E n) =
      pathKernel (complete (K.restrict hE)) n (mapHist Sum.inl 0 h₀) := by
  have hk : (pathKernel K n).map (killHist E n) =
      (pathKernel (complete (K.restrict hE)) n).comap (mapHist Sum.inl 0)
        (mapHist_measurable measurable_inl 0) := by
    apply Kernel.ext_fun
    intro h F hF
    rw [Kernel.lintegral_map _ (killHist_measurable hE n) _ hF,Kernel.comap_apply]
    exact lintegral_killHist K hE n h hF
  rw [← Kernel.map_apply _ (killHist_measurable hE n),hk,Kernel.comap_apply]

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeBinRepresentatives
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeBinRepresentatives

open ErdosInversePrimeBin ErdosPrimeInputs.HarmonicPrimeMeasure
open PrimeHistories RepresentativeAdmission

theorem bin_exponent_bounds {w R xi : ℝ} (hw : 1 < w) (hR : 0 < R) (hxi : 0 ≤ xi)
    {p : ℕ} (hp : p ∈ primeBin R xi) :
    leftExponent w R < primeExponent w p ∧ primeExponent w p ≤ rightExponent w R xi := by
  obtain ⟨hprime,hlo,hhi⟩ := (mem_primeBin hR.le hxi p).mp hp
  have hp0 : (0:ℝ) < p := by exact_mod_cast hprime.pos
  exact ⟨div_lt_div_of_pos_right (Real.log_lt_log hR hlo) (Real.log_pos hw),
    div_le_div_of_nonneg_right (Real.log_le_log hp0 hhi) (Real.log_pos hw).le⟩

theorem bin_exponent_width {w R xi : ℝ} (hR : 0 < R) (hxi : 0 ≤ xi) :
    rightExponent w R xi-leftExponent w R = Real.log (1+xi)/Real.log w := by
  rw [rightExponent,leftExponent,Real.log_mul (by positivity : (1+xi:ℝ) ≠ 0) hR.ne']
  ring

theorem representative_error {w R xi : ℝ} (hw : 1 < w) (hR : 0 < R) (hxi : 0 ≤ xi)
    {p : ℕ} (hp : p ∈ primeBin R xi) :
    0 ≤ rightExponent w R xi-primeExponent w p ∧
      rightExponent w R xi-primeExponent w p ≤ xi/Real.log w := by
  have h := bin_exponent_bounds hw hR hxi hp
  have hlog : Real.log (1+xi) ≤ xi := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+xi)
    linarith
  refine ⟨sub_nonneg.mpr h.2,?_⟩
  calc
    _ ≤ rightExponent w R xi-leftExponent w R := by linarith [h.1]
    _ = Real.log (1+xi)/Real.log w := bin_exponent_width hR hxi
    _ ≤ _ := div_le_div_of_nonneg_right hlog (Real.log_pos hw).le

end NumberTheoryLean.PrimeBinRepresentatives

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CrossingBandGeometry
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ContinuousKilledBins.continuousChain_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.LogarithmicBinScale


theorem logWidth_pos {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    0 < logWidth w z xi :=
  div_pos (span_log_pos hw hwz) (by exact_mod_cast binCount_pos hw hwz hxi)

theorem count_mul_logWidth {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    (binCount w z xi:ℝ)*logWidth w z xi = Real.log (z/w) := by
  have hn : (binCount w z xi:ℝ) ≠ 0 := by exact_mod_cast (binCount_pos hw hwz hxi).ne'
  unfold logWidth
  field_simp [hn]

theorem logWidth_le {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    logWidth w z xi ≤ Real.log (1+xi) := by
  have hlog : 0 < Real.log (1+xi) := Real.log_pos (by linarith)
  have hc := Nat.le_ceil (Real.log (z/w)/Real.log (1+xi))
  have hm := (div_le_iff₀ hlog).mp hc
  change Real.log (z/w) ≤ (binCount w z xi:ℝ)*Real.log (1+xi) at hm
  apply (div_le_iff₀ (by exact_mod_cast binCount_pos hw hwz hxi : (0:ℝ) < binCount w z xi)).mpr
  exact (by nlinarith : Real.log (z/w) ≤ Real.log (1+xi)*(binCount w z xi:ℝ))

theorem effectiveWidth_pos {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    0 < effectiveWidth w z xi := by
  exact sub_pos.mpr (Real.one_lt_exp_iff.mpr (logWidth_pos hw hwz hxi))

theorem effectiveWidth_le {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi) :
    effectiveWidth w z xi ≤ xi := by
  have he := Real.exp_le_exp.mpr (logWidth_le hw hwz hxi)
  rw [Real.exp_log (by linarith : 0 < 1+xi)] at he
  exact sub_le_iff_le_add.mpr (by linarith)

end NumberTheoryLean.LogarithmicBinScale



namespace NumberTheoryLean.LogarithmicBinEndpoints

open LogarithmicBinScale PrimeBinRepresentatives ErdosInversePrimeBin

theorem upper_endpoint (w z xi : ℝ) (i : Fin (binCount w z xi)) :
    upper w z xi i = endpoint w z xi (i.1+1) := by
  simp only [upper,width,lower,effectiveWidth,endpoint,Nat.cast_add,Nat.cast_one,add_mul,one_mul,Real.exp_add]
  ring

theorem endpoint_pos {w z xi : ℝ} (hw : 0 < w) (k : ℕ) : 0 < endpoint w z xi k := by
  exact mul_pos hw (Real.exp_pos _)

end NumberTheoryLean.LogarithmicBinEndpoints



namespace NumberTheoryLean.LogarithmicBinLabels

open LogarithmicBinScale LogarithmicBinEndpoints ErdosInversePrimeBin

theorem coordinate_bounds {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    {p : ℕ} (hp : w < (p:ℝ) ∧ (p:ℝ) ≤ z) :
    0 < coordinate w z xi p ∧ coordinate w z xi p ≤ (binCount w z xi:ℝ) := by
  have hlog : 0 < Real.log ((p:ℝ)/w) := by
    apply Real.log_pos
    exact (lt_div_iff₀ hw).mpr (by simpa only [one_mul] using hp.1)
  have hd := logWidth_pos hw hwz hxi
  refine ⟨div_pos hlog hd,?_⟩
  apply (div_le_iff₀ hd).mpr
  rw [count_mul_logWidth hw hwz hxi]
  exact Real.log_le_log (div_pos (hw.trans hp.1) hw) (div_le_div_of_nonneg_right hp.2 hw.le)

theorem index_eq_ceiling {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    {p : ℕ} (hp : w < (p:ℝ) ∧ (p:ℝ) ≤ z) : index w z xi p = ⌈coordinate w z xi p⌉₊-1 := by
  have hc : ⌈coordinate w z xi p⌉₊ ≤ binCount w z xi := Nat.ceil_le.mpr (coordinate_bounds hw hwz hxi hp).2
  exact min_eq_right (by omega)

theorem label_coordinate_bounds {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    {p : ℕ} (hp : w < (p:ℝ) ∧ (p:ℝ) ≤ z) :
    ((label hw hwz hxi p).1:ℝ) < coordinate w z xi p ∧
      coordinate w z xi p ≤ ((label hw hwz hxi p).1:ℝ)+1 := by
  have hc := coordinate_bounds hw hwz hxi hp
  have hpos : 0 < ⌈coordinate w z xi p⌉₊ := Nat.ceil_pos.mpr hc.1
  have hlow := Nat.ceil_lt_add_one hc.1.le
  have hhigh := Nat.le_ceil (coordinate w z xi p)
  have he : ((label hw hwz hxi p).1:ℝ) = (⌈coordinate w z xi p⌉₊:ℝ)-1 := by
    change (index w z xi p:ℝ) = _
    rw [index_eq_ceiling hw hwz hxi hp,Nat.cast_sub (by omega : 1 ≤ ⌈coordinate w z xi p⌉₊)]
    norm_num
  rw [he]
  constructor <;> linarith

theorem label_value_bounds {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    {p : ℕ} (hp : w < (p:ℝ) ∧ (p:ℝ) ≤ z) :
    lower w z xi (label hw hwz hxi p) < (p:ℝ) ∧
      (p:ℝ) ≤ upper w z xi (label hw hwz hxi p) := by
  have hb := label_coordinate_bounds hw hwz hxi hp
  have hd := logWidth_pos hw hwz hxi
  have hpw : 0 < (p:ℝ)/w := div_pos (hw.trans hp.1) hw
  have he : coordinate w z xi p*logWidth w z xi = Real.log ((p:ℝ)/w) := by
    unfold coordinate
    field_simp [hd.ne']
  have hlo := mul_lt_mul_of_pos_right hb.1 hd
  have hhi := mul_le_mul_of_nonneg_right hb.2 hd.le
  rw [he] at hlo hhi
  have hExpLo := Real.exp_lt_exp.mpr hlo
  have hExpHi := Real.exp_le_exp.mpr hhi
  rw [Real.exp_log hpw] at hExpLo hExpHi
  constructor
  · have h := (lt_div_iff₀ hw).mp hExpLo
    simpa only [lower,endpoint,mul_comm] using h
  · rw [upper_endpoint]
    have h := (div_le_iff₀ hw).mp hExpHi
    simpa only [endpoint,Nat.cast_add,Nat.cast_one,mul_comm] using h

theorem label_prime_membership {w z xi : ℝ} (hw : 0 < w) (hwz : w < z) (hxi : 0 < xi)
    {p : ℕ} (hprime : p.Prime) (hp : w < (p:ℝ) ∧ (p:ℝ) ≤ z) :
    p ∈ primeBin (lower w z xi (label hw hwz hxi p)) (width w z xi (label hw hwz hxi p)) := by
  apply (mem_primeBin (endpoint_pos hw _).le (effectiveWidth_pos hw hwz hxi).le p).mpr
  exact ⟨hprime,(label_value_bounds hw hwz hxi hp).1,(label_value_bounds hw hwz hxi hp).2⟩

end NumberTheoryLean.LogarithmicBinLabels



namespace NumberTheoryLean.LogarithmicBinPartition

open _root_.Set _root_.Finset
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels ErdosInversePrimeBin

theorem mem_sourcePrimeSet {w z : ℝ} (hw : 0 < w) (hwz : w < z) (p : ℕ) :
    p ∈ sourcePrimeSet w z ↔ p.Prime ∧ w < (p:ℝ) ∧ (p:ℝ) ≤ z := by
  constructor
  · intro hp
    obtain ⟨hup,hnot⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hbound,hprime⟩ := Nat.mem_primesLE.mp hup
    refine ⟨hprime,?_,(Nat.le_floor_iff (hw.trans hwz).le).mp hbound⟩
    by_contra! hlo
    exact hnot (Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hw.le).mpr hlo,hprime⟩)
  · rintro ⟨hprime,hlo,hhi⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (hw.trans hwz).le).mpr hhi,hprime⟩,?_⟩
    intro hp
    exact (not_le_of_gt hlo) ((Nat.le_floor_iff hw.le).mp (Nat.mem_primesLE.mp hp).1)

end NumberTheoryLean.LogarithmicBinPartition



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



namespace NumberTheoryLean.LogarithmicBinMaps

open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open SourceStopPredicate PrimeBinRepresentatives RepresentativeAdmission PrimeHistories
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem source_representative_error {w z xi : ℝ} (hw : 1 < w) (hwz : w < z) (hxi : 0 < xi)
    {p : ℕ} (hp : p ∈ sourcePrimeSet w z) :
    0 ≤ representative w (lower w z xi) (width w z xi) (label (by linarith : 0 < w) hwz hxi) p-primeExponent w p ∧
      representative w (lower w z xi) (width w z xi) (label (by linarith : 0 < w) hwz hxi) p-primeExponent w p ≤ xi/Real.log w := by
  have hw0 : 0 < w := by linarith
  have hs := (mem_sourcePrimeSet hw0 hwz p).mp hp
  have hbin := label_prime_membership hw0 hwz hxi hs.1 hs.2
  have he := representative_error hw (endpoint_pos hw0 _) (effectiveWidth_pos hw0 hwz hxi).le hbin
  refine ⟨he.1,he.2.trans ?_⟩
  exact div_le_div_of_nonneg_right (effectiveWidth_le hw0 hwz hxi) (Real.log_pos hw).le

end NumberTheoryLean.LogarithmicBinMaps



namespace NumberTheoryLean.IsolatedBinGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinMaps
open PrimeBinRepresentatives SourceStopPredicate
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem source_left_error {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    {p : ℕ} (hp : p ∈ sourcePrimeSet w top) :
    0 ≤ primeExponent w p-leftExponent w (lower w top xi (label (zero_lt_one.trans hw) htop hxi p)) ∧
      primeExponent w p-leftExponent w (lower w top xi (label (zero_lt_one.trans hw) htop hxi p)) ≤ xi/Real.log w := by
  have hp' := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp hp
  have hbin := label_prime_membership (zero_lt_one.trans hw) htop hxi hp'.1 hp'.2
  have hh := bin_exponent_bounds hw (endpoint_pos (zero_lt_one.trans hw) _) (effectiveWidth_pos (zero_lt_one.trans hw) htop hxi).le hbin
  have hwid := bin_exponent_width (w:=w)
    (R:=lower w top xi (label (zero_lt_one.trans hw) htop hxi p))
    (xi:=width w top xi (label (zero_lt_one.trans hw) htop hxi p))
    (endpoint_pos (zero_lt_one.trans hw) _) (effectiveWidth_pos (zero_lt_one.trans hw) htop hxi).le
  have heff := effectiveWidth_pos (zero_lt_one.trans hw) htop hxi
  have hlog : Real.log (1+effectiveWidth w top xi) ≤ xi := by
    have he := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+effectiveWidth w top xi)
    linarith [effectiveWidth_le (zero_lt_one.trans hw) htop hxi]
  refine ⟨sub_nonneg.mpr hh.1.le,?_⟩
  have hb := div_le_div_of_nonneg_right hlog (Real.log_pos hw).le
  simp only [width,lower] at hwid ⊢
  linarith [hh.2]

theorem whole_bin_of_exponent_band {w top xi B alpha beta : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    {p : ℕ} (hp : p ∈ sourcePrimeSet w top)
    (hlo : alpha*B+xi/Real.log w ≤ primeExponent w p)
    (hhi : primeExponent w p+xi/Real.log w ≤ beta*B) :
    isolatedBin w top xi B alpha beta (label (zero_lt_one.trans hw) htop hxi p) := by
  have hl := (source_left_error hw htop hxi hp).2
  have hu := (source_representative_error hw htop hxi hp).2
  change rightExponent w (lower w top xi _) (width w top xi _)-primeExponent w p ≤ _ at hu
  exact ⟨by linarith,by linarith⟩

end NumberTheoryLean.IsolatedBinGeometry



namespace NumberTheoryLean.CrossingBandGeometry
open _root_.Set FinitePathGeometry FinitePathMeasures ArrivalKernelGeometry
open RegeneratingInverseBands

theorem matched_gap_crossing {H r q d : ℝ} (_hH : 0 < H) (hr : 0 < r) (hq : 0 < q)
    (hlo : H/3 < r) (hhi : r ≤ H) (hd : |Real.log r-Real.log q| ≤ d)
    (he : Real.exp d ≤ 11/10) : q ∈ Icc (crossingLower H) (crossingUpper H) := by
  have h := NearbyParentGeometry.log_gap_relative hr hq hd
  have hl : r ≤ (11/10:ℝ)*q := h.1.trans (mul_le_mul_of_nonneg_right he hq.le)
  have hu : q ≤ (11/10:ℝ)*r := h.2.trans (mul_le_mul_of_nonneg_right he hr.le)
  exact ⟨by dsimp [crossingLower] <;> nlinarith,by dsimp [crossingUpper] <;> nlinarith⟩

theorem crossing_cost_band {H : ℝ} (hH : 0 < H) (v : ℝ) (z : CostState)
    (hz : gapValue v z ∈ Icc (crossingLower H) (crossingUpper H)) :
    z.2 ∈ Icc (crossingCenter v H) (crossingCenter v H+crossingWidth) := by
  have hlo : 0 < crossingLower H := by unfold crossingLower; positivity
  have hhi : 0 < crossingUpper H := by unfold crossingUpper; positivity
  have hl := Real.log_le_log hlo hz.1
  have hu := Real.log_le_log (Real.exp_pos (v-z.2)) hz.2
  change Real.log (crossingLower H) ≤ Real.log (Real.exp (v-z.2)) at hl
  change Real.log (Real.exp (v-z.2)) ≤ Real.log (crossingUpper H) at hu
  rw [Real.log_exp] at hl hu
  have hwidth : Real.log (crossingUpper H)-Real.log (crossingLower H)=crossingWidth := by
    unfold crossingWidth
    rw [← Real.log_div hhi.ne' hlo.ne']
    congr 1
    dsimp [crossingUpper,crossingLower]
    field_simp [hH.ne']
  constructor <;> dsimp [crossingCenter] <;> linarith
end NumberTheoryLean.CrossingBandGeometry


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

theorem joint_power_left (v mesh : ℝ) (n : ℕ) (q : JointState w ell S start) :
    (((jointKernel hw hell hS0 hS hr hs hsS v mesh)^n) q).map Prod.fst =
      ((chain w ell S start)^n) q.1 := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  exact map_power_of_step _ _ measurable_fst
    (fun x => jointKernel_left hw hell hS0 hS hr hs hsS v mesh x.1 x.2) n q

instance jointPathLaw_probability (v mesh : ℝ) (z : CostState) (n : ℕ) :
    IsProbabilityMeasure (jointPathLaw hw hell hS0 hS hr hs hsS v mesh z n) := by
  unfold jointPathLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem jointPathLaw_prime (v mesh : ℝ) (z : CostState) (n : ℕ) :
    (jointPathLaw hw hell hS0 hS hr hs hsS v mesh z n).map Prod.fst = pathLaw w ell S start n :=
  joint_power_left hw hell hS0 hS hr hs hsS v mesh n (some History.empty,.inl z)

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

theorem failed_measurable : MeasurableSet (failed (α:=α)) :=
  measurable_snd (measurableSet_singleton true)

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



namespace NumberTheoryLean.FullHistoryFailureFlag

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FiniteHistoryTransport PersistentFailureFlag

variable {X : Type*} [MeasurableSpace X]

theorem noResetPath_measurable (n : ℕ) : MeasurableSet {h : Hist (FlagState X) n | noResetPath n h} := by
  simp only [noResetPath,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  exact ((measurable_snd.comp (last_measurable n)) (measurableSet_singleton false)).imp
    ((measurable_snd.comp (measurable_pi_apply j)) (measurableSet_singleton false))

theorem noResetPath_extend (n : ℕ) (h : Hist (FlagState X) n) (y : FlagState X)
    (hh : noResetPath n h) (hy : y.2 = false → (last n h).2 = false) :
    noResetPath (n+1) (extend n h y) := by
  intro ⟨j,hj⟩ hflag
  rw [extend_last] at hflag
  have hj' := Finset.mem_Iic.mp hj
  by_cases hle : j ≤ n
  · rw [extend_previous n h y ⟨j,Finset.mem_Iic.mpr hle⟩]
    exact hh _ (hy hflag)
  · have heq : j = n+1 := by omega
    subst j
    change (last (n+1) (FiniteHistoryTransport.extend n h y)).2 = false
    rw [extend_last]
    exact hflag

theorem marked_no_reset (K : Kernel X X) [IsMarkovKernel K] {Bad : X → Prop}
    (hBad : MeasurableSet {x | Bad x}) (z : FlagState X) :
    ∀ᵐ y ∂marked K hBad z, y.2 = false → z.2 = false := by
  have hP : MeasurableSet {y : FlagState X | y.2 = false → z.2 = false} :=
    (measurable_snd (measurableSet_singleton false)).imp (by by_cases hz : z.2 = false <;> simp [hz])
  rw [marked_eq_map K hBad z]
  apply (ae_map_iff (row_update_measurable hBad z.2).aemeasurable hP).mpr
  apply Filter.Eventually.of_forall
  intro y
  cases z.2 <;> simp

theorem marked_history_no_reset (K : Kernel X X) [IsMarkovKernel K] {Bad : X → Prop}
    (hBad : MeasurableSet {x | Bad x}) (x : X) (N : ℕ) :
    ∀ᵐ h ∂pathKernel (marked K hBad) N (fun _ => (x,false)), noResetPath N h := by
  induction N with
  | zero =>
    change ∀ᵐ h ∂Measure.dirac (fun _ => (x,false)), noResetPath 0 h
    exact (ae_dirac_iff (noResetPath_measurable 0)).mpr (fun _ _ => rfl)
  | succ N ih =>
    apply ae_pathKernel_succ _ N _ (noResetPath_measurable (N+1))
    filter_upwards [ih] with h hh
    filter_upwards [marked_no_reset K hBad (last N h)] with y hy
    exact noResetPath_extend N h y hh hy

end NumberTheoryLean.FullHistoryFailureFlag



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

theorem sourceLaw_prime (mesh : ℝ) (n : ℕ) :
    (sourceLaw hw hell hS0 hS hr hs hsS mesh n).map (fun q => q.1.1) = pathLaw w ell S start n := by
  calc
    _ = ((sourceLaw hw hell hS0 hS hr hs hsS mesh n).map Prod.fst).map Prod.fst :=
      (Measure.map_map (f:=Prod.fst) (g:=Prod.fst) measurable_fst measurable_fst).symm
    _ = _ := by rw [sourceLaw_joint,jointPathLaw_prime]

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CanonicalCoupledHistories
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ActualCoupledHistories

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualFlagInvariant PersistentFailureFlag
open FlaggedSourceStart ContinuousKilledBins FiniteHistoryTransport

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

instance sourceTransition_markov (mesh : ℝ) :
    IsMarkovKernel (sourceTransition hw hell hS0 hS hr hs hsS mesh) := by
  unfold sourceTransition
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance sourceHistoryLaw_probability (mesh : ℝ) (n : ℕ) :
    IsProbabilityMeasure (sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh n) := by
  unfold sourceHistoryLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem sourceHistoryLaw_endpoint (mesh : ℝ) (n : ℕ) :
    (sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh n).map (last n) =
      sourceLaw hw hell hS0 hS hr hs hsS mesh n :=
  pathMeasure_endpoint _ n _

theorem sourceHistoryLaw_coordinate (mesh : ℝ) (n k : ℕ) (hk : k ≤ n) :
    (sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh n).map
      (fun h => h ⟨k, by simpa using hk⟩) = sourceLaw hw hell hS0 hS hr hs hsS mesh k :=
  pathMeasure_coordinate _ n k hk _

theorem sourceHistoryLaw_prime (mesh : ℝ) (n : ℕ) :
    (sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh n).map
      (mapHist (fun q => q.1.1) n) =
      pathKernel (chain w ell S start) n (fun _ => some History.empty) := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  apply pathMeasure_mapHist _ _ (measurable_fst.comp measurable_fst)
  intro q
  calc
    _ = ((sourceTransition hw hell hS0 hS hr hs hsS mesh q).map Prod.fst).map Prod.fst :=
      (Measure.map_map measurable_fst measurable_fst).symm
    _ = _ := by
      rw [sourceTransition, marked_map]
      exact jointKernel_left hw hell hS0 hS hr hs hsS (Real.log start.gap) mesh q.1.1 q.1.2

theorem sourceHistoryLaw_continuous (mesh : ℝ) (n : ℕ) :
    (sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh n).map
      (mapHist (fun q => q.1.2) n) =
      pathKernel (continuousChain (Real.log start.gap) ell S) n
        (fun _ => Sum.inl (sourceCostState hs)) := by
  apply pathMeasure_mapHist _ _ (measurable_snd.comp measurable_fst)
  intro q
  calc
    _ = ((sourceTransition hw hell hS0 hS hr hs hsS mesh q).map Prod.fst).map Prod.snd :=
      (Measure.map_map measurable_snd measurable_fst).symm
    _ = _ := by
      rw [sourceTransition, marked_map]
      exact jointKernel_right hw hell hS0 hS hr hs hsS (Real.log start.gap) mesh q.1.1 q.1.2

end NumberTheoryLean.ActualCoupledHistories



namespace NumberTheoryLean.ActualSuccessfulHistories

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling PersistentFailureFlag
open FiniteHistoryTransport ActualCoupledHistories FullHistoryFailureFlag
open ActualFlagInvariant FlaggedSourceStart FailureFlagBounds

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem sourceHistory_no_reset (mesh : ℝ) (N : ℕ) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N, noResetPath N h :=
  marked_history_no_reset _ (mismatch_measurable mesh) _ N

theorem sourceHistory_success_good {mesh : ℝ} (hm : 0 < mesh) (N : ℕ) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      (last N h).2 = false → ∀ j : Finset.Iic N,
        GoodAt (Real.log start.gap) mesh j.1 (h j).1 := by
  have hcoords : ∀ j : Finset.Iic N,
      ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
        surviving (GoodAt (Real.log start.gap) mesh j.1) (h j) := by
    intro j
    have hP := surviving_measurable (GoodAt_measurable (w:=w) (ell:=ell) (S:=S) (start:=start)
      (Real.log start.gap) mesh j.1)
    apply (ae_map_iff (measurable_pi_apply j).aemeasurable hP).mp
    have hcoord := sourceHistoryLaw_coordinate hw hell hS0 hS hr hs hsS mesh N j.1 (Finset.mem_Iic.mp j.2)
    rw [hcoord]
    exact sourceLaw_good hw hell hS0 hS hr hs hsS hm j.1
  have hAll := ae_all_iff.mpr hcoords
  filter_upwards [hAll,sourceHistory_no_reset hw hell hS0 hS hr hs hsS mesh N] with h hh hp
  intro hf j
  exact hh j (hp j hf)

theorem sourceHistory_failure_probability (mesh : ℝ) (N : ℕ) :
    sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N {h | (last N h).2 = true} =
      sourceLaw hw hell hS0 hS hr hs hsS mesh N failed := by
  rw [← sourceHistoryLaw_endpoint hw hell hS0 hS hr hs hsS mesh N,
    Measure.map_apply (last_measurable N) failed_measurable]
  rfl

end NumberTheoryLean.ActualSuccessfulHistories



namespace NumberTheoryLean.CanonicalCoupledHistories

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures FiniteHistoryTransport CemeteryHistoryMap
open CemeteryKernel ContinuousKilledBins LowStateHorizon ActualCoupledHistories
open FlaggedSourceStart PrimeHistories ActualProcessCoupling

theorem canonical_killing_image (s : State) (n : ℕ) (v ell S : ℝ) :
    (finitePathMeasure s n).map (killHist (lowDomain v ell S) n) =
      pathKernel (continuousChain v ell S) n (fun _ => Sum.inl (s,0)) := by
  exact pathMeasure_killHist costKernel (lowDomain_measurable v ell S) n (fun _ => (s,0))

variable {w ell S : ℝ} {start : Node}
variable (hw : PrimeKilledChain.normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem sourceHistoryLaw_canonical (mesh : ℝ) (n : ℕ) :
    (sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh n).map
      (mapHist (fun q => q.1.2) n) =
      (finitePathMeasure (typedState start.side start.ratio hs) n).map
        (killHist (lowDomain (Real.log start.gap) ell S) n) := by
  rw [sourceHistoryLaw_continuous,canonical_killing_image]
  rfl

theorem sourceHistoryLaw_canonical_event (mesh : ℝ) (n : ℕ)
    {A : Set (Hist (Space CostState) n)} (hA : MeasurableSet A) :
    sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh n
        ((mapHist (fun q => q.1.2) n) ⁻¹' A) =
      finitePathMeasure (typedState start.side start.ratio hs) n
        ((killHist (lowDomain (Real.log start.gap) ell S) n) ⁻¹' A) := by
  have h := congrArg (fun μ : Measure (Hist (Space CostState) n) => μ A)
    (sourceHistoryLaw_canonical hw hell hS0 hS hr hs hsS mesh n)
  rwa [Measure.map_apply (by exact mapHist_measurable (by exact measurable_snd.comp measurable_fst) n) hA,
    Measure.map_apply (killHist_measurable (lowDomain_measurable _ _ _) n) hA] at h

end NumberTheoryLean.CanonicalCoupledHistories


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FirstVisitRatioTail
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualCoupledHistories.sourceHistoryLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.ActualCoupledHistories.sourceTransition_markov _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointPathLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.continuousParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.jointKernel_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ContinuousKilledBins.continuousChain_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedSourceStart.sourceLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
namespace ErdosHighRatioBandTail
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.TransitionKernels
open NumberTheoryLean.KernelDensityBridge NumberTheoryLean.CompactExponentialMoments

theorem costKernel_highStates (s : State) (c T : ℝ) :
    costKernel (s,c) (Prod.fst ⁻¹' highStates T) = stateKernel s (highStates T) := by
  rw [costKernel_apply _ (measurable_fst (highStates_measurable T))]
  rfl

theorem even_state_high (s : EvenState) (T : ℝ) :
    stateKernel (.inl s) (highStates T) = evenKernel s (Ici T) := by
  rw [← stateKernel_even_ratio s, Measure.map_apply stateRatio_measurable measurableSet_Ici]
  rfl

theorem first_band_tail_bound : ∃ U : ℝ, 4 ≤ U ∧
    ∀ T : ℝ, U ≤ T → ∀ v h : ℝ, ∀ s : EvenState, s.1 ≤ 23/10 →
      costKernel (.inl s,0) (highBand T v h) ≤
        ENNReal.ofReal (Real.exp (-2*(T-(U-1)))) := by
  obtain ⟨U,hU,he,_ho⟩ := kernel_uniform_upper_tails
  refine ⟨U,hU,?_⟩
  intro T hT v h s hs
  have ht := he U le_rfl s (by linarith) (T-(U-1)) (by linarith)
  rw [show U-1+(T-(U-1))=T by ring] at ht
  calc
    _ ≤ costKernel (.inl s,0) (Prod.fst ⁻¹' highStates T) :=
      measure_mono (fun _ hz => hz.1)
    _ = evenKernel s (Ici T) := by rw [costKernel_highStates, even_state_high]
    _ ≤ _ := ht

theorem exponential_tail_tendsto (U : ℝ) :
    Tendsto (fun T : ℝ => ENNReal.ofReal (Real.exp (-2*(T-(U-1))))) atTop (𝓝 0) := by
  have hsub : Tendsto (fun T : ℝ => T-(U-1)) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using
      tendsto_atTop_add_const_right atTop (-(U-1)) (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop)
  have hlin : Tendsto (fun T : ℝ => 2*(T-(U-1))) atTop atTop :=
    hsub.const_mul_atTop (by norm_num)
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
  have hh := (ENNReal.continuous_ofReal.tendsto 0).comp he
  simpa only [Function.comp_def, neg_mul, ENNReal.ofReal_zero] using hh

end ErdosHighRatioBandTail


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_FullOccupationRatioTail
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualCoupledHistories.sourceHistoryLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.ActualCoupledHistories.sourceTransition_markov _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointPathLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.continuousParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.jointKernel_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ContinuousKilledBins.continuousChain_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedSourceStart.sourceLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
namespace ErdosHighRatioBandTail
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.TransitionKernels
open NumberTheoryLean.OccupationDecomposition NumberTheoryLean.InitialOccupation
open NumberTheoryLean.CostPrefixTransport NumberTheoryLean.EvenBandBounds
open Erdos970Dependency.StateKernelInvariance

theorem full_band_tail_bound (h : ℝ) : ∃ C : ℝ≥0∞, C < ∞ ∧ ∃ U : ℝ, 4 ≤ U ∧
    ∀ T : ℝ, U ≤ T → ∀ v : ℝ, ∀ s : EvenState,
      199/100 ≤ s.1 → s.1 ≤ 23/10 →
      fullOccupation (.inl s,0) (highBand T v h) ≤
        ENNReal.ofReal (Real.exp (-2*(T-(U-1)))) + C*stateMeasure (highStates T) := by
  obtain ⟨C,hC,hlater⟩ := later_band_tail_bound h
  obtain ⟨U,hU,hfirst⟩ := first_band_tail_bound
  refine ⟨C,hC,U,hU,?_⟩
  intro T hT v s hsL hsU
  rw [fullOccupation_first_and_later]
  change costKernel (.inl s,0) (highBand T v h) +
      prefixOccupation 2 (.inl s,0) (highBand T v h) ≤ _
  exact add_le_add (hfirst T hT v h s hsU) (hlater T v s hsL hsU)

theorem uniform_full_occupation_tail (h eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ T : ℝ in atTop, ∀ v : ℝ, ∀ s : EvenState,
      199/100 ≤ s.1 → s.1 ≤ 23/10 →
      fullOccupation (.inl s,0) (highBand T v h) ≤ ENNReal.ofReal eps := by
  obtain ⟨C,hC,U,_hU,hb⟩ := full_band_tail_bound h
  have hct : Tendsto (fun T : ℝ => C*stateMeasure (highStates T)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul stateMeasure_tail_tendsto (Or.inr hC.ne)
  have ht : Tendsto (fun T : ℝ => ENNReal.ofReal (Real.exp (-2*(T-(U-1)))) +
      C*stateMeasure (highStates T)) atTop (𝓝 0) := by
    simpa only [add_zero] using (exponential_tail_tendsto U).add hct
  have hsmall := ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr heps))
  filter_upwards [hsmall,eventually_ge_atTop U] with T hT hU
  intro v s hsL hsU
  exact (hb T hU v s hsL hsU).trans hT.le

end ErdosHighRatioBandTail


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_CanonicalHighRatioVisit
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualCoupledHistories.sourceHistoryLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.ActualCoupledHistories.sourceTransition_markov _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointPathLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.continuousParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.jointKernel_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ContinuousKilledBins.continuousChain_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedSourceStart.sourceLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
namespace ErdosHighRatioBandTail
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.TransitionKernels
open NumberTheoryLean.FiniteHistoryTransport NumberTheoryLean.OccupationDecomposition

theorem mem_positiveVisit (E : Set CostState) (N : ℕ)
    (path : ∀ _ : Finset.Iic N, CostState) :
    path ∈ positiveVisit E N ↔ ∃ k : Finset.Iic N, 0 < k.1 ∧ path k ∈ E := by
  constructor
  · intro h
    obtain ⟨j,hj⟩ := mem_iUnion.mp h
    exact ⟨⟨j.1+1,Finset.mem_Iic.mpr (Nat.succ_le_of_lt j.2)⟩,Nat.zero_lt_succ j.1,hj⟩
  · rintro ⟨k,hk,hE⟩
    let j : Fin N := ⟨k.1-1,by have := Finset.mem_Iic.mp k.2; omega⟩
    apply mem_iUnion.mpr
    refine ⟨j,?_⟩
    have he : (⟨j.1+1,Finset.mem_Iic.mpr (Nat.succ_le_of_lt j.2)⟩ : Finset.Iic N)=k := by
      apply Subtype.ext
      dsimp [j]
      omega
    change path _ ∈ E
    rwa [he]

theorem canonical_coordinate_law (s : State) (N k : ℕ) (hk : k ≤ N) :
    (finitePathMeasure s N).map (fun path => path ⟨k,Finset.mem_Iic.mpr hk⟩) =
      (costKernel^k) (s,0) := by
  have h := pathMeasure_coordinate costKernel N k hk (fun _ => (s,0))
  have hkernel : pastKernel costKernel = historyKernel := by
    funext n
    rfl
  unfold pathKernel at h
  rw [hkernel] at h
  simpa only [finitePathMeasure, finitePathKernel, last] using h

theorem positiveVisit_le_fullOccupation (s : State) (N : ℕ) {E : Set CostState}
    (hE : MeasurableSet E) :
    finitePathMeasure s N (positiveVisit E N) ≤ fullOccupation (s,0) E := by
  calc
    _ ≤ ∑ j : Fin N, finitePathMeasure s N
        {path | path ⟨j.1+1,Finset.mem_Iic.mpr (Nat.succ_le_of_lt j.2)⟩ ∈ E} :=
      measure_iUnion_fintype_le (finitePathMeasure s N) _
    _ = ∑ j : Fin N, (costKernel^(j.1+1)) (s,0) E := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← canonical_coordinate_law s N (j.1+1) (Nat.succ_le_of_lt j.2)]
      have hm : Measurable (fun path : (∀ _ : Finset.Iic N, CostState) =>
          path ⟨j.1+1,Finset.mem_Iic.mpr (Nat.succ_le_of_lt j.2)⟩) := measurable_pi_apply _
      exact (Measure.map_apply hm hE).symm
    _ ≤ ∑' k : ℕ, (costKernel^(k+1)) (s,0) E := by
      rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (costKernel^(k+1)) (s,0) E) N]
      exact ENNReal.sum_le_tsum (Finset.range N)
    _ = fullOccupation (s,0) E := by
      rw [fullOccupation, Kernel.sum_apply' _ _ hE]

theorem uniform_canonical_visit_tail (h eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ T : ℝ in atTop, ∀ v : ℝ, ∀ s : EvenState,
      199/100 ≤ s.1 → s.1 ≤ 23/10 → ∀ N : ℕ,
      finitePathMeasure (.inl s) N (positiveVisit (highBand T v h) N) ≤ ENNReal.ofReal eps := by
  filter_upwards [uniform_full_occupation_tail h eps heps] with T hT
  intro v s hsL hsU N
  exact (positiveVisit_le_fullOccupation (.inl s) N (highBand_measurable T v h)).trans
    (hT v s hsL hsU)

theorem exists_canonical_visit_threshold (h eps : ℝ) (heps : 0 < eps) :
    ∃ T₀ : ℝ, 3 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ v : ℝ, ∀ s : EvenState,
      199/100 ≤ s.1 → s.1 ≤ 23/10 → ∀ N : ℕ,
      finitePathMeasure (.inl s) N (positiveVisit (highBand T v h) N) ≤ ENNReal.ofReal eps := by
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp (uniform_canonical_visit_tail h eps heps)
  refine ⟨max T₀ 3,le_max_right _ _,?_⟩
  intro T hT
  exact hT₀ T ((le_max_left _ _).trans hT)

end ErdosHighRatioBandTail


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

theorem mesh_le_one {κ : ℝ} (hκ : 0 ≤ κ) (w : ℝ) : mesh κ w ≤ 1 := by
  apply (mesh_upper κ w).trans
  apply Real.exp_le_one_iff.mpr
  nlinarith [Real.sqrt_nonneg (Real.log w)]

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

end NumberTheoryLean.ExponentialMesh

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
open UniformFailureBudget ExponentialMesh BudgetPolynomialBound PrimeKilledChain

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ScaledOriginalTail
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualCoupledHistories.sourceHistoryLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.ActualCoupledHistories.sourceTransition_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open SuccessfulTailTransport ExponentialMesh UniformBudgetRate LowStateHorizon
open RegeneratingInverseBands CostPrefixTransport

theorem even_source_cost_state {start : Node} (hs : Valid start.side start.ratio)
    (hi : start.side = .even) :
    ∃ s : EvenState,s.1 = start.ratio ∧ FlaggedSourceStart.sourceCostState hs = (.inl s,0) := by
  cases start with
  | mk i s r cap closed =>
    change i = .even at hi
    subst i
    exact ⟨⟨s,hs⟩,rfl,rfl⟩

end NumberTheoryLean.SourceSuccessfulTail

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_SourceNodeCoordinates
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualCoupledHistories.sourceHistoryLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.ActualCoupledHistories.sourceTransition_markov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceNodeCoordinates

open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeBinMembership
open RegeneratingInverseBands ArrivalKernelGeometry SourceLowRemoval SourceSuccessfulTail
open InvariantInverseWeights DerivativeWeights

theorem node_gap_eq {B : ℝ} {start : Node} (hs : Valid start.side start.ratio)
    (hcons : Consistent start) (hcut : start.cutoff=B) : start.gap=B*start.ratio := by
  have he : start.cutoff=start.gap/start.ratio := hcons
  rw [hcut] at he
  exact ((eq_div_iff (valid_pos hs).ne').mp he).symm

theorem source_node_bounds {B : ℝ} (hB : 0 < B) (start : Node)
    (hi : start.side=.even) (h199 : 199/100 ≤ start.ratio) (h23 : start.ratio ≤ 23/10)
    (hcons : Consistent start) (hcut : start.cutoff=B) :
    Valid start.side start.ratio ∧ 0 < start.gap ∧ B ≤ start.gap ∧ start.gap ≤ (23/10:ℝ)*B := by
  have hs : Valid start.side start.ratio := by rw [hi]; change 198/100 ≤ start.ratio; linarith
  have he := node_gap_eq hs hcons hcut
  refine ⟨hs,?_,?_,?_⟩
  · rw [he]; exact mul_pos hB (valid_pos hs)
  · nlinarith
  · nlinarith

end NumberTheoryLean.SourceNodeCoordinates

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_ActualThresholdArrival
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.LiveKilledPrefixes

open _root_.Set Preorder
open FiniteHistoryTransport CemeteryHistoryMap CemeteryKernel

variable {X : Type*} [MeasurableSpace X]
attribute [local instance] Classical.propDecidable

theorem live_coordinate_original (E : Set X) (N k : ℕ) (hk : k ≤ N)
    (h : Hist X N) (z : X)
    (hz : killHist E N h ⟨k,Finset.mem_Iic.mpr hk⟩ = Sum.inl z) :
    h ⟨k,Finset.mem_Iic.mpr hk⟩ = z ∧
      aliveThrough E k (frestrictLe₂ (π := fun _ => X) hk h) := by
  rw [killHist_coordinate E N k hk h] at hz
  split_ifs at hz with ha
  · exact ⟨Sum.inl_injective hz,ha⟩
  · simp [dead] at hz

end NumberTheoryLean.LiveKilledPrefixes

end

section

namespace NumberTheoryLean.CompletedArrivalOccurrence
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures FiniteHistoryTransport FiniteHistoryOccurrence
open CemeteryKernel CemeteryHistoryMap LiveKilledPrefixes CanonicalCoupledHistories
open PrimeHistories PrimeKilledChain ActualCoupledHistories ActualProcessCoupling

theorem liveMember_measurable {X : Type*} [MeasurableSpace X] {E : Set X} (hE : MeasurableSet E) :
    MeasurableSet {y | liveMember E y} := measurableSet_sum_iff.mpr ⟨hE,MeasurableSet.empty⟩

theorem completedOccurrence_measurable {X : Type*} [MeasurableSpace X] {E : Set X}
    (hE : MeasurableSet E) (N : ℕ) : MeasurableSet {h | completedOccurrence E N h} := by
  simp only [completedOccurrence,Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro j
  have hc : Measurable (fun h : Hist (Space X) N => atIndex N h j.succ) := measurable_pi_apply _
  exact hc (liveMember_measurable hE)

theorem kill_completed_subset {X : Type*} [MeasurableSpace X] (D E : Set X) (N : ℕ) :
    (killHist D N) ⁻¹' {h | completedOccurrence E N h} ⊆ arrivalOccurrence E N := by
  rintro h ⟨j,hj⟩
  cases hy : atIndex N (killHist D N h) j.succ with
  | inr u => rw [hy] at hj; exact False.elim hj
  | inl y =>
    rw [hy] at hj
    have horig := (live_coordinate_original D N (j.1+1) (by have := j.isLt; omega) h y hy).1
    apply Set.mem_iUnion.mpr
    refine ⟨j,?_⟩
    change atIndex N h j.succ ∈ E
    rw [show atIndex N h j.succ=y from horig]
    exact hj

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem source_completed_occurrence_le (mesh : ℝ) (N : ℕ) {E : Set CostState} (hE : MeasurableSet E) :
    sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N
      ((mapHist (fun q => q.1.2) N) ⁻¹' {h | completedOccurrence E N h}) ≤
      finitePathMeasure (FlaggedSourceStart.typedState start.side start.ratio hs) N (arrivalOccurrence E N) := by
  rw [sourceHistoryLaw_canonical_event hw hell hS0 hS hr hs hsS mesh N (completedOccurrence_measurable hE N)]
  exact measure_mono (kill_completed_subset _ E N)
end NumberTheoryLean.CompletedArrivalOccurrence

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_AdjacentPrimeRecovery
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeHistoryPrefixOrder

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualCouplingUpdates
open FiniteHistoryTransport ActualCoupledHistories

variable {w ell S : ℝ} {start : Node}

theorem prefixRel_refl (p : ChainState w ell S start) : prefixRel p p := by
  cases p with
  | none => trivial
  | some p => exact ⟨[],by simp⟩

theorem prefixRel_trans {p q r : ChainState w ell S start} (hp : prefixRel p q) (hq : prefixRel q r) :
    prefixRel p r := by
  cases r with
  | none => trivial
  | some r =>
    cases q with
    | none => exact False.elim hq
    | some q =>
      cases p with
      | none => exact False.elim hp
      | some p =>
        obtain ⟨u,hu⟩ := hp
        obtain ⟨v,hv⟩ := hq
        exact ⟨u++v,by rw [hv,hu,List.append_assoc]⟩

theorem actual_row_prefixRel (p : ChainState w ell S start) :
    ∀ᵐ q ∂chain w ell S start p, prefixRel p q := by
  cases p with
  | none =>
    rw [chain_none]
    exact (ae_dirac_iff (by trivial)).mpr trivial
  | some p =>
    filter_upwards [prime_follows p] with q hq
    cases q with
    | none => trivial
    | some q =>
      obtain ⟨a,ha,rfl⟩ := hq
      exact ⟨[a],rfl⟩

theorem orderedPast_measurable (N : ℕ) :
    MeasurableSet {h : Hist (ChainState w ell S start) N | orderedPast N h} :=
  (Set.to_countable _).measurableSet

theorem orderedPast_extend (N : ℕ) (h : Hist (ChainState w ell S start) N)
    (q : ChainState w ell S start) (hp : orderedPast N h) (hq : prefixRel (last N h) q) :
    orderedPast (N+1) (FiniteHistoryTransport.extend N h q) := by
  intro ⟨i,hi⟩ ⟨j,hj⟩ hij
  have hi' := Finset.mem_Iic.mp hi
  have hj' := Finset.mem_Iic.mp hj
  by_cases hjN : j ≤ N
  · have hiN : i ≤ N := hij.trans hjN
    rw [extend_previous N h q ⟨i,Finset.mem_Iic.mpr hiN⟩,
      extend_previous N h q ⟨j,Finset.mem_Iic.mpr hjN⟩]
    exact hp _ _ hij
  · have hjEq : j = N+1 := by omega
    subst j
    change prefixRel _ (last (N+1) (FiniteHistoryTransport.extend N h q))
    rw [extend_last]
    by_cases hiN : i ≤ N
    · rw [extend_previous N h q ⟨i,Finset.mem_Iic.mpr hiN⟩]
      exact prefixRel_trans (hp ⟨i,Finset.mem_Iic.mpr hiN⟩ ⟨N,by simp⟩ hiN) hq
    · have hiEq : i = N+1 := by omega
      subst i
      change prefixRel (last (N+1) (FiniteHistoryTransport.extend N h q)) q
      rw [extend_last]
      exact prefixRel_refl q

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

include hw hell hS0 hS hr hs hsS

theorem actual_history_ordered (N : ℕ) :
    ∀ᵐ h ∂pathKernel (chain w ell S start) N (fun _ => some History.empty), orderedPast N h := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  induction N with
  | zero =>
    change ∀ᵐ h ∂Measure.dirac (fun _ => some History.empty), orderedPast 0 h
    exact (ae_dirac_iff (orderedPast_measurable 0)).mpr (fun _ _ _ => prefixRel_refl _)
  | succ N ih =>
    apply ae_pathKernel_succ _ N _ (orderedPast_measurable (N+1))
    filter_upwards [ih] with h hh
    filter_upwards [actual_row_prefixRel (last N h)] with q hq
    exact orderedPast_extend N h q hh hq

end NumberTheoryLean.PrimeHistoryPrefixOrder

end

section

namespace NumberTheoryLean.PriorPrimeWindow

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open FiniteHistoryTransport ActualCoupledHistories PrimeHistoryPrefixOrder
open ActualProcessCoupling ActualSuccessfulHistories SuccessfulMarkedCoordinates ArrivalKernelGeometry

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem sourceHistory_ordered (mesh : ℝ) (N : ℕ) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      orderedPast N (mapHist (fun q => q.1.1) N h) := by
  have hm := orderedPast_measurable (w:=w) (ell:=ell) (S:=S) (start:=start) N
  have hp : ∀ᵐ h ∂(sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N).map
      (mapHist (fun q => q.1.1) N), orderedPast N h := by
    rw [sourceHistoryLaw_prime]
    exact actual_history_ordered hw hell hS0 hS hr hs hsS N
  exact (ae_map_iff (mapHist_measurable (by exact measurable_fst.comp measurable_fst) N).aemeasurable hm).mp hp

theorem sourceHistory_prior_live (mesh : ℝ) (N : ℕ) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      ∀ i j : Finset.Iic N, i.1 ≤ j.1 → ∀ p : History w ell S start,
      (h j).1.1 = some p → ∃ q : History w ell S start,
        (h i).1.1 = some q ∧ ∃ tail : List ℕ,p.primes = q.primes++tail := by
  filter_upwards [sourceHistory_ordered hw hell hS0 hS hr hs hsS mesh N] with h hh
  intro i j hij p hp
  have hrel := hh i j hij
  change prefixRel (h i).1.1 (h j).1.1 at hrel
  rw [hp] at hrel
  cases hq : (h i).1.1 with
  | none => rw [hq] at hrel; exact False.elim hrel
  | some q =>
    rw [hq] at hrel
    exact ⟨q,rfl,hrel⟩

end NumberTheoryLean.PriorPrimeWindow

end

section

namespace NumberTheoryLean.PrimePrefixRecovery
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeChainHorizon
open FiniteHistoryTransport ActualCoupledHistories FlaggedSourceStart ActualProcessCoupling
open PriorPrimeWindow SourceThresholdCoupling ReconstructedParentCoupling

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem sourceHistory_stages (mesh : ℝ) (N : ℕ) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,∀ j : Finset.Iic N,
      stage j.1 (h j).1.1 := by
  apply ae_all_iff.mpr
  intro j
  have hP : MeasurableSet {q : PersistentFailureFlag.FlagState (JointState w ell S start) | stage j.1 q.1.1} :=
    (measurable_fst.comp measurable_fst) (stage_measurable j.1)
  have hc : Measurable (fun h : Hist (PersistentFailureFlag.FlagState (JointState w ell S start)) N => h j) :=
    measurable_pi_apply j
  apply (ae_map_iff hc.aemeasurable hP).mp
  rw [sourceHistoryLaw_coordinate hw hell hS0 hS hr hs hsS mesh N j.1 (Finset.mem_Iic.mp j.2)]
  have hh : ∀ᵐ p ∂(sourceLaw hw hell hS0 hS hr hs hsS mesh j.1).map (fun q => q.1.1),stage j.1 p := by
    rw [sourceLaw_prime hw hell hS0 hS hr hs hsS mesh j.1]
    exact pathLaw_stage j.1
  exact (ae_map_iff (measurable_fst.comp measurable_fst).aemeasurable (stage_measurable j.1)).mp hh

theorem sourceHistory_recovers_prefix (mesh : ℝ) (N : ℕ) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      ∀ j : Finset.Iic N,∀ p : History w ell S start,(h j).1.1=some p →
      ∀ pre tail : List ℕ,p.primes=pre++tail →
      ∃ hk : pre.length ≤ N,∃ q : History w ell S start,
        (h ⟨pre.length,Finset.mem_Iic.mpr hk⟩).1.1=some q ∧ q.primes=pre := by
  filter_upwards [sourceHistory_stages hw hell hS0 hS hr hs hsS mesh N,
    sourceHistory_prior_live hw hell hS0 hS hr hs hsS mesh N] with h hstage hprior
  intro j p hp pre tail hword
  have hlen : p.primes.length=j.1 := by
    have hh := hstage j
    rw [hp] at hh
    exact hh
  have hprej : pre.length ≤ j.1 := by rw [hword,List.length_append] at hlen; omega
  have hpreN := hprej.trans (Finset.mem_Iic.mp j.2)
  let i : Finset.Iic N := ⟨pre.length,Finset.mem_Iic.mpr hpreN⟩
  obtain ⟨q,hq,suf,hsuf⟩ := hprior i j hprej p hp
  have hqlen : q.primes.length=pre.length := by
    have hh := hstage i
    rw [hq] at hh
    exact hh
  have htakeP : p.primes.take pre.length=pre := by rw [hword]; simp
  have htakeQ : p.primes.take q.primes.length=q.primes := by rw [hsuf]; simp
  rw [hqlen] at htakeQ
  exact ⟨hpreN,q,hq,htakeQ.symm.trans htakeP⟩

end NumberTheoryLean.PrimePrefixRecovery

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_SourceSelectedCompactOccupation
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceSelectedCompactOccupation

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling PersistentFailureFlag
open FiniteHistoryTransport ActualCoupledHistories FullPathCompactSelection
open PrimeCompactWeights PrimeCorrectionFactor PrimeBinMembership

theorem fullSourceLaw_eq {w ell S : ℝ} {start : Node}
    (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
    (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S) (mesh : ℝ) (N : ℕ) :
    fullSourceLaw w ell S start hs mesh N = sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N := rfl

end NumberTheoryLean.SourceSelectedCompactOccupation

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SourceMarkedStopping
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.MarkedPrefixTools
open FinitePathGeometry PrimeHistories FiniteFirstTag ActualSourceTags PrimeBinRepresentatives
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem terminal_cutoff_last (w : ℝ) (z : Node) (ps : List ℕ) (hne : ps ≠ []) :
    (terminal w z ps).cutoff=primeExponent w (ps.getLast hne) := by
  conv_lhs => rw [← List.dropLast_append_getLast hne]
  rw [terminal_append]
  rfl

theorem terminal_lastD (w : ℝ) (z : Node) (ps : List ℕ) (hne : ps ≠ []) :
    (terminal w z ps).cutoff=primeExponent w (ps.getLastD 0) := by
  have hh := terminal_cutoff_last w z ps hne
  have he : ps.getLastD 0=ps.getLast hne := by
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    exact List.getLastD_concat
  rwa [he]

end NumberTheoryLean.MarkedPrefixTools

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_ActualRepeatedBinStep
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CandidateTerminalGeometry
open FinitePathGeometry PrimeHistories PrimeBinMembership SourceStopPredicate
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem terminal_ratio_div_cutoff (w : ℝ) (z : Node) (ps : List ℕ) (hne : ps ≠ [])
    (hx : (terminal w z ps).cutoff ≠ 0) :
    (terminal w z ps).ratio=(terminal w z ps).gap/(terminal w z ps).cutoff := by
  induction ps generalizing z with
  | nil => exact False.elim (hne rfl)
  | cons p ps ih =>
    cases ps with
    | nil =>
      change primeExponent w p ≠ 0 at hx
      change PrimeTiltGeometry.childRatio w z.gap p=(z.gap-primeExponent w p)/primeExponent w p
      unfold PrimeTiltGeometry.childRatio
      field_simp [hx]
    | cons q qs => exact ih (step w z p) (by simp) hx

end NumberTheoryLean.CandidateTerminalGeometry



namespace NumberTheoryLean.ActualRepeatedBinStep
open FinitePathGeometry PrimeHistories PrimeTiltGeometry PrimeBinMembership ActualPrimeHigh
open CandidateTerminalGeometry MarkedPrefixTools
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinMaps
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem history_source_primes {w ell S top : ℝ} {start : Node}
    (hw : 1 < w) (htop : w < top) (hell : 1 ≤ ell) (hcap : w^start.cutoff=top)
    (h : History w ell S start) : ∀ p ∈ h.primes,p ∈ sourcePrimeSet w top := by
  intro p hp
  obtain ⟨hprime,hlo,hguard⟩ := allowed_prime_bounds hw h.admissible p hp
  have hp0 : 0 < (p:ℝ) := by exact_mod_cast hprime.pos
  have hlow : w < (p:ℝ) := by
    simpa only [Real.rpow_one] using (lt_exponent_iff hw hp0).mp (hell.trans_lt hlo)
  have hupper : primeExponent w p ≤ start.cutoff := by
    cases he : start.closed with
    | false =>
      simp only [capGuard,he,Bool.false_eq_true,ite_false, if_false] at hguard
      exact hguard.le
    | true => simpa only [capGuard,he,ite_true, if_true] using hguard
  have hhigh := (exponent_le_iff hw hp0).mp hupper
  rw [hcap] at hhigh
  exact (mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mpr ⟨hprime,hlow,hhigh⟩

end NumberTheoryLean.ActualRepeatedBinStep


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FiniteBoxWordMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace ErdosSearchCount
open NumberTheoryLean FinitePathGeometry PrimeTiltGeometry PrimeHistories
open ErdosPrimeInputs.HarmonicPrimeMeasure


theorem valid_half {i : Side} {s : ℝ} (hs : Valid i s) : (1:ℝ)/2 ≤ s := by
  cases i <;> dsimp [Valid] at hs <;> linarith

theorem child_gap_third {w ell S : ℝ} {z : Node} {p : ℕ}
    (hell : 0 ≤ ell) (hs : Valid z.side z.ratio)
    (hp : p ∈ nodeChildren w ell S z) : z.gap ≤ 3*(step w z p).gap := by
  have hx := child_exponent_positive hell hp
  have ht := valid_half (child_valid hs hp)
  change (1:ℝ)/2 ≤ z.gap/primeExponent w p-1 at ht
  have hh : (3:ℝ)/2 ≤ z.gap/primeExponent w p := by linarith
  have hm := (le_div_iff₀ hx).mp hh
  change z.gap ≤ 3*(z.gap-primeExponent w p)
  linarith

end ErdosSearchCount



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_RepeatedPairEvents
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RepeatedPairEvents
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling ActualFlagInvariant PersistentFailureFlag
open RepeatedStepRowBound

variable {w ell S : ℝ} {start : Node}

theorem goodAt_enlarge {v mesh : ℝ} (hm : 0 ≤ mesh) {n N : ℕ} (hn : n ≤ N)
    (q : JointState w ell S start) (hq : GoodAt v mesh n q) : GoodAt v mesh N q := by
  rcases q with ⟨p,y⟩
  cases p with
  | none => cases y <;> exact hq
  | some p =>
    cases y with
    | inr u => exact False.elim hq
    | inl y =>
      refine ⟨hq.1,hq.2.1,hq.2.2.1,hq.2.2.2.trans ?_⟩
      have hnR : (n:ℝ) ≤ N := by exact_mod_cast hn
      nlinarith [mul_le_mul_of_nonneg_right hnR hm]
end NumberTheoryLean.RepeatedPairEvents


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_RepeatedWordData
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RepeatedWordData
open _root_.Set FinitePathGeometry PrimeHistories PrimeKilledChain PrimeTiltGeometry ActualPrimeHigh
open ActualRepeatedBinStep CandidateTerminalGeometry MarkedPrefixTools
open RepeatedPairEvents RepeatedPairProbability ActualSourceTags PrimeBinRepresentatives
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure


variable {w ell S : ℝ} {start : Node}

theorem history_last_mem (h : History w ell S start) (hne : h.primes ≠ []) : h.primes.getLastD 0 ∈ h.primes := by
  have he : h.primes.getLastD 0=h.primes.getLast hne := by
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    exact List.getLastD_concat
  rw [he]
  exact List.getLast_mem hne

theorem history_nonempty_cutoff_gt (hw : 1 < w) (h : History w ell S start) (hne : h.primes ≠ []) :
    ell < h.node.cutoff := by
  have hh := (allowed_prime_bounds hw h.admissible _ (history_last_mem h hne)).2.1
  rwa [← terminal_lastD w start h.primes hne] at hh

end NumberTheoryLean.RepeatedWordData


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceFirstCrossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.FirstGapCrossing
open FinitePathGeometry PrimeHistories PrimeTiltGeometry ErdosSearchCount
open ErdosPrimeInputs.HarmonicPrimeMeasure


theorem first_gap_crossing {w ell S : ℝ} (hell : 0 ≤ ell) (z : Node)
    (hs : Valid z.side z.ratio) (ps : List ℕ) (ha : allowed w ell S z ps)
    (H : ℝ) (hstart : H < z.gap) (hend : (terminal w z ps).gap ≤ H) :
    ∃ pre p tail,ps=pre++p::tail ∧ H < (terminal w z pre).gap ∧
      (terminal w z (pre++[p])).gap ≤ H ∧ H/3 < (terminal w z (pre++[p])).gap := by
  induction ps generalizing z with
  | nil => exact False.elim (not_lt_of_ge hend hstart)
  | cons p ps ih =>
    obtain ⟨hp,ht⟩ := (allowed_cons w ell S z p ps).mp ha
    by_cases hc : (step w z p).gap ≤ H
    · have hh := child_gap_third hell hs hp
      exact ⟨[],p,ps,rfl,hstart,hc,by change H/3 < (step w z p).gap; linarith⟩
    · obtain ⟨pre,q,tail,he,hpre,hend,hlo⟩ := ih (step w z p) (child_valid hs hp) ht (lt_of_not_ge hc) hend
      refine ⟨p::pre,q,tail,by rw [List.cons_append,he],hpre,?_,?_⟩
      · simpa only [List.cons_append,terminal_cons] using hend
      · simpa only [List.cons_append,terminal_cons] using hlo
end NumberTheoryLean.FirstGapCrossing



namespace NumberTheoryLean.SourceFirstCrossing
open FinitePathGeometry PrimeHistories PrimeTiltGeometry PrimeBinMembership FirstGapCrossing
open ErdosPrimeInputs.HarmonicPrimeMeasure

attribute [local instance] Classical.propDecidable

theorem source_first_above {w ell S B theta : ℝ} (hB : 0 < B) (htheta : theta ≤ 1/2)
    (z : Node) (hs : 199/100 ≤ z.ratio) (hc : Consistent z) (hcut : z.cutoff=B)
    {p : ℕ} (hp : p ∈ nodeChildren w ell S z) : theta*B < (step w z p).gap := by
  have hcap := (Finset.mem_filter.mp hp).2.2.1
  have hx : primeExponent w p ≤ B := by
    change capGuard z.closed z.cutoff (primeExponent w p) at hcap
    rw [hcut] at hcap
    cases h : z.closed <;> simp [capGuard,h] at hcap
    · exact hcap.le
    · exact hcap
  have hgap : z.gap=z.ratio*B := by
    have he : B=z.gap/z.ratio := hcut.symm.trans hc
    have hh := (eq_div_iff (by linarith : z.ratio ≠ 0)).mp he
    nlinarith
  change theta*B < z.gap-primeExponent w p
  rw [hgap]
  nlinarith

theorem source_gap_crossing {w ell S B theta : ℝ} (hell : 0 ≤ ell) (hB : 0 < B)
    (htheta : theta ≤ 1/2) (z : Node) (hs : Valid z.side z.ratio)
    (h199 : 199/100 ≤ z.ratio) (hc : Consistent z) (hcut : z.cutoff=B)
    (ps : List ℕ) (ha : allowed w ell S z ps) (hend : (terminal w z ps).gap ≤ theta*B) :
    ∃ pre p tail,pre ≠ [] ∧ ps=pre++p::tail ∧ theta*B < (terminal w z pre).gap ∧
      (terminal w z (pre++[p])).gap ≤ theta*B ∧ theta*B/3 < (terminal w z (pre++[p])).gap := by
  have hg : z.gap=z.ratio*B := (SourceNodeCoordinates.node_gap_eq hs hc hcut).trans (mul_comm _ _)
  have hstart : theta*B < z.gap := by rw [hg]; nlinarith
  obtain ⟨pre,p,tail,he,hpre,hhi,hlo⟩ := first_gap_crossing hell z hs ps ha (theta*B) hstart hend
  refine ⟨pre,p,tail,?_,he,hpre,hhi,hlo⟩
  intro hn
  subst pre
  simp only [List.nil_append] at he hhi
  have hp := ((allowed_cons w ell S z p tail).mp (he ▸ ha)).1
  exact (not_lt_of_ge hhi) (source_first_above hB htheta z h199 hc hcut hp)
end NumberTheoryLean.SourceFirstCrossing


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_CrossingPrimeBin
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CrossingPrimeBin
open FinitePathGeometry PrimeHistories PrimeTiltGeometry RepeatedWordData CandidateTerminalGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open IsolatedBinGeometry MarkedPrefixTools
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem isolated_alpha_bounds {theta T : ℝ} (htheta : 0 < theta) (hT : 1 ≤ T) :
    0 < isolatedAlpha theta T ∧ isolatedAlpha theta T ≤ theta := by
  unfold isolatedAlpha
  refine ⟨div_pos htheta (by linarith),?_⟩
  exact div_le_self htheta.le (by linarith)

theorem crossing_exponent_room {theta T B r s x h : ℝ} (htheta : 0 < theta) (hT : 1 ≤ T)
    (hB : 0 < B) (hx : 0 < x) (hs : (1:ℝ)/2 ≤ s) (hsT : s ≤ T)
    (he : r=s*x) (hlo : theta*B/3 < r) (hhi : r ≤ theta*B)
    (hh : h ≤ isolatedAlpha theta T*B) :
    isolatedAlpha theta T*B+h ≤ x ∧ x+h ≤ (4*theta)*B := by
  have ha := isolated_alpha_bounds htheta hT
  have hA : 0 ≤ isolatedAlpha theta T*B := mul_nonneg ha.1.le hB.le
  have hEq : 10*(isolatedAlpha theta T*B)*(T+1)=theta*B := by
    unfold isolatedAlpha
    field_simp [show T+1 ≠ 0 by linarith]
  have hlo' : 2*(isolatedAlpha theta T*B) ≤ x := by
    by_contra! hn
    have hm := mul_lt_mul_of_pos_right hn (by linarith : 0 < T)
    have hr : r ≤ x*T := by rw [he]; nlinarith
    nlinarith
  have hhi' : x ≤ 2*(theta*B) := by rw [he] at hhi; nlinarith
  have hAB : isolatedAlpha theta T*B ≤ theta*B := mul_le_mul_of_nonneg_right ha.2 hB.le
  exact ⟨by linarith,by nlinarith⟩

theorem actual_crossing_bin {w top xi ell S theta T B : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hell : 1 ≤ ell)
    (htheta : 0 < theta) (hT : 1 ≤ T) (hB : 0 < B) (z : Node)
    (hs : Valid z.side z.ratio) (hcap : w^z.cutoff=top)
    (h : History w ell S z) (hne : h.primes ≠ [])
    (hlo : theta*B/3 < h.node.gap) (hhi : h.node.gap ≤ theta*B) (hbound : h.node.ratio ≤ T)
    (hwidth : xi/Real.log w ≤ isolatedAlpha theta T*B) :
    isolatedBin w top xi B (isolatedAlpha theta T) (4*theta)
      (label (zero_lt_one.trans hw) htop hxi (h.primes.getLastD 0)) := by
  have hx := history_nonempty_cutoff_gt hw h hne
  have hx0 : 0 < h.node.cutoff := by linarith
  have hvalid : Valid h.node.side h.node.ratio := terminal_valid hs h.admissible
  have hslo : (1:ℝ)/2 ≤ h.node.ratio := by
    cases he : h.node.side <;> rw [he] at hvalid <;> dsimp [Valid] at hvalid <;> linarith
  have hratio := terminal_ratio_div_cutoff w z h.primes hne hx0.ne'
  change h.node.ratio=h.node.gap/h.node.cutoff at hratio
  have hgap : h.node.gap=h.node.ratio*h.node.cutoff := ((eq_div_iff hx0.ne').mp hratio).symm
  have hroom := crossing_exponent_room htheta hT hB hx0 hslo hbound hgap hlo hhi hwidth
  have hl : h.primes.getLastD 0 ∈ h.primes := history_last_mem h hne
  have hsrc := ActualRepeatedBinStep.history_source_primes hw htop hell hcap h _ hl
  have hcut : h.node.cutoff=primeExponent w (h.primes.getLastD 0) := terminal_lastD w z h.primes hne
  apply whole_bin_of_exponent_band hw htop hxi hsrc
  · rw [← hcut]; exact hroom.1
  · rw [← hcut]; exact hroom.2
end NumberTheoryLean.CrossingPrimeBin


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_GeometricRegularWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.GoodCrossingVisit
open _root_.Set _root_.MeasureTheory FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeTiltGeometry
open RegeneratingInverseBands ArrivalKernelGeometry ActualFlagInvariant CrossingPrimeBin CrossingBandGeometry
open IsolatedBinGeometry LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels

theorem crossingHighEvent_measurable (v H T : ℝ) : MeasurableSet (crossingHighEvent v H T) :=
  (measurableSet_lt measurable_const (stateRatio_measurable.comp measurable_fst)).inter
    (measurable_snd measurableSet_Icc)

theorem good_crossing_visit {w top xi ell S theta T B v mesh : ℝ} {N : ℕ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hell : 1 ≤ ell)
    (htheta : 0 < theta) (hT : 1 ≤ T) (hB : 0 < B) (hm : mesh ≤ 1)
    (he : Real.exp (4*(N:ℝ)*mesh) ≤ 11/10)
    (z : Node) (hs : Valid z.side z.ratio) (hcap : w^z.cutoff=top)
    (p : History w ell S z) (hne : p.primes ≠ []) (y : CostState)
    (hg : liveGood v mesh N p y)
    (hlo : theta*B/3 < p.node.gap) (hhi : p.node.gap ≤ theta*B)
    (hwidth : xi/Real.log w ≤ isolatedAlpha theta (T+1)*B)
    (hno : ¬isolatedBin w top xi B (isolatedAlpha theta (T+1)) (4*theta)
      (label (zero_lt_one.trans hw) htop hxi (p.primes.getLastD 0))) :
    y ∈ crossingHighEvent v (theta*B) T := by
  have hratio : T < stateRatio y.1 := by
    by_contra! hr
    have hpT : p.node.ratio ≤ T+1 := by linarith [(abs_le.mp hg.2.2.1).2]
    exact hno (actual_crossing_bin hw htop hxi hell htheta (by linarith) hB z hs hcap p hne hlo hhi hpT hwidth)
  have hp0 : 0 < p.node.gap := by nlinarith
  have hband := matched_gap_crossing (mul_pos htheta hB) hp0 (Real.exp_pos _) hlo hhi hg.2.2.2 he
  exact ⟨hratio,crossing_cost_band (mul_pos htheta hB) v y hband⟩
end NumberTheoryLean.GoodCrossingVisit



namespace NumberTheoryLean.NonisolatedWordOccurrence
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain FiniteHistoryTransport
open ActualSuccessfulHistories ActualCoupledHistories PrimePrefixRecovery ActualFlagInvariant RepeatedPairEvents
open SourceFirstCrossing GoodCrossingVisit CrossingPrimeBin IsolatedBinGeometry
open CompletedArrivalOccurrence LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels
open PersistentFailureFlag

variable {w ell S : ℝ} {start : Node}
variable (hwn : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem nonisolated_word_occurs {top xi B theta T mesh : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hB : 0 < B) (htheta : 0 < theta) (htheta1 : theta ≤ 1/2) (hT : 1 ≤ T)
    (h199 : 199/100 ≤ start.ratio) (hc : PrimeBinMembership.Consistent start) (hcut : start.cutoff=B)
    (hcap : w^start.cutoff=top) (hm : 0 < mesh) (hmesh : mesh ≤ 1) (N : ℕ)
    (hexp : Real.exp (4*(N:ℝ)*mesh) ≤ 11/10)
    (hwidth : xi/Real.log w ≤ isolatedAlpha theta (T+1)*B) :
    ∀ᵐ h ∂sourceHistoryLaw hwn hell hS0 hS hr hs hsS mesh N,
      (last N h).2=false → ∀ j : Finset.Iic N,∀ p : History w ell S start,(h j).1.1=some p →
        p.node.gap ≤ theta*B → noIsolatedWord hw htop hxi B (isolatedAlpha theta (T+1)) (4*theta) p.primes →
        completedOccurrence (crossingHighEvent (Real.log start.gap) (theta*B) T) N
          (mapHist (fun q => q.1.2) N h) := by
  filter_upwards [sourceHistory_success_good hwn hell hS0 hS hr hs hsS hm N,
    sourceHistory_recovers_prefix hwn hell hS0 hS hr hs hsS mesh N] with h hgood hprefix
  intro hf j p hp hend hno
  obtain ⟨pre,a,tail,hpre,he,_hbefore,hhi,hlo⟩ :=
    source_gap_crossing (by linarith) hB htheta1 start hs h199 hc hcut p.primes p.admissible hend
  have hword : p.primes=(pre++[a])++tail := by simpa only [List.append_assoc,List.singleton_append] using he
  obtain ⟨hk,q,hq,hqword⟩ := hprefix j p hp (pre++[a]) tail hword
  have hn : (pre++[a]).length ≠ 0 := by simp
  let i : Finset.Iic N := ⟨(pre++[a]).length,Finset.mem_Iic.mpr hk⟩
  let k : Fin N := ⟨(pre++[a]).length-1,by omega⟩
  have hkval : k.1+1=(pre++[a]).length := by dsimp [k]; omega
  have hg := goodAt_enlarge hm.le hk _ (hgood hf i)
  change GoodAt (Real.log start.gap) mesh N ((h i).1.1,(h i).1.2) at hg
  rw [hq] at hg
  cases hy : (h i).1.2 with
  | inr u => rw [hy] at hg; exact False.elim hg
  | inl y =>
    rw [hy] at hg
    have hqne : q.primes ≠ [] := by rw [hqword]; simp
    have hqhi : q.node.gap ≤ theta*B := by change (terminal w start q.primes).gap ≤ _; rwa [hqword]
    have hqlo : theta*B/3 < q.node.gap := by change _ < (terminal w start q.primes).gap; rwa [hqword]
    have ha : a ∈ p.primes := by rw [he]; simp
    have hlast : q.primes.getLastD 0=a := by rw [hqword]; exact List.getLastD_concat
    have hno' : ¬isolatedBin w top xi B (isolatedAlpha theta (T+1)) (4*theta)
        (label (zero_lt_one.trans hw) htop hxi (q.primes.getLastD 0)) := by rw [hlast]; exact hno a ha
    have hv := good_crossing_visit hw htop hxi hell htheta hT hB hmesh hexp start hs hcap q hqne y hg hqlo hqhi hwidth hno'
    refine ⟨k,?_⟩
    change liveMember _ ((h ⟨k.1+1,Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩).1.2)
    have hy' : (h ⟨k.1+1,Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩).1.2=Sum.inl y := by
      simpa only [hkval] using hy
    rw [hy']
    exact hv
end NumberTheoryLean.NonisolatedWordOccurrence



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_CanonicalCrossingTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CanonicalCrossingTail
open _root_.Set _root_.Erdos970.Set _root_.Filter _root_.Erdos970.Filter
open _root_.MeasureTheory _root_.Erdos970.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures FiniteHistoryTransport FiniteHistoryOccurrence
open TransitionKernels GoodCrossingVisit CrossingBandGeometry ErdosHighRatioBandTail


theorem crossing_arrival_subset (v H T : ℝ) (N : ℕ) :
    arrivalOccurrence (crossingHighEvent v H T) N ⊆
      positiveVisit (highBand T (crossingCenter v H) crossingWidth) N := by
  intro path hp
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hp
  apply (mem_positiveVisit _ _ _).mpr
  refine ⟨⟨j.1+1,Finset.mem_Iic.mpr (Nat.succ_le_of_lt j.2)⟩,Nat.zero_lt_succ _,?_,?_⟩
  · exact hj.1.le
  · exact hj.2

theorem canonical_crossing_tail (eps : ℝ) (heps : 0 < eps) :
    ∃ T : ℝ,3 ≤ T ∧ ∀ v H : ℝ,∀ s : EvenState,199/100 ≤ s.1 → s.1 ≤ 23/10 → ∀ N : ℕ,
      finitePathMeasure (.inl s) N (arrivalOccurrence (crossingHighEvent v H T) N) ≤ ENNReal.ofReal eps := by
  obtain ⟨T,hT,hTail⟩ := exists_canonical_visit_threshold crossingWidth eps heps
  refine ⟨T,hT,?_⟩
  intro v H s h199 h23 N
  exact (measure_mono (crossing_arrival_subset v H T N)).trans (hTail T le_rfl (crossingCenter v H) s h199 h23 N)
end NumberTheoryLean.CanonicalCrossingTail


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_NonisolatedSelectedOccurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.NonisolatedSelectedOccurrence
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain FiniteHistoryTransport
open ActualSuccessfulHistories ActualCoupledHistories CompactPrefixOccurrence SourceSelectedCompactOccupation
open NonisolatedWordOccurrence GoodCrossingVisit CrossingPrimeBin
open CompletedArrivalOccurrence PersistentFailureFlag CanonicalCoupledHistories

variable {w ell S : ℝ} {start : Node}
variable (hwn : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

include hwn hell hS0 hS hr hsS in
theorem selected_nonisolated_probability {top xi B theta T mesh : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (hB : 0 < B) (htheta : 0 < theta) (htheta1 : theta ≤ 1/2) (hT : 1 ≤ T)
    (h199 : 199/100 ≤ start.ratio) (hc : PrimeBinMembership.Consistent start) (hcut : start.cutoff=B)
    (hcap : w^start.cutoff=top) (hm : 0 < mesh) (hmesh : mesh ≤ 1) (N : ℕ)
    (hexp : Real.exp (4*(N:ℝ)*mesh) ≤ 11/10)
    (hwidth : xi/Real.log w ≤ isolatedAlpha theta (T+1)*B) (E : Set (List ℕ))
    (hE : ∀ p : History w ell S start,p.primes ∈ E → p.node.gap ≤ theta*B ∧
      noIsolatedWord hw htop hxi B (isolatedAlpha theta (T+1)) (4*theta) p.primes) :
    fullSourceLaw w ell S start hs mesh N {h | occurs E N h} ≤
      FlaggedSourceStart.sourceLaw hwn hell hS0 hS hr hs hsS mesh N failed +
      finitePathMeasure (FlaggedSourceStart.typedState start.side start.ratio hs) N
        (FiniteHistoryOccurrence.arrivalOccurrence (crossingHighEvent (Real.log start.gap) (theta*B) T) N) := by
  rw [fullSourceLaw_eq hwn hell hS0 hS hr hs hsS]
  have hsub : ∀ᵐ h ∂sourceHistoryLaw hwn hell hS0 hS hr hs hsS mesh N,
      occurs E N h → h ∈ {h | (last N h).2=true} ∪
        ((mapHist (fun q => q.1.2) N) ⁻¹' {h | completedOccurrence (crossingHighEvent (Real.log start.gap) (theta*B) T) N h}) := by
    filter_upwards [nonisolated_word_occurs hwn hell hS0 hS hr hs hsS hw htop hxi hB htheta htheta1 hT
      h199 hc hcut hcap hm hmesh N hexp hwidth] with h hh
    intro ho
    cases hf : (last N h).2 with
    | true => exact Or.inl hf
    | false =>
      apply Or.inr
      obtain ⟨j,hj⟩ := ho
      let k : Finset.Iic N := ⟨j.1,Finset.mem_Iic.mpr j.isLt.le⟩
      change selectedNode E ((h k).1.1) at hj
      cases hp : (h k).1.1 with
      | none => rw [hp] at hj; exact False.elim hj
      | some p =>
        rw [hp] at hj
        exact hh hf k p hp (hE p hj).1 (hE p hj).2
  have hu := (measure_mono_ae hsub).trans (measure_union_le _ _)
  rw [sourceHistory_failure_probability hwn hell hS0 hS hr hs hsS mesh N] at hu
  exact hu.trans (add_le_add le_rfl (source_completed_occurrence_le hwn hell hS0 hS hr hs hsS mesh N
    (crossingHighEvent_measurable _ _ _)))
end NumberTheoryLean.NonisolatedSelectedOccurrence


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CrossingMeshRate
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CrossingMeshRate
open _root_.Filter ExponentialMesh
open scoped Topology

theorem crossing_mesh_control {A κ : ℝ} (hA : 0 ≤ A) (hκ : 0 < κ) :
    ∀ᶠ w : ℝ in atTop,∀ N : ℕ,(N:ℝ) ≤ A*(Real.log w)^3 →
      Real.exp (4*(N:ℝ)*mesh κ w) ≤ 11/10 := by
  have hp : 0 < Real.log (11/10:ℝ) := Real.log_pos (by norm_num)
  filter_upwards [(log_power_exp_tendsto (4*A) 3 hκ).eventually (eventually_le_nhds hp),
    Real.tendsto_log_atTop.eventually_ge_atTop 0] with w hh hlog
  intro N hN
  have hb : 4*(N:ℝ)*mesh κ w ≤ Real.log (11/10:ℝ) := by
    calc
      _ ≤ (4*A*(Real.log w)^3)*Real.exp (-κ*Real.sqrt (Real.log w)) :=
        mul_le_mul (by nlinarith) (mesh_upper κ w) (mesh_pos κ w).le (by positivity)
      _ ≤ _ := hh
  exact (Real.exp_le_exp.mpr hb).trans_eq (Real.exp_log (by norm_num))
end NumberTheoryLean.CrossingMeshRate


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SourceIsolatedProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SourceIsolatedProbability
open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open ActualCoupledHistories FlaggedSourceStart SourceSelectedCompactOccupation SourceCouplingRate
open NonisolatedSelectedOccurrence NonisolatedWordOccurrence GoodCrossingVisit CrossingPrimeBin
open CanonicalCrossingTail CrossingMeshRate ExponentialMesh LowStateHorizon SourceSuccessfulTail


theorem source_nonisolated_probability_jb247_oai (D theta eps : ℝ) (hD : 0 < D)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1/2) (heps : 0 < eps) :
    ∃ κ alpha B₀ w₀ : ℝ,0 < κ ∧ 0 < alpha ∧ alpha ≤ theta ∧ 0 < B₀ ∧ 1 < w₀ ∧
    ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w → ∀ hw : 1 < w,∀ top : ℝ,∀ htop : w < top,
      ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ 1 → ∀ ell : ℝ,∀ start : Node,
      ∀ hs : Valid start.side start.ratio,1 ≤ ell → Real.log B ≤ D*Real.log w →
      start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 → Consistent start → start.cutoff=B →
      w^start.cutoff=top → ∀ E : Set (List ℕ),
      (∀ p : History w ell ((Real.log B)^2) start,p.primes ∈ E → p.node.gap ≤ theta*B ∧
        noIsolatedWord hw htop hxi B alpha (4*theta) p.primes) →
      fullSourceLaw w ell ((Real.log B)^2) start hs (mesh κ w) (sourceHorizon ((Real.log B)^2) B)
        {h | CompactPrefixOccurrence.occurs E _ h} ≤ ENNReal.ofReal eps := by
  obtain ⟨κ,hκ,hCouple⟩ := source_coupling_rate_jb247
  obtain ⟨WC,hWC,hC⟩ := hCouple κ hκ le_rfl D hD
  obtain ⟨T,hT,hTail⟩ := canonical_crossing_tail (eps/2) (by positivity)
  let alpha := isolatedAlpha theta (T+1)
  have ha : 0 < alpha ∧ alpha ≤ theta := isolated_alpha_bounds htheta (by linarith)
  have hEvents := (crossing_mesh_control (show 0 ≤ 5*D^3 by positivity) hκ).and
    (((log_power_exp_tendsto 1 0 (show 0 < κ/2 by positivity)).eventually
      (eventually_le_nhds (show 0 < eps/2 by positivity))).and
      (Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (D^2))))
  obtain ⟨W,hW⟩ := eventually_atTop.mp hEvents
  refine ⟨κ,alpha,max (Real.exp 2) (1/alpha),max WC (max normalizationThreshold W),
    hκ,ha.1,ha.2,(Real.exp_pos _).trans_le (le_max_left _ _),hWC.trans_le (le_max_left _ _),?_⟩
  intro B w hB₀ hw₀ hw top htop xi hxi hxi1 ell start hs hell hcomp hi h199 h23 hc hcut hcap E hE
  have hB : 0 < B := (Real.exp_pos _).trans_le ((le_max_left _ _).trans hB₀)
  have hlogB : 2 ≤ Real.log B := (Real.le_log_iff_exp_le hB).mpr ((le_max_left _ _).trans hB₀)
  have hnorm : normalizationThreshold ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw₀
  have he := hW w ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hw₀)
  have hlogw : 1 ≤ Real.log w := (le_max_left _ _).trans he.2.2
  have hscale := UniformBudgetRate.source_scale_bound ((le_max_right _ _).trans he.2.2) hlogB hcomp
  have hS0 : 0 ≤ (Real.log B)^2 := sq_nonneg _
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  have hrnode := SourceNodeCoordinates.source_node_bounds hB start hi h199 h23 hc hcut
  let N := sourceHorizon ((Real.log B)^2) B
  have hwidth : xi/Real.log w ≤ alpha*B := by
    have hlen : 1/alpha ≤ B := (le_max_right _ _).trans hB₀
    have hmul : 1 ≤ alpha*B := by have hh := (div_le_iff₀ ha.1).mp hlen; nlinarith
    exact (div_le_self hxi.le hlogw).trans (hxi1.trans hmul)
  have hOcc := selected_nonisolated_probability hnorm hell hS0 hscale.1 hrnode.2.1 hs hsS
    hw htop hxi hB htheta htheta1 (by linarith : 1 ≤ T) h199 hc hcut hcap
    (mesh_pos κ w) (mesh_le_one hκ.le w) N (he.1 N hscale.2) hwidth E hE
  have hf := (hC w ((le_max_left _ _).trans hw₀) ell B start hs hell hB hlogB hcomp hrnode.2.1 h23 hc hrnode.2.2.2).1 N le_rfl |>.1
  have hfail : Real.exp (-(κ/2)*Real.sqrt (Real.log w)) ≤ eps/2 := by
    simpa only [pow_zero,mul_one,one_mul] using he.2.1
  have hf' := hf.trans (ENNReal.ofReal_le_ofReal hfail)
  obtain ⟨s,hsv,hcost⟩ := even_source_cost_state hs hi
  have htyped : typedState start.side start.ratio hs=Sum.inl s := congrArg Prod.fst hcost
  have ht := hTail (Real.log start.gap) (theta*B) s (by rwa [hsv]) (by rwa [hsv]) N
  rw [← htyped] at ht
  have hh := hOcc.trans (add_le_add hf' ht)
  rw [← ENNReal.ofReal_add (by positivity : 0 ≤ eps/2) (by positivity : 0 ≤ eps/2)] at hh
  simpa only [add_halves] using hh
end NumberTheoryLean.SourceIsolatedProbability


end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.NumberTheoryLean.SourceIsolatedProbability.source_nonisolated_probability_jb247_oai := @OAI.Erdos970.NumberTheoryLean.SourceIsolatedProbability.source_nonisolated_probability_jb247_oai
