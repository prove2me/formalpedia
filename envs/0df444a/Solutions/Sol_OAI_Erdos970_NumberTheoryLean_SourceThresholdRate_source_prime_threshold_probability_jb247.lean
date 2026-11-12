-- Prove2me | solution 1 for OAI.Erdos970.NumberTheoryLean.SourceThresholdRate.source_prime_threshold_probability_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:10:56.082196+00:00
-- url     : https://prove2.me/submissions/f70e259a-fdaf-4a90-b3c1-91d7f8f7a66c

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

theorem nextExponent_pos {r t : ℝ} (hr : 0 < r) (ht : 0 < t) : 0 < nextExponent r t := by
  unfold nextExponent
  positivity

theorem nextGap_div_ratio {r t : ℝ} (ht : 0 < t) : nextGap r t / t = nextExponent r t := by
  unfold nextGap nextExponent
  field_simp

theorem nextGap_eq_cost {r t : ℝ} (ht : 0 < t) : nextGap r t = r * Real.exp (-cost t) := by
  have hx : 0 < 1 + 1 / t := by positivity
  unfold cost nextGap
  rw [Real.exp_neg, Real.exp_log hx]
  field_simp

end NumberTheoryLean.FinitePathGeometry



namespace NumberTheoryLean.ReciprocalGapExposure
open FinitePathGeometry
attribute [local instance] Classical.propDecidable

theorem potential_step_mono {a r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    potential a r ≤ potential a (nextGap r t) := by
  have hn := nextGap_pos hr ht
  have hle : nextGap r t ≤ r := by linarith [gap_exponent_conservation (r := r) ht,nextExponent_pos hr ht]
  exact min_le_min_right _ (one_div_le_one_div_of_le hn hle)

theorem selected_step_exposure {a L r t : ℝ} (ha : 0 < a) (hL : 0 ≤ L) (hr : 0 < r) (ht : 0 < t) :
    (if a ≤ nextGap r t ∧ t ≤ L then 1/nextGap r t else 0) ≤
      (L+1)*(potential a (nextGap r t)-potential a r) := by
  have hn := nextGap_pos hr ht
  have hmono := potential_step_mono (a := a) hr ht
  split_ifs with hs
  · have hnr : nextGap r t ≤ r := by linarith [gap_exponent_conservation (r := r) ht,nextExponent_pos hr ht]
    have hpnext : potential a (nextGap r t)=1/nextGap r t :=
      min_eq_left (one_div_le_one_div_of_le ha hs.1)
    have hpr : potential a r=1/r := min_eq_left (one_div_le_one_div_of_le ha (hs.1.trans hnr))
    rw [hpnext,hpr] at hmono ⊢
    have he : (t+1)*(1/nextGap r t-1/r)=1/nextGap r t := by
      unfold nextGap
      field_simp [hr.ne',ht.ne',show t+1 ≠ 0 by positivity]
      ring
    have hm := mul_le_mul_of_nonneg_right (show t+1 ≤ L+1 by linarith) (sub_nonneg.mpr hmono)
    rw [he] at hm
    exact hm
  · exact mul_nonneg (by linarith) (sub_nonneg.mpr hmono)

end NumberTheoryLean.ReciprocalGapExposure



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



namespace NumberTheoryLean.FiniteGapExposure
open FinitePathGeometry ReciprocalGapExposure
attribute [local instance] Classical.propDecidable

theorem finite_potential_telescope (N : ℕ) (f : Fin (N+1) → ℝ) :
    (∑ j : Fin N,(f j.succ-f j.castSucc))=f (Fin.last N)-f 0 := by
  have h₁ := Fin.sum_univ_succ f
  have h₂ := Fin.sum_univ_castSucc f
  rw [Finset.sum_sub_distrib]
  linarith

theorem finite_arrival_exposure {a L : ℝ} (ha : 0 < a) (hL : 0 ≤ L)
    (N : ℕ) (r : Fin (N+1) → ℝ) (t : Fin N → ℝ)
    (hr : ∀ j,0 < r j) (ht : ∀ j,0 < t j)
    (hflow : ∀ j,r j.succ=nextGap (r j.castSucc) (t j)) :
    (∑ j : Fin N,if a ≤ r j.succ ∧ t j ≤ L then 1/r j.succ else 0) ≤ (L+1)/a := by
  have hsum : (∑ j : Fin N,if a ≤ r j.succ ∧ t j ≤ L then 1/r j.succ else 0) ≤
      ∑ j : Fin N,(L+1)*(potential a (r j.succ)-potential a (r j.castSucc)) := by
    apply Finset.sum_le_sum
    intro j _
    rw [hflow j]
    exact selected_step_exposure ha hL (hr j.castSucc) (ht j)
  rw [← Finset.mul_sum,finite_potential_telescope N (fun j => potential a (r j))] at hsum
  have hn : 0 ≤ potential a (r 0) := le_min (one_div_nonneg.mpr (hr 0).le) (by positivity)
  have hu : potential a (r (Fin.last N)) ≤ 1/a := min_le_right _ _
  have hm := mul_le_mul_of_nonneg_left (show potential a (r (Fin.last N))-potential a (r 0) ≤ 1/a by linarith)
    (show 0 ≤ L+1 by linarith)
  exact hsum.trans (by simpa only [mul_one_div] using hm)

theorem finite_all_exposure {a L : ℝ} (ha : 0 < a) (hL : 0 ≤ L)
    (N : ℕ) (r s : Fin (N+1) → ℝ)
    (hr : ∀ j,0 < r j) (hs : ∀ j,0 < s j)
    (hflow : ∀ j : Fin N,r j.succ=nextGap (r j.castSucc) (s j.succ)) :
    (∑ j : Fin (N+1),if a ≤ r j ∧ s j ≤ L then 1/r j else 0) ≤ (L+2)/a := by
  have hh := finite_arrival_exposure ha hL N r (fun j => s j.succ) hr (fun j => hs j.succ) hflow
  rw [Fin.sum_univ_succ]
  have hinit : (if a ≤ r 0 ∧ s 0 ≤ L then 1/r 0 else 0) ≤ 1/a := by
    split_ifs with h
    · exact one_div_le_one_div_of_le ha h.1
    · positivity
  have he : (L+2)/a=1/a+(L+1)/a := by ring
  rw [he]
  exact add_le_add hinit hh
end NumberTheoryLean.FiniteGapExposure



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



namespace NumberTheoryLean.FiniteHistoryOccurrence
open Set MeasureTheory ProbabilityTheory FiniteHistoryTransport
variable {X : Type*} [MeasurableSpace X]

theorem atIndex_law (K : Kernel X X) [IsMarkovKernel K] (N : ℕ) (h₀ : Hist X 0) (j : Fin (N+1)) :
    (pathKernel K N h₀).map (fun h => atIndex N h j)=(K^j.1) (last 0 h₀) :=
  pathMeasure_coordinate K N j.1 (Nat.le_of_lt_succ j.isLt) h₀

theorem probability_integrable (K : Kernel X X) [IsMarkovKernel K]
    {E : Set X} (hE : MeasurableSet E) (N : ℕ) (h₀ : Hist X 0) (j : Fin (N+1)) :
    Integrable (fun h => (K (atIndex N h j) E).toReal) (pathKernel K N h₀) := by
  have hc : Measurable (fun h : Hist X N => atIndex N h j) := measurable_pi_apply _
  have hm := (K.measurable_coe hE).ennreal_toReal.comp hc
  apply (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun h => by
    change ‖(K (atIndex N h j) E).toReal‖ ≤ 1
    have hb : (K (atIndex N h j) E).toReal ≤ 1 := measureReal_le_one
    simpa only [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg] using hb)

theorem next_probability_identity (K : Kernel X X) [IsMarkovKernel K]
    {E : Set X} (hE : MeasurableSet E) (N : ℕ) (h₀ : Hist X 0) (j : Fin N) :
    (pathKernel K N h₀).real {h | atIndex N h j.succ ∈ E}=
      ∫ h,(K (atIndex N h j.castSucc) E).toReal ∂pathKernel K N h₀ := by
  have hn := atIndex_law K N h₀ j.succ
  have hp := atIndex_law K N h₀ j.castSucc
  simp only [Fin.val_succ] at hn
  simp only [Fin.val_castSucc] at hp
  have hcn : Measurable (fun h : Hist X N => atIndex N h j.succ) := measurable_pi_apply _
  have hcp : Measurable (fun h : Hist X N => atIndex N h j.castSucc) := measurable_pi_apply _
  have he : (K^(j.1+1)) (last 0 h₀) E = ∫⁻ x,K x E ∂(K^j.1) (last 0 h₀) := by
    have hh := Kernel.pow_add_apply_eq_lintegral K j.1 1 (last 0 h₀) hE
    simpa only [pow_one] using hh
  calc
    _ = ((K^(j.1+1)) (last 0 h₀) E).toReal := by
      rw [← hn,Measure.map_apply hcn hE]
      rfl
    _ = (∫⁻ x,K x E ∂(K^j.1) (last 0 h₀)).toReal := congrArg ENNReal.toReal he
    _ = ∫ x,(K x E).toReal ∂(K^j.1) (last 0 h₀) :=
      (integral_toReal (K.measurable_coe hE).aemeasurable
        (Filter.Eventually.of_forall (fun x => measure_lt_top (K x) E))).symm
    _ = _ := by
      rw [← hp,integral_map_of_stronglyMeasurable hcp
        (K.measurable_coe hE).ennreal_toReal.stronglyMeasurable]

theorem occurrence_le_integrated_hazards (K : Kernel X X) [IsMarkovKernel K]
    {E : Set X} (hE : MeasurableSet E) (N : ℕ) (h₀ : Hist X 0) :
    (pathKernel K N h₀).real (arrivalOccurrence E N) ≤
      ∫ h,∑ j : Fin N,(K (atIndex N h j.castSucc) E).toReal ∂pathKernel K N h₀ := by
  apply (measureReal_iUnion_fintype_le (fun j : Fin N => {h | atIndex N h j.succ ∈ E})).trans_eq
  simp_rw [next_probability_identity K hE N h₀]
  symm
  apply integral_finsetSum
  intro j _
  exact probability_integrable K hE N h₀ j.castSucc
end NumberTheoryLean.FiniteHistoryOccurrence



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
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_UniformCycleMoments
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.InitialRegeneration.hitOrReturn_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_CostPrefixTransport
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open OccupationBoundaries OccupationDecomposition OccupationRegeneration
open InitialOccupation FullOccupationCovariance KernelPotential

theorem stateRatio_ge_half (s : State) : (1 / 2 : ℝ) ≤ stateRatio s := by
  cases s with
  | inl s => change (1 / 2 : ℝ) ≤ s.1; linarith [s.2]
  | inr s => change (1 / 2 : ℝ) ≤ s.1; linarith [s.2]

end NumberTheoryLean.CostPrefixTransport

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_ArrivalKernelGeometry
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

theorem currentExponent_pos (v : ℝ) (z : CostState) : 0 < currentExponent v z :=
  div_pos (Real.exp_pos _) (stateRatio_pos z.1)

theorem gapValue_update (v : ℝ) (z : CostState) (s : State) :
    gapValue v (s, z.2 + cost (stateRatio s)) = nextGap (gapValue v z) (stateRatio s) := by
  rw [nextGap_eq_cost (stateRatio_pos s)]
  change Real.exp (v - (z.2 + cost (stateRatio s))) = Real.exp (v - z.2) * Real.exp (-cost (stateRatio s))
  rw [show v - (z.2 + cost (stateRatio s)) = (v - z.2) + (-cost (stateRatio s)) by ring, Real.exp_add]

theorem currentExponent_update (v : ℝ) (z : CostState) (s : State) :
    currentExponent v (s, z.2 + cost (stateRatio s)) = nextExponent (gapValue v z) (stateRatio s) := by
  change gapValue v (s, z.2 + cost (stateRatio s)) / stateRatio s = _
  rw [gapValue_update, nextGap_div_ratio (stateRatio_pos s)]

theorem stateKernel_ae_minRatio (s : State) :
    ∀ᵐ t ∂stateKernel s, minRatio (stateSide s) (stateRatio s) ≤ stateRatio t := by
  cases s with
  | inl s =>
    change ∀ᵐ t ∂stateKernel (.inl s), s.1 - 1 ≤ stateRatio t
    have h : ∀ᵐ u ∂(stateKernel (.inl s)).map stateRatio, s.1 - 1 ≤ u := by
      rw [stateKernel_even_ratio]
      exact evenKernel_ae_support s
    exact (ae_map_iff stateRatio_measurable.aemeasurable measurableSet_Ici).mp h
  | inr s =>
    change ∀ᵐ t ∂stateKernel (.inr s), max 2 (s.1 - 1) ≤ stateRatio t
    have h : ∀ᵐ u ∂(stateKernel (.inr s)).map stateRatio, max 2 (s.1 - 1) ≤ u := by
      rw [stateKernel_odd_ratio]
      exact oddKernel_ae_support s
    exact (ae_map_iff stateRatio_measurable.aemeasurable measurableSet_Ici).mp h

end NumberTheoryLean.ArrivalKernelGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_LowStateHorizon
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

theorem costKernel_time_update (z : CostState) :
    ∀ᵐ y ∂costKernel z, y.2 = z.2 + cost (stateRatio y.1) := by
  have hm : Measurable (fun s : State => (s, z.2 + cost (stateRatio s))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  have hp : MeasurableSet {y : CostState | y.2 = z.2 + cost (stateRatio y.1)} :=
    measurableSet_eq_fun measurable_snd
      (measurable_const.add (cost_measurable.comp (stateRatio_measurable.comp measurable_fst)))
  rw [costKernel_eq_map]
  apply (ae_map_iff hm.aemeasurable hp).mpr
  exact Eventually.of_forall fun _ => rfl

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeCompactWeights
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeBinMembership

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeTiltGeometry PrimeTiltPrefixes PrimeHistories
open PrimeRatioBins NormalizedPrimeBins PrimeKilledChain
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem step_consistent {w ell S : ℝ} {z : Node} {p : ℕ} (hell : 0 ≤ ell)
    (hr : 0 < z.gap) (hs : Valid z.side z.ratio) (hp : p ∈ nodeChildren w ell S z) :
    Consistent (step w z p) := by
  have hx := child_exponent_positive hell hp
  have ht := valid_pos (child_valid hs hp)
  change primeExponent w p = (z.gap-primeExponent w p)/childRatio w z.gap p
  rw [← nextGap_childRatio hr hx ht, nextGap_div_ratio ht, nextExponent_childRatio hr hx]

theorem terminal_consistent {w ell S : ℝ} {z : Node} {ps : List ℕ} (hell : 0 ≤ ell)
    (hr : 0 < z.gap) (hs : Valid z.side z.ratio) (hz : Consistent z) (hp : allowed w ell S z ps) :
    Consistent (terminal w z ps) := by
  induction ps generalizing z with
  | nil => exact hz
  | cons p ps ih =>
    rcases (allowed_cons w ell S z p ps).mp hp with ⟨hc,ht⟩
    exact ih (child_gap_positive hell hr hs hc) (child_valid hs hc) (step_consistent hell hr hs hc) ht

theorem history_consistent {w ell S : ℝ} {start : Node} (hell : 0 ≤ ell)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hc : Consistent start)
    (h : History w ell S start) : Consistent h.node :=
  terminal_consistent hell hr hs hc h.admissible

end NumberTheoryLean.PrimeBinMembership

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

theorem clipped_relative_stability {A x y c : ℝ} (hA : 0 ≤ A) (hc : 1 ≤ c)
    (hxy : x ≤ c*y) (hyx : y ≤ c*x) :
    |min A x-min A y| ≤ A*(c-1) := by
  have hnonneg : 0 ≤ A*(c-1) := mul_nonneg hA (by linarith)
  simp only [min_def]
  split_ifs <;> apply abs_le.mpr <;> constructor <;> nlinarith

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

instance jointPathLaw_probability (v mesh : ℝ) (z : CostState) (n : ℕ) :
    IsProbabilityMeasure (jointPathLaw hw hell hS0 hS hr hs hsS v mesh z n) := by
  unfold jointPathLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CommonCellSum
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ActualSupportIntervals

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open PrimeTiltGeometry ActualCouplingUpdates ContinuousKilledBins LowStateHorizon
open ArrivalKernelGeometry RegeneratingInverseBands PairedCostGrouping

theorem costKernel_lower_support (z : CostState) :
    ∀ᵐ y ∂costKernel z, minRatio (stateSide z.1) (stateRatio z.1) ≤ stateRatio y.1 := by
  have hm : Measurable (fun s : State => (s,z.2+cost (stateRatio s))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  have hP : MeasurableSet {y : CostState | minRatio (stateSide z.1) (stateRatio z.1) ≤ stateRatio y.1} :=
    measurableSet_le measurable_const (stateRatio_measurable.comp measurable_fst)
  rw [costKernel_eq_map]
  exact (ae_map_iff hm.aemeasurable hP).mpr (stateKernel_ae_minRatio z.1)

end NumberTheoryLean.ActualSupportIntervals

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_HistoryRestrictionAlgebra
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualCoupledHistories.sourceHistoryLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.ActualCoupledHistories.sourceTransition_markov _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointPathLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.continuousParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.jointKernel_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ContinuousKilledBins.continuousChain_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedSourceStart.sourceLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory Function Preorder
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures

local instance instMeasurableSingletonClassState : MeasurableSingletonClass State := by
  constructor
  intro x
  cases x with
  | inl e =>
    simpa only [image_singleton] using ((measurableSet_singleton e).inl_image :
      MeasurableSet (Sum.inl '' {e} : Set State))
  | inr o =>
    simpa only [image_singleton] using ((measurableSet_singleton o).inr_image :
      MeasurableSet (Sum.inr '' {o} : Set State))

lemma rawExtension_retains_prefix {b c : ℕ} (hbc : b ≤ c) (h : RawHistory b) :
    ∀ᵐ z ∂rawExtension b c h, rawPrefix hbc z = h := by
  have he : (rawExtension b c h).map (rawPrefix hbc) = Measure.dirac h := by
    rw [rawExtension,rawPrefix,Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ => CostState) (κ := historyKernel) h hbc,Kernel.partialTraj_self,Kernel.id_apply]
  have hd : ∀ᵐ y ∂(rawExtension b c h).map (rawPrefix hbc), y=h := by
    rw [he]
    exact ae_eq_dirac' measurable_id
  exact (ae_map_iff (rawPrefix_measurable hbc).aemeasurable (measurableSet_singleton h)).mp hd

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RawInitialEven
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualCoupledHistories.sourceHistoryLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.ActualCoupledHistories.sourceTransition_markov _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointPathLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.continuousParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.jointKernel_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ContinuousKilledBins.continuousChain_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedSourceStart.sourceLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.TransitionKernels
open NumberTheoryLean.InitialOddDraw NumberTheoryLean.InitialRegeneration

lemma rawExtension_last_step (a : ℕ) (h : RawHistory a) :
    (rawExtension a (a+1) h).map (rawLast (a+1))=costKernel (rawLast a h) := by
  have he := congrArg (fun K : Kernel (RawHistory a) CostState => K h)
    (Kernel.map_partialTraj_succ_self (X := fun _ => CostState) (κ := historyKernel) a)
  change ((rawExtension a (a+1)).map (rawLast (a+1))) h=costKernel (rawLast a h) at he
  rw [Kernel.map_apply _ (rawLast_measurable (a+1))] at he
  exact he

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_EvenThresholdGeometry
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosEvenThreshold
open Set NumberTheoryLean.FinitePathGeometry

theorem gap_eq_exponent_mul (R t : ℝ) : nextGap R t=nextExponent R t*t := by
  unfold nextGap nextExponent
  ring

theorem strip_parameters {R d t : ℝ} (hd : d ≤ 1) (ht : t ∈ thresholdStrip R d) :
    4 < R ∧ t ≤ 4 := by
  obtain ⟨ht2,hx,hlo,hhi⟩ := ht
  have hcons := gap_exponent_conservation (r:=R) (show 0 < t by linarith)
  have hm := gap_eq_exponent_mul R t
  have hlow := le_max_right (2*nextExponent R t) (nextExponent R t+2)
  have hmax : max (2*nextExponent R t) (nextExponent R t+2) ≤ 3*nextExponent R t :=
    max_le (by linarith) (by linarith)
  unfold thresholdSlack at hlo hhi
  constructor
  · linarith
  · have hprod : nextExponent R t*t ≤ nextExponent R t*4 := by nlinarith
    exact le_of_mul_le_mul_left hprod (by linarith : 0 < nextExponent R t)

end ErdosEvenThreshold

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_EvenThresholdEvent
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosEvenThreshold
open Set MeasureTheory NumberTheoryLean
open FinitePathGeometry TransitionKernels FinitePathMeasures

theorem thresholdStrip_eq_near (R d : ℝ) : thresholdStrip R d=nearThreshold R d := by
  ext t
  constructor
  · intro ht
    exact ht.2
  · rintro ⟨hx,hlo,hhi⟩
    have hm := gap_eq_exponent_mul R t
    have hlow := le_max_left (2*nextExponent R t) (nextExponent R t+2)
    have ht2 : 2 ≤ t := by
      have hh : nextExponent R t*2 ≤ nextExponent R t*t := by
        unfold thresholdSlack at hlo
        nlinarith
      exact le_of_mul_le_mul_left hh (by linarith : 0 < nextExponent R t)
    exact ⟨ht2,hx,hlo,hhi⟩

end ErdosEvenThreshold

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_TwoSidedThresholdGeometry
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.TwoSidedThresholdGeometry
open Set MeasureTheory FinitePathGeometry ErdosEvenThreshold

theorem normalizedSlack_eq_min {R t : ℝ} (hR : 0 < R) (ht : 0 < t+1) :
    normalizedSlack R t=min ((t-2)/(t+1)) ((t-1)/(t+1)-2/R) := by
  rw [normalizedSlack,thresholdSlack,← min_sub_sub_left,← min_div_div_right hR.le]
  congr 1
  · unfold nextGap nextExponent
    field_simp [hR.ne',ht.ne']
  · unfold nextGap nextExponent
    field_simp [hR.ne',ht.ne']
    ring

theorem thickStrip_cover {R delta t : ℝ} (hR : 3 ≤ R) (ht : t ∈ thickStrip R delta) :
    t ∈ Icc 2 (2+6*delta) ∪ Icc ((R+2)/(R-2)-18*delta) ((R+2)/(R-2)+18*delta) := by
  obtain ⟨ht2,ht5,hslack⟩ := ht
  have hRp : 0 < R := by linarith
  have hRm : 0 < R-2 := by linarith
  have htp : 0 < t+1 := by linarith
  have hd : 0 ≤ delta := (abs_nonneg _).trans hslack
  rw [normalizedSlack_eq_min hRp htp] at hslack
  by_cases hbranch : (t-2)/(t+1) ≤ (t-1)/(t+1)-2/R
  · rw [min_eq_left hbranch] at hslack
    have hh := (div_le_iff₀ htp).mp ((le_abs_self _).trans hslack)
    exact Or.inl ⟨ht2,by nlinarith⟩
  · rw [min_eq_right (le_of_not_ge hbranch)] at hslack
    have he : t-(R+2)/(R-2)=((t-1)/(t+1)-2/R)*((t+1)*R/(R-2)) := by
      field_simp [hRp.ne',hRm.ne',htp.ne']
      ring
    have hfac0 : 0 ≤ (t+1)*R/(R-2) := by positivity
    have hfac : (t+1)*R/(R-2) ≤ 18 := by
      apply (div_le_iff₀ hRm).mpr
      nlinarith
    have habs : |t-(R+2)/(R-2)| ≤ 18*delta := by
      rw [he,abs_mul,abs_of_nonneg hfac0]
      nlinarith [mul_le_mul hslack hfac hfac0 hd]
    exact Or.inr ⟨by linarith [(abs_le.mp habs).1],by linarith [(abs_le.mp habs).2]⟩

theorem thickStrip_measurable (R delta : ℝ) : MeasurableSet (thickStrip R delta) := by
  have hs : Measurable (normalizedSlack R) := by
    unfold normalizedSlack thresholdSlack nextGap nextExponent
    fun_prop
  exact measurableSet_Ici.inter (measurableSet_Iic.inter (measurableSet_le hs.abs measurable_const))

theorem thickStrip_volume {R delta : ℝ} (hR : 3 ≤ R) (hd : 0 ≤ delta) :
    volume (thickStrip R delta) ≤ ENNReal.ofReal (42*delta) := by
  calc
    _ ≤ volume (Icc 2 (2+6*delta) ∪ Icc ((R+2)/(R-2)-18*delta) ((R+2)/(R-2)+18*delta)) :=
      measure_mono (fun _ ht => thickStrip_cover hR ht)
    _ ≤ volume (Icc 2 (2+6*delta))+volume (Icc ((R+2)/(R-2)-18*delta) ((R+2)/(R-2)+18*delta)) :=
      measure_union_le _ _
    _ = ENNReal.ofReal (6*delta)+ENNReal.ofReal (36*delta) := by
      rw [Real.volume_Icc,Real.volume_Icc]
      congr 1 <;> congr 1 <;> ring
    _ = ENNReal.ofReal (42*delta) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
end NumberTheoryLean.TwoSidedThresholdGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_CanonicalCostCoordinates
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.ActualCoupledHistories.sourceHistoryLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.ActualCoupledHistories.sourceTransition_markov _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointPathLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.continuousParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.jointKernel_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ContinuousKilledBins.continuousChain_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedSourceStart.sourceLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.CanonicalCostCoordinates

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures FinitePathGeometry LowStateHorizon
open Erdos970Dependency.MarkedVisits

theorem raw_cost_step (k : ℕ) (h : RawHistory k) :
    ∀ᵐ y ∂rawExtension k (k+1) h,
      (rawLast (k+1) y).2 = (y ⟨k,Finset.mem_Iic.mpr k.le_succ⟩).2 +
        cost (stateRatio (rawLast (k+1) y).1) := by
  have hs : ∀ᵐ y ∂rawExtension k (k+1) h,
      (rawLast (k+1) y).2 = (rawLast k h).2 + cost (stateRatio (rawLast (k+1) y).1) := by
    apply (ae_map_iff (rawLast_measurable (k+1)).aemeasurable
      (measurableSet_eq_fun measurable_snd
        (measurable_const.add (cost_measurable.comp (stateRatio_measurable.comp measurable_fst))))).mp
    rw [rawExtension_last_step]
    exact costKernel_time_update _
  filter_upwards [hs,rawExtension_retains_prefix k.le_succ h] with y hy hp
  have he := congrFun hp (⟨k,by simp⟩ : Finset.Iic k)
  change y ⟨k,Finset.mem_Iic.mpr k.le_succ⟩ = rawLast k h at he
  rw [he]
  exact hy

theorem raw_cost_coordinate {a b k : ℕ} (hak : a ≤ k) (hkb : k < b) (h : RawHistory a) :
    ∀ᵐ y ∂rawExtension a b h,
      (y ⟨k+1,Finset.mem_Iic.mpr (by omega)⟩).2 =
        (y ⟨k,Finset.mem_Iic.mpr (by omega)⟩).2 +
          cost (stateRatio (y ⟨k+1,Finset.mem_Iic.mpr (by omega)⟩).1) := by
  have hm : MeasurableSet {y : RawHistory (k+1) |
      (rawLast (k+1) y).2 = (y ⟨k,Finset.mem_Iic.mpr k.le_succ⟩).2 +
        cost (stateRatio (rawLast (k+1) y).1)} :=
    measurableSet_eq_fun (measurable_snd.comp (rawLast_measurable _))
      ((measurable_snd.comp (measurable_pi_apply _)).add
        (cost_measurable.comp (stateRatio_measurable.comp
          (measurable_fst.comp (rawLast_measurable _)))))
  have he : (rawExtension a b h).map (rawPrefix (show k+1 ≤ b by omega)) = rawExtension a (k+1) h :=
    Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ => CostState) (κ := historyKernel) h (by omega)
  have ht : ∀ᵐ y ∂rawExtension a (k+1) h,
      (rawLast (k+1) y).2 = (y ⟨k,Finset.mem_Iic.mpr k.le_succ⟩).2 +
        cost (stateRatio (rawLast (k+1) y).1) := by
    have hc : rawExtension a (k+1) = rawExtension k (k+1) ∘ₖ rawExtension a k :=
      (Kernel.partialTraj_comp_partialTraj hak (by omega)).symm
    rw [hc]
    exact Kernel.ae_comp_of_ae_ae hm (Eventually.of_forall (raw_cost_step k))
  rw [← he] at ht
  exact (ae_map_iff (rawPrefix_measurable (show k+1 ≤ b by omega)).aemeasurable hm).mp ht

end NumberTheoryLean.CanonicalCostCoordinates

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

section

namespace NumberTheoryLean.CanonicalGapExposure
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures FiniteGapExposure ArrivalKernelGeometry RegeneratingInverseBands
open CanonicalCostCoordinates Erdos970Dependency.MarkedVisits
attribute [local instance] Classical.propDecidable

theorem canonical_gap_steps (v : ℝ) (s : State) (N : ℕ) :
    ∀ᵐ h ∂finitePathMeasure s N,∀ j : Fin N,
      gapValue v (coordinate N h j.succ)=
        nextGap (gapValue v (coordinate N h j.castSucc)) (stateRatio (coordinate N h j.succ).1) := by
  have hall : ∀ᵐ h ∂finitePathMeasure s N,∀ j : Fin N,
      (coordinate N h j.succ).2=(coordinate N h j.castSucc).2+cost (stateRatio (coordinate N h j.succ).1) := by
    apply ae_all_iff.mpr
    intro j
    exact raw_cost_coordinate (Nat.zero_le _) j.isLt (fun _ => (s,0))
  filter_upwards [hall] with h hh
  intro j
  have he : coordinate N h j.succ=((coordinate N h j.succ).1,
      (coordinate N h j.castSucc).2+cost (stateRatio (coordinate N h j.succ).1)) := Prod.ext rfl (hh j)
  calc
    _ = gapValue v ((coordinate N h j.succ).1,
      (coordinate N h j.castSucc).2+cost (stateRatio (coordinate N h j.succ).1)) := congrArg _ he
    _ = _ := gapValue_update v (coordinate N h j.castSucc) (coordinate N h j.succ).1

theorem canonical_exposure_bound (v : ℝ) {a L : ℝ} (ha : 0 < a) (hL : 0 ≤ L)
    (s : State) (N : ℕ) :
    ∀ᵐ h ∂finitePathMeasure s N,pathExposure v a L N h ≤ (L+2)/a := by
  filter_upwards [canonical_gap_steps v s N] with h hh
  exact finite_all_exposure ha hL N (fun j => gapValue v (coordinate N h j))
    (fun j => stateRatio (coordinate N h j).1) (fun _ => Real.exp_pos _)
    (fun j => valid_pos (stateRatio_valid _)) hh

end NumberTheoryLean.CanonicalGapExposure

end

section

namespace NumberTheoryLean.CanonicalEvenArrivalSupport
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures FiniteHistoryTransport FiniteHistoryOccurrence
open ActualCouplingUpdates ActualSupportIntervals CanonicalGapExposure

theorem evenArrivalSupport_measurable : MeasurableSet {y | evenArrivalSupport y} := by
  have he : {y : CostState | evenArrivalSupport y}=
      {y : CostState | stateSide y.1=.even}ᶜ ∪ {y | 2 ≤ stateRatio y.1} := by
    ext y
    simp only [evenArrivalSupport,Set.mem_ofPred_eq,Set.mem_union,Set.mem_compl_iff]
    tauto
  rw [he]
  exact (measurable_fst (side_set_measurable .even)).compl.union
    (measurableSet_le measurable_const (stateRatio_measurable.comp measurable_fst))

theorem costKernel_even_output (z : CostState) : ∀ᵐ y ∂costKernel z,evenArrivalSupport y := by
  filter_upwards [costKernel_follows z,costKernel_lower_support z] with y hy hmin
  intro he
  cases hi : stateSide z.1 with
  | even =>
    have hh := hy.2
    rw [hi,he] at hh
    exact False.elim (Side.noConfusion hh)
  | odd =>
    rw [hi] at hmin
    exact (le_max_left (2:ℝ) _).trans hmin

theorem path_arrival_support {X : Type*} [MeasurableSpace X]
    (K : Kernel X X) [IsMarkovKernel K] {P : X → Prop} (hP : MeasurableSet {x | P x})
    (hOut : ∀ x,∀ᵐ y ∂K x,P y) (N : ℕ) (h₀ : Hist X 0) :
    ∀ᵐ h ∂pathKernel K N h₀,∀ j : Fin N,P (atIndex N h j.succ) := by
  apply ae_all_iff.mpr
  intro j
  have hm : Measurable (fun h : Hist X N => atIndex N h j.succ) := measurable_pi_apply _
  apply (ae_map_iff hm.aemeasurable hP).mp
  rw [atIndex_law]
  have he : K^(j.1+1)=K ∘ₖ (K^j.1) := by
    simpa only [Nat.add_comm,pow_one] using Kernel.pow_add K 1 j.1
  change ∀ᵐ y ∂(K^(j.1+1)) (last 0 h₀),P y
  rw [he]
  exact Kernel.ae_comp_of_ae_ae hP (Filter.Eventually.of_forall hOut)

theorem canonical_even_arrivals (s : State) (N : ℕ) :
    ∀ᵐ h ∂finitePathMeasure s N,∀ j : Fin N,
      stateSide (coordinate N h j.succ).1=.even → 2 ≤ stateRatio (coordinate N h j.succ).1 :=
  path_arrival_support costKernel evenArrivalSupport_measurable costKernel_even_output N (fun _ => (s,0))
end NumberTheoryLean.CanonicalEvenArrivalSupport

end

section

namespace NumberTheoryLean.CoupledEvenArrivalSupport
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures FiniteHistoryTransport CanonicalGapExposure
open FiniteHistoryOccurrence
open CanonicalEvenArrivalSupport CanonicalCoupledHistories CemeteryHistoryMap LiveKilledPrefixes
open ActualCouplingUpdates ActualCoupledHistories ActualProcessCoupling
open PrimeHistories PrimeKilledChain LowStateHorizon

theorem killed_even_coordinate {E : Set CostState} (hE : MeasurableSet E)
    (s : State) (N : ℕ) (j : Fin N) :
    ∀ᵐ h ∂(finitePathMeasure s N).map (killHist E N),
      liftPredicate evenArrivalSupport (atIndex N h j.succ) := by
  have hP : MeasurableSet {h : Hist (CemeteryKernel.Space CostState) N |
      liftPredicate evenArrivalSupport (atIndex N h j.succ)} :=
    (measurable_pi_apply _) (liftPredicate_measurable evenArrivalSupport_measurable)
  apply (ae_map_iff (killHist_measurable hE N).aemeasurable hP).mpr
  filter_upwards [canonical_even_arrivals s N] with h hh
  cases hy : atIndex N (killHist E N h) j.succ with
  | inr u => trivial
  | inl y =>
    have horig := (live_coordinate_original E N (j.1+1) (by have := j.isLt; omega) h y hy).1
    change evenArrivalSupport y
    rw [← horig]
    exact hh j

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem sourceHistory_even_arrivals (mesh : ℝ) (N : ℕ) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      ∀ j : Fin N,∀ y : CostState,
        (h ⟨j.1+1,Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩).1.2=Sum.inl y →
        stateSide y.1=.even → 2 ≤ stateRatio y.1 := by
  have hall : ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,∀ j : Fin N,
      liftPredicate evenArrivalSupport ((h ⟨j.1+1,Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩).1.2) := by
    apply ae_all_iff.mpr
    intro j
    have hP : MeasurableSet {h : Hist (CemeteryKernel.Space CostState) N |
        liftPredicate evenArrivalSupport (atIndex N h j.succ)} :=
      (measurable_pi_apply _) (liftPredicate_measurable evenArrivalSupport_measurable)
    have hh : ∀ᵐ h ∂(sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N).map
        (mapHist (fun q => q.1.2) N),liftPredicate evenArrivalSupport (atIndex N h j.succ) := by
      rw [sourceHistoryLaw_canonical hw hell hS0 hS hr hs hsS mesh N]
      exact killed_even_coordinate (lowDomain_measurable _ _ _) _ N j
    exact (ae_map_iff (mapHist_measurable (by exact measurable_snd.comp measurable_fst) N).aemeasurable hP).mp hh
  filter_upwards [hall] with h hh
  intro j y hy he
  have hp := hh j
  rw [hy] at hp
  exact hp he
end NumberTheoryLean.CoupledEvenArrivalSupport

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_TwoSidedThresholdKernel
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.TwoSidedThresholdKernel
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures TransitionKernels KernelDensityBridge DerivativeWeights
open TwoSidedThresholdGeometry ErdosEvenThreshold CanonicalGapExposure RegeneratingInverseBands
attribute [local instance] Classical.propDecidable

theorem thickDensityBound_pos : 0 < thickDensityBound := by
  have he := phiEven_pos (by norm_num : (1:ℝ)<2)
  have ho := phiOdd_pos 6
  unfold thickDensityBound
  positivity

theorem thickConstant_pos : 0 < thickConstant := by
  unfold thickConstant
  exact mul_pos (by norm_num) thickDensityBound_pos

theorem oddDensity_thick_bound (s : OddState) {t : ℝ} (ht2 : 2 ≤ t) (ht5 : t ≤ 5) :
    oddDensity s t ≤ thickDensityBound := by
  change (if max 2 (s.1-1) ≤ t then W t*phiEven t/phiOdd s.1 else 0) ≤ _
  by_cases hsup : max 2 (s.1-1) ≤ t
  · rw [ite_eq_left hsup]
    have hs6 : s.1 ≤ 6 := by linarith [le_max_right (2:ℝ) (s.1-1)]
    have ht0 : 0 < t := by linarith
    have hW : W t ≤ (3:ℝ)/2 := by
      unfold W
      apply (div_le_div_iff₀ (sq_pos_of_pos ht0) (by norm_num : (0:ℝ)<2)).mpr
      nlinarith
    have hphi := phiEven_strictAntiOn.antitoneOn (by norm_num : (2:ℝ) ∈ Ioi 1)
      (by change 1 < t; linarith : t ∈ Ioi (1:ℝ)) ht2
    have hden := phiOdd_antitone hs6
    have hnum := mul_le_mul hW hphi (phiEven_pos (by linarith : 1 < t)).le (by norm_num : (0:ℝ)≤3/2)
    calc
      _ ≤ ((3:ℝ)/2*phiEven 2)/phiOdd s.1 := div_le_div_of_nonneg_right hnum (phiOdd_pos _).le
      _ ≤ ((3:ℝ)/2*phiEven 2)/phiOdd 6 :=
        div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (phiEven_pos (by norm_num)).le) (phiOdd_pos 6) hden
      _ = _ := rfl
  · rw [ite_eq_right hsup]
    exact thickDensityBound_pos.le

theorem oddKernel_thick_bound (s : OddState) {R delta : ℝ} (hR : 3 ≤ R) (hd : 0 ≤ delta) :
    oddKernel s (thickStrip R delta) ≤ ENNReal.ofReal (thickConstant*delta) := by
  rw [oddKernel_apply]
  calc
    _ ≤ ∫⁻ _t in thickStrip R delta,ENNReal.ofReal thickDensityBound := by
      apply setLIntegral_mono measurable_const
      intro t ht
      exact ENNReal.ofReal_le_ofReal (oddDensity_thick_bound s ht.1 ht.2.1)
    _ = ENNReal.ofReal thickDensityBound*volume (thickStrip R delta) := by simp
    _ ≤ ENNReal.ofReal thickDensityBound*ENNReal.ofReal (42*delta) :=
      mul_le_mul_right (thickStrip_volume hR hd) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul thickDensityBound_pos.le]
      congr 1
      unfold thickConstant
      ring

theorem oddToEven_thick_bound (s : OddState) {R delta : ℝ} (hR : 3 ≤ R) (hd : 0 ≤ delta) :
    oddToEven s ((Subtype.val : EvenState → ℝ) ⁻¹' thickStrip R delta) ≤ ENNReal.ofReal (thickConstant*delta) := by
  have hh := oddKernel_thick_bound s hR hd
  rw [← oddToEven_map_ratio s,Measure.map_apply measurable_subtype_coe (thickStrip_measurable R delta)] at hh
  exact hh

theorem oddToEven_thick_zero_high_parent (s : OddState) {R delta : ℝ} (hs : 6 < s.1) :
    oddToEven s ((Subtype.val : EvenState → ℝ) ⁻¹' thickStrip R delta)=0 := by
  have he : oddToEven s ((Subtype.val : EvenState → ℝ) ⁻¹' thickStrip R delta)=oddKernel s (thickStrip R delta) := by
    rw [← oddToEven_map_ratio s,Measure.map_apply measurable_subtype_coe (thickStrip_measurable R delta)]
  rw [he,oddKernel_apply]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (thickStrip_measurable R delta)] with t ht
  have hn : ¬max 2 (s.1-1) ≤ t := by linarith [le_max_right (2:ℝ) (s.1-1),ht.2.1]
  have hz : oddDensity s t=0 := ite_eq_right hn
  simp only [hz,ENNReal.ofReal_zero,Pi.zero_apply]
end NumberTheoryLean.TwoSidedThresholdKernel

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_TwoSidedThresholdHazard
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.TwoSidedThresholdHazard
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures TransitionKernels
open TwoSidedThresholdGeometry TwoSidedThresholdKernel CanonicalGapExposure RegeneratingInverseBands
attribute [local instance] Classical.propDecidable

theorem thickHazard_exposure (s : State) {R d e : ℝ}
    (hR : 0 < R) (hd : 0 ≤ d) (he : 0 ≤ e) :
    thickHazard R d e s ≤ thickConstant*d*(if 3 ≤ R ∧ stateRatio s ≤ 6 then 1/R else 0)+thickConstant*e := by
  have hC := thickConstant_pos
  cases s with
  | inl s =>
    change 0 ≤ _
    split_ifs <;> positivity
  | inr s =>
    by_cases hR3 : 3 ≤ R
    · by_cases hs : s.1 ≤ 6
      · simp only [thickHazard,ite_eq_left hR3]
        split_ifs with hguard
        · have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
            (oddToEven_thick_bound s hR3 (show 0 ≤ d/R+e by positivity))
          rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ thickConstant*(d/R+e))] at hh
          calc
            _ ≤ thickConstant*(d/R+e) := hh
            _ = _ := by ring
        · exact (hguard ⟨hR3,hs⟩).elim
      · rw [thickHazard,ite_eq_left hR3,oddToEven_thick_zero_high_parent s (lt_of_not_ge hs)]
        simp only [ENNReal.toReal_zero,stateRatio,Sum.elim_inr,hs,and_false,ite_false, if_false,mul_zero,zero_add]
        positivity
    · rw [thickHazard,ite_eq_right hR3]
      simp only [hR3,false_and,ite_false, if_false,mul_zero,zero_add]
      positivity

theorem canonical_total_thick_hazard (v : ℝ) {d e : ℝ} (hd : 0 ≤ d) (he : 0 ≤ e)
    (s : State) (N : ℕ) :
    ∀ᵐ h ∂finitePathMeasure s N,
      (∑ j : Fin (N+1),thickHazard (gapValue v (coordinate N h j)) d e (coordinate N h j).1) ≤
        thickConstant*((8/3:ℝ)*d+((N:ℝ)+1)*e) := by
  filter_upwards [canonical_exposure_bound v (by norm_num : (0:ℝ)<3) (by norm_num : (0:ℝ)≤6) s N] with h hh
  have hsum : (∑ j : Fin (N+1),thickHazard (gapValue v (coordinate N h j)) d e (coordinate N h j).1) ≤
      thickConstant*d*pathExposure v 3 6 N h+((N:ℝ)+1)*(thickConstant*e) := by
    calc
      _ ≤ ∑ j : Fin (N+1),(thickConstant*d*(if 3 ≤ gapValue v (coordinate N h j) ∧
          stateRatio (coordinate N h j).1 ≤ 6 then 1/gapValue v (coordinate N h j) else 0)+thickConstant*e) := by
        apply Finset.sum_le_sum
        intro j _
        exact thickHazard_exposure _ (Real.exp_pos _) hd he
      _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum]; simp [pathExposure,Nat.cast_add,Nat.cast_one]
  have hm := mul_le_mul_of_nonneg_left hh (mul_nonneg thickConstant_pos.le hd)
  calc
    _ ≤ thickConstant*d*((6+2)/3)+((N:ℝ)+1)*(thickConstant*e) := by linarith
    _ = _ := by ring
end NumberTheoryLean.TwoSidedThresholdHazard

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_TwoSidedThresholdArrival
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.TwoSidedThresholdArrival
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures TransitionKernels ArrivalKernelGeometry RegeneratingInverseBands
open TwoSidedThresholdGeometry TwoSidedThresholdKernel TwoSidedThresholdHazard
open RepresentativeStopGeometry ActualCouplingUpdates

theorem reconstructedParent_measurable (v : ℝ) : Measurable (reconstructedParent v) :=
  (gapValue_measurable v).add (currentExponent_measurable v)

theorem reconstructedParent_update (v : ℝ) (z : CostState) (s : State) :
    reconstructedParent v (s,z.2+cost (stateRatio s))=gapValue v z := by
  rw [reconstructedParent,gapValue_update,currentExponent_update]
  exact gap_exponent_conservation (valid_pos (stateRatio_valid s))

theorem thickArrival_measurable (v d e : ℝ) : MeasurableSet (thickArrival v d e) := by
  have hr := reconstructedParent_measurable v
  have ht : Measurable (fun y : CostState => stateRatio y.1) := stateRatio_measurable.comp measurable_fst
  have hs : Measurable (fun y : CostState => normalizedSlack (reconstructedParent v y) (stateRatio y.1)) := by
    unfold normalizedSlack ErdosEvenThreshold.thresholdSlack nextGap nextExponent
    exact (((hr.mul ht).div (ht.add_const 1)).sub
      (((measurable_const.mul (hr.div (ht.add_const 1)))).max ((hr.div (ht.add_const 1)).add_const 2))).div hr
  exact (measurable_fst (side_set_measurable .even)).inter
    ((measurableSet_le measurable_const hr).inter
      ((measurableSet_le measurable_const ht).inter ((measurableSet_le ht measurable_const).inter
        (measurableSet_le hs.abs ((measurable_const.div hr).add_const e)))))

theorem thickArrival_update (v d e : ℝ) (z : CostState) (s : State) :
    (s,z.2+cost (stateRatio s)) ∈ thickArrival v d e ↔ stateSide s=.even ∧
      3 ≤ gapValue v z ∧ stateRatio s ∈ thickStrip (gapValue v z) (d/gapValue v z+e) := by
  change stateSide s=.even ∧ _ ↔ _
  rw [reconstructedParent_update]

theorem thickHazard_eq_actual (v d e : ℝ) (z : CostState) :
    thickHazard (gapValue v z) d e z.1=(costKernel z (thickArrival v d e)).toReal := by
  rw [costKernel_apply z (thickArrival_measurable v d e)]
  rcases z with ⟨s,T⟩
  cases s with
  | inl s =>
    change 0=(evenBranch s {t | (t,T+cost (stateRatio t)) ∈ thickArrival v d e}).toReal
    rw [evenBranch,Kernel.map_apply' _ measurable_inr _]
    · have he : Sum.inr ⁻¹' {t : State | (t,T+cost (stateRatio t)) ∈ thickArrival v d e}=∅ := by
        ext t
        change (Sum.inr t,T+cost (stateRatio (Sum.inr t))) ∈ thickArrival v d e ↔ False
        rw [thickArrival_update v d e ((Sum.inl s),T)]
        simp [stateSide]
      rw [he,measure_empty,ENNReal.toReal_zero]
    · exact (measurable_id.prodMk
        (measurable_const.add (cost_measurable.comp stateRatio_measurable))) (thickArrival_measurable v d e)
  | inr s =>
    change _=(oddBranch s {t | (t,T+cost (stateRatio t)) ∈ thickArrival v d e}).toReal
    rw [oddBranch,Kernel.map_apply' _ measurable_inl _]
    · by_cases hR : 3 ≤ gapValue v ((Sum.inr s),T)
      · have he : Sum.inl ⁻¹' {t : State | (t,T+cost (stateRatio t)) ∈ thickArrival v d e}=
            (Subtype.val : EvenState → ℝ) ⁻¹' thickStrip (gapValue v ((Sum.inr s),T)) (d/gapValue v ((Sum.inr s),T)+e) := by
          ext t
          change (Sum.inl t,T+cost (stateRatio (Sum.inl t))) ∈ thickArrival v d e ↔ _
          rw [thickArrival_update v d e ((Sum.inr s),T)]
          simp only [stateSide,stateRatio,Sum.elim_inl,hR,true_and,Set.mem_preimage]
        rw [he,thickHazard,ite_eq_left hR]
      · have he : Sum.inl ⁻¹' {t : State | (t,T+cost (stateRatio t)) ∈ thickArrival v d e}=∅ := by
          ext t
          change (Sum.inl t,T+cost (stateRatio (Sum.inl t))) ∈ thickArrival v d e ↔ False
          rw [thickArrival_update v d e ((Sum.inr s),T)]
          simp only [hR,false_and,and_false]
        rw [he,measure_empty,ENNReal.toReal_zero,thickHazard,ite_eq_right hR]
    · exact (measurable_id.prodMk
        (measurable_const.add (cost_measurable.comp stateRatio_measurable))) (thickArrival_measurable v d e)
end NumberTheoryLean.TwoSidedThresholdArrival

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_TwoSidedThresholdOccurrence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.TwoSidedThresholdOccurrence
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures FiniteHistoryTransport FiniteHistoryOccurrence
open ArrivalKernelGeometry RegeneratingInverseBands CanonicalGapExposure
open TwoSidedThresholdArrival TwoSidedThresholdHazard TwoSidedThresholdKernel

theorem canonical_thick_occurrence_bound (v : ℝ) {d e : ℝ} (hd : 0 ≤ d) (he : 0 ≤ e)
    (s : State) (N : ℕ) :
    (finitePathMeasure s N).real (thickOccurrence v d e N) ≤
      thickConstant*((8/3:ℝ)*d+((N:ℝ)+1)*e) := by
  let E := thickArrival v d e
  have hE : MeasurableSet E := thickArrival_measurable v d e
  have hu := occurrence_le_integrated_hazards costKernel hE N (fun _ => (s,0))
  change (finitePathMeasure s N).real (thickOccurrence v d e N) ≤
    ∫ h,∑ j : Fin N,(costKernel (coordinate N h j.castSucc) E).toReal ∂finitePathMeasure s N at hu
  have hi : Integrable (fun h => ∑ j : Fin N,(costKernel (coordinate N h j.castSucc) E).toReal)
      (finitePathMeasure s N) := by
    apply integrable_finsetSum
    intro j _
    exact probability_integrable costKernel hE N (fun _ => (s,0)) j.castSucc
  have hb : ∀ᵐ h ∂finitePathMeasure s N,
      (∑ j : Fin N,(costKernel (coordinate N h j.castSucc) E).toReal) ≤
        thickConstant*((8/3:ℝ)*d+((N:ℝ)+1)*e) := by
    filter_upwards [canonical_total_thick_hazard v hd he s N] with h hh
    rw [Fin.sum_univ_castSucc] at hh
    have hn : 0 ≤ thickHazard (gapValue v (coordinate N h (Fin.last N))) d e (coordinate N h (Fin.last N)).1 := by
      rw [thickHazard_eq_actual]
      exact ENNReal.toReal_nonneg
    have hsum : (∑ j : Fin N,(costKernel (coordinate N h j.castSucc) E).toReal)=
        ∑ j : Fin N,thickHazard (gapValue v (coordinate N h j.castSucc)) d e (coordinate N h j.castSucc).1 := by
      apply Finset.sum_congr rfl
      intro j _
      exact (thickHazard_eq_actual v d e _).symm
    rw [hsum]
    linarith
  have hh := integral_mono_ae hi (integrable_const (thickConstant*((8/3:ℝ)*d+((N:ℝ)+1)*e))) hb
  have hconst : (∫ _h : Hist CostState N,thickConstant*((8/3:ℝ)*d+((N:ℝ)+1)*e) ∂finitePathMeasure s N)=
      thickConstant*((8/3:ℝ)*d+((N:ℝ)+1)*e) := by simp
  rw [hconst] at hh
  exact hu.trans hh
end NumberTheoryLean.TwoSidedThresholdOccurrence

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_TwoSidedThresholdStability
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.TwoSidedThresholdStability
open FinitePathGeometry NearbyParentGeometry TwoSidedThresholdGeometry ErdosEvenThreshold

theorem reciprocal_lipschitz_one {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |1/x-1/y| ≤ |x-y| := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have he : 1/x-1/y=(y-x)/(x*y) := by field_simp
  rw [he,abs_div,abs_of_pos (mul_pos hx0 hy0),abs_sub_comm y x]
  apply div_le_self (abs_nonneg _)
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]

theorem reciprocal_log_gap_error {R Q D : ℝ} (hR : 3 ≤ R) (hQ : 3 ≤ Q)
    (hlog : |Real.log R-Real.log Q| ≤ D) : |1/R-1/Q| ≤ Real.exp D-1 := by
  have hR0 : 0 < R := by linarith
  have hQ0 : 0 < Q := by linarith
  have hD : 0 ≤ D := (abs_nonneg _).trans hlog
  have hc : 1 ≤ Real.exp D := Real.one_le_exp_iff.mpr hD
  have hrel := log_gap_relative hR0 hQ0 hlog
  have hxy : 1/R ≤ Real.exp D*(1/Q) := by
    rw [mul_one_div]
    apply (div_le_div_iff₀ hR0 hQ0).mpr
    simpa only [one_mul] using hrel.2
  have hyx : 1/Q ≤ Real.exp D*(1/R) := by
    rw [mul_one_div]
    apply (div_le_div_iff₀ hQ0 hR0).mpr
    simpa only [one_mul] using hrel.1
  have hh := clipped_relative_stability (A := 1/3) (by norm_num) hc hxy hyx
  have hRi : 1/R ≤ (1/3:ℝ) := one_div_le_one_div_of_le (by norm_num) hR
  have hQi : 1/Q ≤ (1/3:ℝ) := one_div_le_one_div_of_le (by norm_num) hQ
  rw [min_eq_right hRi,min_eq_right hQi] at hh
  linarith

theorem normalizedSlack_stability {R Q t u h G : ℝ}
    (hR : 0 < R) (hQ : 0 < Q) (ht : 2 ≤ t) (hu : 2 ≤ u)
    (hclose : |t-u| ≤ h) (hgap : |1/R-1/Q| ≤ G) :
    |normalizedSlack R t-normalizedSlack Q u| ≤ 3*h+2*G := by
  have ht0 : 0 < t+1 := by linarith
  have hu0 : 0 < u+1 := by linarith
  have hh0 : 0 ≤ h := (abs_nonneg _).trans hclose
  have hG0 : 0 ≤ G := (abs_nonneg _).trans hgap
  have hi : |1/(t+1)-1/(u+1)| ≤ h := by
    have hh := reciprocal_lipschitz_one (x := t+1) (y := u+1) (by linarith) (by linarith)
    have hh' : |1/(t+1)-1/(u+1)| ≤ |t-u| := by simpa only [add_sub_add_right_eq_sub] using hh
    exact hh'.trans hclose
  have hA : |(t-2)/(t+1)-(u-2)/(u+1)| ≤ 3*h := by
    have he : (t-2)/(t+1)-(u-2)/(u+1)= -3*(1/(t+1)-1/(u+1)) := by
      field_simp [ht0.ne',hu0.ne']
      ring
    rw [he,abs_mul]
    norm_num
    simpa only [one_div] using hi
  have hB : |((t-1)/(t+1)-2/R)-((u-1)/(u+1)-2/Q)| ≤ 2*h+2*G := by
    have he : ((t-1)/(t+1)-2/R)-((u-1)/(u+1)-2/Q)=
        -2*(1/(t+1)-1/(u+1))-2*(1/R-1/Q) := by
      field_simp [ht0.ne',hu0.ne',hR.ne',hQ.ne']
      ring
    rw [he]
    calc
      _ ≤ |-2*(1/(t+1)-1/(u+1))|+|2*(1/R-1/Q)| := abs_sub _ _
      _ = 2*|1/(t+1)-1/(u+1)|+2*|1/R-1/Q| := by rw [abs_mul,abs_mul]; norm_num
      _ ≤ _ := by linarith
  rw [normalizedSlack_eq_min hR ht0,normalizedSlack_eq_min hQ hu0]
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by linarith) (by linarith))

theorem coupled_near_to_thick {R Q t u d h D : ℝ}
    (hQ : 0 < Q) (hu : 2 ≤ u) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hnear : t ∈ nearThreshold R d) (hclose : |t-u| ≤ h) (hsmall : h ≤ 1)
    (hlog : |Real.log R-Real.log Q| ≤ D) (hexp : Real.exp D ≤ 4/3) :
    3 ≤ Q ∧ u ∈ thickStrip Q (d/Q+3*h+3*(Real.exp D-1)) := by
  have hs : t ∈ thresholdStrip R d := (thresholdStrip_eq_near R d).symm ▸ hnear
  have hpar := strip_parameters hd1 hs
  have hR0 : 0 < R := by linarith [hpar.1]
  have hrel := log_gap_relative hR0 hQ hlog
  have hQ3 : 3 ≤ Q := by nlinarith [hrel.1,mul_le_mul_of_nonneg_right hexp hQ.le]
  have hR3 : 3 ≤ R := by linarith [hpar.1]
  have hG := reciprocal_log_gap_error hR3 hQ3 hlog
  have hG0 : 0 ≤ Real.exp D-1 := (abs_nonneg _).trans hG
  have hstab := normalizedSlack_stability hR0 hQ hs.1 hu hclose hG
  have hnorm : |normalizedSlack R t| ≤ d/R := by
    rw [normalizedSlack,abs_div,abs_of_pos hR0,abs_of_nonneg hnear.2.1]
    exact div_le_div_of_nonneg_right hnear.2.2 hR0.le
  have hdR : d/R ≤ d/Q+(Real.exp D-1) := by
    have hh := mul_le_mul_of_nonneg_left ((le_abs_self (1/R-1/Q)).trans hG) hd0
    have hc := mul_le_mul_of_nonneg_right hd1 hG0
    rw [mul_sub,mul_one_div,mul_one_div] at hh
    linarith
  refine ⟨hQ3,hu,by linarith [(abs_le.mp hclose).1,hpar.2],?_⟩
  have hh := abs_add_le (normalizedSlack Q u-normalizedSlack R t) (normalizedSlack R t)
  rw [sub_add_cancel,abs_sub_comm (normalizedSlack Q u)] at hh
  linarith
end NumberTheoryLean.TwoSidedThresholdStability

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SourceThresholdCoupling
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReconstructedParentCoupling
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeBinMembership
open RepresentativeStopGeometry NearbyParentGeometry ActualFlagInvariant
open TwoSidedThresholdStability TwoSidedThresholdArrival TwoSidedThresholdGeometry
open ArrivalKernelGeometry RegeneratingInverseBands ErdosEvenThreshold

theorem node_parent_reconstruction (z : Node) (hc : Consistent z) (hs : 0 < z.ratio) :
    nextExponent (z.gap+z.cutoff) z.ratio=z.cutoff ∧ nextGap (z.gap+z.cutoff) z.ratio=z.gap := by
  have he : z.cutoff=z.gap/z.ratio := hc
  constructor
  · rw [he]
    unfold nextExponent
    field_simp [hs.ne',show z.ratio+1 ≠ 0 by positivity]
  · rw [he]
    unfold nextGap
    field_simp [hs.ne',show z.ratio+1 ≠ 0 by positivity]

theorem node_near_reconstruction {d : ℝ} (z : Node) (hc : Consistent z) (hs : 0 < z.ratio)
    (hn : primeNearThreshold d z) : z.ratio ∈ nearThreshold (z.gap+z.cutoff) d := by
  have hg := node_parent_reconstruction z hc hs
  change 1 < nextExponent (z.gap+z.cutoff) z.ratio ∧
    0 ≤ thresholdSlack (z.gap+z.cutoff) z.ratio ∧ thresholdSlack (z.gap+z.cutoff) z.ratio ≤ d
  rw [thresholdSlack,hg.1,hg.2]
  exact hn.2

theorem log_reconstructed_parent {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    Real.log (r+r/t)=Real.log r+cost t := by
  have he : r+r/t=r*(1+1/t) := by ring
  rw [he,Real.log_mul hr.ne' (show 1+1/t ≠ 0 by positivity)]
  rfl

theorem reconstructed_log_stability {r q t u D h : ℝ} (hr : 0 < r) (hq : 0 < q)
    (ht : (1/2:ℝ) ≤ t) (hu : (1/2:ℝ) ≤ u)
    (hgap : |Real.log r-Real.log q| ≤ D) (hratio : |t-u| ≤ h) :
    |Real.log (r+r/t)-Real.log (q+q/u)| ≤ D+4*h := by
  rw [log_reconstructed_parent hr (by linarith),log_reconstructed_parent hq (by linarith)]
  have he : (Real.log r+cost t)-(Real.log q+cost u)=
      (Real.log r-Real.log q)+(cost t-cost u) := by ring
  rw [he]
  have hc := cost_stability ht hu
  exact (abs_add_le _ _).trans (by linarith)

theorem good_prime_near_thick {w ell S v mesh d : ℝ} {start : Node}
    (hell : 0 ≤ ell) (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hc : Consistent start)
    (n : ℕ) (h : History w ell S start) (y : CostState)
    (hgood : GoodAt v mesh n (some h,Sum.inl y))
    (hy2 : 2 ≤ stateRatio y.1) (hmesh : mesh ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hexp : Real.exp (4*((n:ℝ)+1)*mesh) ≤ 4/3) (hne : primeNearThreshold d h.node) :
    y ∈ thickArrival v d (3*mesh+3*(Real.exp (4*((n:ℝ)+1)*mesh)-1)) := by
  have hcons := history_consistent hell hr hs hc h
  have hvalid := terminal_valid hs h.admissible
  have hpos : 0 < h.node.gap := terminal_gap_positive hell hr hs h.admissible
  have hratio : 0 < h.node.ratio := valid_pos hvalid
  have hnear := node_near_reconstruction h.node hcons hratio hne
  have htwo : 2 ≤ h.node.ratio := ((thresholdStrip_eq_near _ _).symm ▸ hnear :
    h.node.ratio ∈ thresholdStrip (h.node.gap+h.node.cutoff) d).1
  have he : h.node.cutoff=h.node.gap/h.node.ratio := hcons
  have hg := reconstructed_log_stability (r := h.node.gap) (q := gapValue v y)
    (t := h.node.ratio) (u := stateRatio y.1) hpos (Real.exp_pos _) (by linarith) (by linarith)
    hgood.2.2.2 hgood.2.2.1
  have hpg : |Real.log (h.node.gap+h.node.cutoff)-Real.log (reconstructedParent v y)| ≤
      4*((n:ℝ)+1)*mesh := by
    rw [he]
    change |Real.log (h.node.gap+h.node.gap/h.node.ratio)-
      Real.log (gapValue v y+gapValue v y/stateRatio y.1)| ≤ _
    convert hg using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hQ : 0 < reconstructedParent v y := add_pos (Real.exp_pos _) (currentExponent_pos v y)
  have hh := coupled_near_to_thick hQ hy2 hd0 hd1 hnear hgood.2.2.1 hmesh hpg hexp
  have hi : stateSide y.1=.even := hgood.2.1.symm.trans hne.1
  refine ⟨hi,hh.1,?_⟩
  simpa only [add_assoc] using hh.2
end NumberTheoryLean.ReconstructedParentCoupling

end

section

namespace NumberTheoryLean.SourceThresholdCoupling
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open FiniteHistoryTransport FiniteHistoryOccurrence ActualProcessCoupling ActualCoupledHistories
open ActualSuccessfulHistories ActualFlagInvariant PersistentFailureFlag
open ReconstructedParentCoupling CoupledEvenArrivalSupport CompletedArrivalOccurrence
open TwoSidedThresholdArrival TwoSidedThresholdKernel TwoSidedThresholdOccurrence
open CanonicalGapExposure RegeneratingInverseBands
attribute [local instance] Classical.propDecidable

variable {w ell S : ℝ} {start : Node}

theorem thresholdPerturbation_nonneg {mesh : ℝ} (hm : 0 ≤ mesh) (N : ℕ) :
    0 ≤ thresholdPerturbation mesh N := by
  have he : 1 ≤ Real.exp (4*((N:ℝ)+1)*mesh) := Real.one_le_exp_iff.mpr (by positivity)
  unfold thresholdPerturbation
  linarith

theorem thickArrival_mono {v d e f : ℝ} (hef : e ≤ f) : thickArrival v d e ⊆ thickArrival v d f := by
  intro y hy
  exact ⟨hy.1,hy.2.1,hy.2.2.1,hy.2.2.2.1,hy.2.2.2.2.trans (add_le_add le_rfl hef)⟩

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem sourceHistory_threshold_transfer (hc : Consistent start)
    {mesh d : ℝ} (hm : 0 < mesh) (hmesh : mesh ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (N : ℕ) (hexp : Real.exp (4*((N:ℝ)+1)*mesh) ≤ 4/3) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      (last N h).2=false → primeThresholdOccurs d N h →
        completedOccurrence (thickArrival (Real.log start.gap) d (thresholdPerturbation mesh N)) N
          (mapHist (fun q => q.1.2) N h) := by
  filter_upwards [sourceHistory_success_good hw hell hS0 hS hr hs hsS hm N,
    sourceHistory_even_arrivals hw hell hS0 hS hr hs hsS mesh N] with h hgood hsupport
  intro hf hbad
  obtain ⟨j,hj⟩ := hbad
  let k : Finset.Iic N := ⟨j.1+1,Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩
  have hg := hgood hf k
  change GoodAt (Real.log start.gap) mesh (j.1+1) ((h k).1.1,(h k).1.2) at hg
  change nearPrimeNode d ((h k).1.1) at hj
  cases hp : (h k).1.1 with
  | none => rw [hp] at hj; exact False.elim hj
  | some p =>
    rw [hp] at hg hj
    cases hy : (h k).1.2 with
    | inr u => rw [hy] at hg; exact False.elim hg
    | inl y =>
      rw [hy] at hg
      have hi : stateSide y.1=.even := hg.2.1.symm.trans hj.1
      have hy2 := hsupport j y hy hi
      have hn : (j.1+1:ℕ) ≤ N := by have := j.isLt; omega
      have hnr : ((j.1+1:ℕ):ℝ) ≤ N := by exact_mod_cast hn
      have harg : 4*((((j.1+1:ℕ):ℝ))+1)*mesh ≤ 4*((N:ℝ)+1)*mesh := by nlinarith
      have hnear := good_prime_near_thick (by linarith : 0 ≤ ell) hr hs hc (j.1+1) p y hg hy2 hmesh hd0 hd1
        ((Real.exp_le_exp.mpr harg).trans hexp) hj
      have herr : 3*mesh+3*(Real.exp (4*((((j.1+1:ℕ):ℝ))+1)*mesh)-1) ≤ thresholdPerturbation mesh N := by
        unfold thresholdPerturbation
        linarith [Real.exp_le_exp.mpr harg]
      refine ⟨j,?_⟩
      change liveMember _ ((h k).1.2)
      rw [hy]
      exact thickArrival_mono herr hnear

theorem source_threshold_probability (hc : Consistent start)
    {mesh d : ℝ} (hm : 0 < mesh) (hmesh : mesh ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (N : ℕ) (hexp : Real.exp (4*((N:ℝ)+1)*mesh) ≤ 4/3) :
    sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N {h | primeThresholdOccurs d N h} ≤
      FlaggedSourceStart.sourceLaw hw hell hS0 hS hr hs hsS mesh N failed +
        ENNReal.ofReal (thickConstant*((8/3:ℝ)*d+((N:ℝ)+1)*thresholdPerturbation mesh N)) := by
  let A : Set (Hist (CemeteryKernel.Space CostState) N) :=
    {h | completedOccurrence (thickArrival (Real.log start.gap) d (thresholdPerturbation mesh N)) N h}
  have hA : MeasurableSet A := completedOccurrence_measurable (thickArrival_measurable _ _ _) N
  have hsub : ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      h ∈ {h | primeThresholdOccurs d N h} → h ∈ {h | (last N h).2=true} ∪
        (mapHist (fun q => q.1.2) N) ⁻¹' A := by
    filter_upwards [sourceHistory_threshold_transfer hw hell hS0 hS hr hs hsS hc hm hmesh hd0 hd1 N hexp] with h hh
    intro hp
    cases hf : (last N h).2 with
    | false => exact Or.inr (hh hf hp)
    | true => exact Or.inl hf
  have hraw := canonical_thick_occurrence_bound (Real.log start.gap) hd0 (thresholdPerturbation_nonneg hm.le N)
    (FlaggedSourceStart.typedState start.side start.ratio hs) N
  have hrawEN : finitePathMeasure (FlaggedSourceStart.typedState start.side start.ratio hs) N
      (thickOccurrence (Real.log start.gap) d (thresholdPerturbation mesh N) N) ≤
        ENNReal.ofReal (thickConstant*((8/3:ℝ)*d+((N:ℝ)+1)*thresholdPerturbation mesh N)) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal hraw
  calc
    _ ≤ sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N
        ({h | (last N h).2=true} ∪ (mapHist (fun q => q.1.2) N) ⁻¹' A) := measure_mono_ae hsub
    _ ≤ sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N {h | (last N h).2=true}+
        sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N ((mapHist (fun q => q.1.2) N) ⁻¹' A) := measure_union_le _ _
    _ ≤ _ := by
      rw [sourceHistory_failure_probability hw hell hS0 hS hr hs hsS mesh N]
      exact add_le_add le_rfl ((source_completed_occurrence_le hw hell hS0 hS hr hs hsS mesh N
        (thickArrival_measurable _ _ _)).trans hrawEN)
end NumberTheoryLean.SourceThresholdCoupling

end

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_ThresholdMeshRate
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ThresholdMeshRate
open _root_.Filter SourceThresholdCoupling ExponentialMesh
open scoped Topology

theorem thresholdPerturbation_le {h : ℝ} (hh : 0 ≤ h) (N : ℕ)
    (hsmall : 4*((N:ℝ)+1)*h ≤ 1) : thresholdPerturbation h N ≤ 39*((N:ℝ)+1)*h := by
  have hexp := exp_increment (show 0 ≤ 4*((N:ℝ)+1)*h by positivity) hsmall
  unfold thresholdPerturbation
  nlinarith [mul_nonneg (Nat.cast_nonneg N) hh]

theorem threshold_mesh_controls {A C κ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hκ : 0 < κ)
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ w : ℝ in atTop,∀ N : ℕ,(N:ℝ) ≤ A*(Real.log w)^3 →
      Real.exp (4*((N:ℝ)+1)*mesh κ w) ≤ 4/3 ∧
        C*((N:ℝ)+1)*thresholdPerturbation (mesh κ w) N ≤ eta := by
  have hlog : 0 < Real.log (4/3:ℝ) := Real.log_pos (by norm_num)
  have hmin : 0 < min 1 (Real.log (4/3:ℝ)) := lt_min (by norm_num) hlog
  filter_upwards [(log_power_exp_tendsto (4*(A+1)) 3 hκ).eventually (eventually_le_nhds hmin),
    (log_power_exp_tendsto (39*C*(A+1)^2) 6 hκ).eventually (eventually_le_nhds heta),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with w harg herr hL
  intro N hN
  have hm : 0 ≤ mesh κ w := (mesh_pos κ w).le
  have hL3 : 1 ≤ (Real.log w)^3 := one_le_pow₀ hL
  have hNp : (N:ℝ)+1 ≤ (A+1)*(Real.log w)^3 := by nlinarith
  have harg' : 4*((N:ℝ)+1)*mesh κ w ≤ min 1 (Real.log (4/3:ℝ)) := by
    calc
      _ ≤ (4*(A+1)*(Real.log w)^3)*Real.exp (-κ*Real.sqrt (Real.log w)) :=
        mul_le_mul (by nlinarith) (mesh_upper κ w) hm (by positivity)
      _ ≤ _ := harg
  refine ⟨?_,?_⟩
  · have hh := Real.exp_le_exp.mpr (harg'.trans (min_le_right _ _))
    simpa only [Real.exp_log (by norm_num : (0:ℝ)<4/3)] using hh
  · have hpert := thresholdPerturbation_le hm N (harg'.trans (min_le_left _ _))
    have hsq : ((N:ℝ)+1)^2 ≤ (A+1)^2*(Real.log w)^6 := by
      have hh := sq_le_sq₀ (show 0 ≤ (N:ℝ)+1 by positivity) (show 0 ≤ (A+1)*(Real.log w)^3 by positivity) |>.mpr hNp
      nlinarith
    calc
      _ ≤ 39*C*((N:ℝ)+1)^2*mesh κ w := by
        have hh := mul_le_mul_of_nonneg_left hpert (show 0 ≤ C*((N:ℝ)+1) by positivity)
        nlinarith
      _ ≤ (39*C*(A+1)^2*(Real.log w)^6)*Real.exp (-κ*Real.sqrt (Real.log w)) :=
        mul_le_mul (by nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ 39*C by positivity)])
          (mesh_upper κ w) hm (by positivity)
      _ ≤ _ := herr
end NumberTheoryLean.ThresholdMeshRate


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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReferenceIsolatedExclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970



namespace NumberTheoryLean.SourceThresholdRate
open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open ActualCoupledHistories SourceSelectedCompactOccupation SourceThresholdCoupling ThresholdMeshRate
open SourceCouplingRate ExponentialMesh TwoSidedThresholdKernel LowStateHorizon


theorem source_prime_threshold_probability_jb247_oai : ∃ κ₀ : ℝ,0 < κ₀ ∧
    ∀ κ : ℝ,0 < κ → κ ≤ κ₀ → ∀ D eps : ℝ,0 < D → 0 < eps →
    ∃ w₀ : ℝ,1 < w₀ ∧ ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ,
      ∀ start : Node,∀ hs : Valid start.side start.ratio,
      1 ≤ ell → 0 < B → 2 ≤ Real.log B → Real.log B ≤ D*Real.log w →
      0 < start.gap → start.ratio ≤ 23/10 → Consistent start → start.gap ≤ (23/10:ℝ)*B →
      let S := (Real.log B)^2
      let N := sourceHorizon S B
      ∀ delta : ℝ,0 ≤ delta → delta ≤ 1 →
      fullSourceLaw w ell S start hs (mesh κ w) N {h | primeThresholdOccurs delta N h} ≤
        ENNReal.ofReal ((8/3:ℝ)*thickConstant*delta+eps) := by
  have hCpos : 0 < thickConstant := thickConstant_pos
  obtain ⟨κ₀,hκ₀,hCouple⟩ := source_coupling_rate_jb247
  refine ⟨κ₀,hκ₀,?_⟩
  intro κ hκ hκle D eps hD heps
  obtain ⟨WC,hWC,hC⟩ := hCouple κ hκ hκle D hD
  have hA : 0 ≤ 5*D^3 := by positivity
  have hEvents := (threshold_mesh_controls hA thickConstant_pos.le hκ (show 0 < eps/2 by positivity)).and
    (((log_power_exp_tendsto 1 0 (show 0 < κ/2 by positivity)).eventually
      (eventually_le_nhds (show 0 < eps/2 by positivity))).and
      (Real.tendsto_log_atTop.eventually_ge_atTop (D^2)))
  obtain ⟨W,hW⟩ := eventually_atTop.mp hEvents
  refine ⟨max WC (max normalizationThreshold W),hWC.trans_le (le_max_left _ _),?_⟩
  intro w hw ell B start hs hell hB hlogB hcomp hr hs23 hc hsize
  dsimp only
  intro delta hd0 hd1
  have hwC : WC ≤ w := (le_max_left _ _).trans hw
  have hnorm : normalizationThreshold ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw
  have hwe := hW w ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hw)
  have hscale := UniformBudgetRate.source_scale_bound hwe.2.2 hlogB hcomp
  have hS0 : 0 ≤ (Real.log B)^2 := sq_nonneg _
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  have hcontrols := hwe.1 (sourceHorizon ((Real.log B)^2) B) hscale.2
  have hf := (hC w hwC ell B start hs hell hB hlogB hcomp hr hs23 hc hsize).1
    (sourceHorizon ((Real.log B)^2) B) le_rfl |>.1
  have hfail : Real.exp (-(κ/2)*Real.sqrt (Real.log w)) ≤ eps/2 := by
    simpa only [pow_zero,mul_one,one_mul] using hwe.2.1
  have hprob := source_threshold_probability hnorm hell hS0 hscale.1 hr hs hsS hc
    (mesh_pos κ w) (mesh_le_one hκ.le w) hd0 hd1 (sourceHorizon ((Real.log B)^2) B) hcontrols.1
  rw [← fullSourceLaw_eq hnorm hell hS0 hscale.1 hr hs hsS] at hprob
  have he : thickConstant*((8/3:ℝ)*delta+((sourceHorizon ((Real.log B)^2) B:ℝ)+1)*
      thresholdPerturbation (mesh κ w) (sourceHorizon ((Real.log B)^2) B)) ≤
        (8/3:ℝ)*thickConstant*delta+eps/2 := by nlinarith [hcontrols.2]
  calc
    _ ≤ _ := hprob
    _ ≤ ENNReal.ofReal (eps/2)+ENNReal.ofReal ((8/3:ℝ)*thickConstant*delta+eps/2) :=
      add_le_add (hf.trans (ENNReal.ofReal_le_ofReal hfail)) (ENNReal.ofReal_le_ofReal he)
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ eps/2)
        (by positivity : 0 ≤ (8/3:ℝ)*thickConstant*delta+eps/2)]
      congr 1
      ring
end NumberTheoryLean.SourceThresholdRate



end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.NumberTheoryLean.SourceThresholdRate.source_prime_threshold_probability_jb247_oai := @OAI.Erdos970.NumberTheoryLean.SourceThresholdRate.source_prime_threshold_probability_jb247_oai
