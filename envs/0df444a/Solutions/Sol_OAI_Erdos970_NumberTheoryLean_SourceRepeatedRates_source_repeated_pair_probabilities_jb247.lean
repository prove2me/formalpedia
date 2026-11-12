-- Prove2me | solution 1 for OAI.Erdos970.NumberTheoryLean.SourceRepeatedRates.source_repeated_pair_probabilities_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:07:49.957191+00:00
-- url     : https://prove2.me/submissions/e9cd86c6-0aea-40e2-8df6-4f6117ef0e04

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
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.ZMod.Units
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.GroupTheory.Index
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
import Mathlib.Order.Filter.AtTopBot.Basic
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
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.ContinuousMap.Bounded.Basic
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

theorem minRatio_ge_sub_one (i : Side) (s : ℝ) : s - 1 ≤ minRatio i s := by
  cases i with
  | even => exact le_rfl
  | odd => exact le_max_right _ _

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



namespace NumberTheoryLean.FiniteHistoryOccurrence
open Set MeasureTheory ProbabilityTheory FiniteHistoryTransport
variable {X : Type*} [MeasurableSpace X]

theorem atIndex_law (K : Kernel X X) [IsMarkovKernel K] (N : ℕ) (h₀ : Hist X 0) (j : Fin (N+1)) :
    (pathKernel K N h₀).map (fun h => atIndex N h j)=(K^j.1) (last 0 h₀) :=
  pathMeasure_coordinate K N j.1 (Nat.le_of_lt_succ j.isLt) h₀

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

theorem pathSum_measurable {F : X → ℝ} (hF : Measurable F) (n : ℕ) :
    Measurable (pathSum F n) := by
  unfold pathSum
  fun_prop

theorem extend_previous (n : ℕ) (h : Hist X n) (x : X) (k : Finset.Iic n) :
    extend n h x ⟨k,by exact Finset.mem_Iic.mpr ((Finset.mem_Iic.mp k.2).trans n.le_succ)⟩ = h k := by
  simp [extend,IicProdIoc_def,show (k:ℕ) ≤ n from Finset.mem_Iic.mp k.2]

theorem pathSum_extend (F : X → ℝ) (n : ℕ) (h : Hist X n) (x : X) :
    pathSum F (n+1) (extend n h x) = pathSum F n h + F (last n h) := by
  rw [pathSum,Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact extend_previous n h x ⟨j,by exact Finset.mem_Iic.mpr j.isLt.le⟩
  · congr 1
    exact extend_previous n h x ⟨n,by simp⟩

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

theorem gapValue_update (v : ℝ) (z : CostState) (s : State) :
    gapValue v (s, z.2 + cost (stateRatio s)) = nextGap (gapValue v z) (stateRatio s) := by
  rw [nextGap_eq_cost (stateRatio_pos s)]
  change Real.exp (v - (z.2 + cost (stateRatio s))) = Real.exp (v - z.2) * Real.exp (-cost (stateRatio s))
  rw [show v - (z.2 + cost (stateRatio s)) = (v - z.2) + (-cost (stateRatio s)) by ring, Real.exp_add]

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



namespace NumberTheoryLean.PrimeKilledChain

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeHistories PrimeRowNormalization

theorem normalizationThreshold_gt_one : 1 < normalizationThreshold :=
  (Classical.choose_spec (Classical.choose_spec retained_row_mass_one_add)).2.1

end NumberTheoryLean.PrimeKilledChain



namespace NumberTheoryLean.PrimeCompactVisits

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeTiltGeometry

variable {w ell S : ℝ} {start : Node}

theorem visit_nonneg (K : ℝ) (z : ChainState w ell S start) : 0 ≤ visit K z := by
  cases z with
  | none => exact le_rfl
  | some h => simp only [visit]; split_ifs <;> norm_num

theorem potential_nonneg {K : ℝ} (hK : 0 ≤ K) (hell : 0 ≤ ell)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (z : ChainState w ell S start) :
    0 ≤ potential K z := by
  cases z with
  | none => exact le_rfl
  | some h =>
    have hg : 0 < h.node.gap := terminal_gap_positive hell hr hs h.admissible
    exact add_nonneg (le_min hg.le hK) zero_le_one

theorem potential_le {K : ℝ} (hK : 0 ≤ K) (z : ChainState w ell S start) :
    potential K z ≤ K+1 := by
  cases z with
  | none => change (0:ℝ) ≤ K+1; linarith
  | some h => exact add_le_add_left (min_le_right _ _) 1

theorem visit_le_potential {K : ℝ} (hK : 0 ≤ K) (hell : 0 ≤ ell)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (z : ChainState w ell S start) :
    visit K z ≤ potential K z := by
  cases z with
  | none => exact le_rfl
  | some h =>
    have hg : 0 < h.node.gap := terminal_gap_positive hell hr hs h.admissible
    simp only [visit,potential]
    split_ifs with hle
    · rw [min_eq_left hle]; linarith
    · exact add_nonneg (le_min hg.le hK) zero_le_one

theorem child_potential_drift {K : ℝ} (hell : 1 ≤ ell)
    (h : History w ell S start) (p : ℕ) (hp : p ∈ nodeChildren w ell S h.node) :
    visit K (some h) + potential K (some (h.append p hp)) ≤ potential K (some h) := by
  classical
  have he : ell < ErdosPrimeInputs.HarmonicPrimeMeasure.primeExponent w p :=
    (Finset.mem_filter.mp hp).2.1
  simp only [visit,potential,History.append_node,step]
  split_ifs with hle
  · rw [min_eq_left hle]
    have hm := min_le_left (h.node.gap-ErdosPrimeInputs.HarmonicPrimeMeasure.primeExponent w p) K
    linarith
  · rw [min_eq_right (le_of_not_ge hle)]
    have hm := min_le_right (h.node.gap-ErdosPrimeInputs.HarmonicPrimeMeasure.primeExponent w p) K
    linarith

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell)
    (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

include hell hr hs in

theorem actual_row_drift_ae {K : ℝ} (hK : 0 ≤ K) (z : ChainState w ell S start) :
    ∀ᵐ y ∂chain w ell S start z, visit K z + potential K y ≤ potential K z := by
  classical
  cases z with
  | none =>
    rw [chain_none]
    exact (ae_dirac_iff (by trivial)).mpr (by simp [visit,potential])
  | some h =>
    have hdead : visit K (some h) + potential K (none : ChainState w ell S start) ≤ potential K (some h) := by
      simpa only [potential,add_zero] using visit_le_potential hK (by linarith : 0 ≤ ell) hr hs (some h)
    have hchild := child_potential_drift (K := K) hell h
    apply ae_iff.mpr
    simp [chain_some,completedLaw,liveLaw,hdead,hchild]

end NumberTheoryLean.PrimeCompactVisits



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
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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



namespace NumberTheoryLean.RepeatedBinGeometry
open _root_.Set FinitePathGeometry SourceStopPredicate
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinMaps
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem equal_label_exponent_distance {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    {p q : ℕ} (hp : p ∈ sourcePrimeSet w top) (hq : q ∈ sourcePrimeSet w top)
    (hl : label (zero_lt_one.trans hw) htop hxi p=label (zero_lt_one.trans hw) htop hxi q) :
    |primeExponent w p-primeExponent w q| ≤ xi/Real.log w := by
  have hpe := source_representative_error hw htop hxi hp
  have hqe := source_representative_error hw htop hxi hq
  have he : representative w (lower w top xi) (width w top xi) (label (zero_lt_one.trans hw) htop hxi) p=
      representative w (lower w top xi) (width w top xi) (label (zero_lt_one.trans hw) htop hxi) q := by
    unfold representative
    rw [hl]
  rw [he] at hpe
  exact abs_le.mpr ⟨by linarith [hpe.1,hpe.2,hqe.1,hqe.2],by linarith [hpe.1,hpe.2,hqe.1,hqe.2]⟩

theorem adjacent_ratio_slack {r x x' h : ℝ} (hr : 0 < r) (hx : 0 < x)
    (hxx : x ≤ x') (hwidth : x'-x ≤ h) :
    0 ≤ (r/x-1)-(r/x'-1) ∧ (r/x-1)-(r/x'-1) ≤ (r/x')*h/x := by
  have hx' : 0 < x' := hx.trans_le hxx
  have he : (r/x-1)-(r/x'-1)=(r/x')*(x'-x)/x := by
    field_simp [hx.ne',hx'.ne']
    ring
  rw [he]
  exact ⟨div_nonneg (mul_nonneg (div_pos hr hx').le (sub_nonneg.mpr hxx)) hx.le,
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwidth (div_pos hr hx').le) hx.le⟩

theorem matched_repeat_interval (i : Side) {s t s' t' H mesh : ℝ}
    (hs : |s-s'| ≤ mesh) (ht : |t-t'| ≤ mesh)
    (hslack : t-(s-1) ≤ H) (hsupport : minRatio i s' ≤ t') :
    t' ∈ Icc (minRatio i s') (minRatio i s'+H+2*mesh) := by
  refine ⟨hsupport,?_⟩
  have hmin := minRatio_ge_sub_one i s'
  linarith [(abs_le.mp hs).2,(abs_le.mp ht).1]
end NumberTheoryLean.RepeatedBinGeometry



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



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_FiniteHistoryPairLaw
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.ActualCoupledHistories.sourceHistoryLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.FiniteHistoryPairLaw
open Set MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal
open FiniteHistoryTransport FiniteHistoryOccurrence
variable {X : Type*} [MeasurableSpace X]

theorem adjacentPair_measurable (N : ℕ) (j : Fin N) : Measurable (fun h : Hist X N => adjacentPair N h j) :=
  (measurable_pi_apply _).prodMk (measurable_pi_apply _)

theorem lintegral_adjacent_pair (K : Kernel X X) [IsMarkovKernel K]
    (N : ℕ) (h₀ : Hist X 0) (j : Fin N) {F : X×X → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ h,F (adjacentPair N h j) ∂pathKernel K N h₀)=
      ∫⁻ x,∫⁻ y,F (x,y) ∂K x ∂(K^j.1) (last 0 h₀) := by
  have hk : j.1+1 ≤ N := by have := j.isLt; omega
  let G : Hist X (j.1+1) → ℝ≥0∞ :=
    fun h => F (h ⟨j.1,Finset.mem_Iic.mpr (by omega)⟩,last (j.1+1) h)
  have hG : Measurable G := hF.comp ((measurable_pi_apply _).prodMk (last_measurable _))
  have hprefix : (pathKernel K N h₀).map (frestrictLe₂ (π := fun _ => X) hk)=pathKernel K (j.1+1) h₀ :=
    Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ => X) (κ := pastKernel K) h₀ hk
  change (∫⁻ h,G (frestrictLe₂ (π := fun _ => X) hk h) ∂pathKernel K N h₀)=_
  rw [← lintegral_map hG (measurable_frestrictLe₂ hk),hprefix,lintegral_pathKernel_succ K j.1 h₀ hG]
  calc
    _ = ∫⁻ h,∫⁻ y,F (last j.1 h,y) ∂K (last j.1 h) ∂pathKernel K j.1 h₀ := by
      apply lintegral_congr
      intro h
      apply lintegral_congr
      intro y
      change F ((extend j.1 h y) ⟨j.1,Finset.mem_Iic.mpr (by omega)⟩,
        last (j.1+1) (extend j.1 h y))=F (last j.1 h,y)
      rw [extend_last,extend_previous j.1 h y ⟨j.1,by simp⟩]
      rfl
    _ = _ := by
      have hcur : Measurable (Function.uncurry (fun x : X => fun y : X => F (x,y))) := hF
      exact lintegral_endpoint K j.1 h₀ (hcur.lintegral_kernel_prod_right (κ := K))

theorem pairProbability_integral (K : Kernel X X) {E : Set (X×X)} (hE : MeasurableSet E) (x : X) :
    (∫⁻ y,E.indicator (fun _ => (1:ℝ≥0∞)) (x,y) ∂K x)=pairProbability K E x := by
  change (∫⁻ y,((Prod.mk x) ⁻¹' E).indicator 1 y ∂K x)=_
  exact lintegral_indicator_one (measurable_prodMk_left hE)

theorem pairProbability_measurable (K : Kernel X X) [IsSFiniteKernel K]
    {E : Set (X×X)} (hE : MeasurableSet E) : Measurable (pairProbability K E) := by
  have hF : Measurable (E.indicator (fun _ => (1:ℝ≥0∞))) := measurable_const.indicator hE
  have hcur : Measurable (Function.uncurry (fun x : X => fun y : X => E.indicator (fun _ => (1:ℝ≥0∞)) (x,y))) := hF
  have hh := hcur.lintegral_kernel_prod_right (κ := K)
  simpa only [pairProbability_integral K hE] using hh

theorem adjacent_pair_probability (K : Kernel X X) [IsMarkovKernel K]
    {E : Set (X×X)} (hE : MeasurableSet E) (N : ℕ) (h₀ : Hist X 0) (j : Fin N) :
    pathKernel K N h₀ ((fun h => adjacentPair N h j) ⁻¹' E)=
      ∫⁻ h,pairProbability K E (atIndex N h j.castSucc) ∂pathKernel K N h₀ := by
  have hF : Measurable (E.indicator (fun _ => (1:ℝ≥0∞))) := measurable_const.indicator hE
  have hc : Measurable (fun h : Hist X N => atIndex N h j.castSucc) := measurable_pi_apply _
  have hp := atIndex_law K N h₀ j.castSucc
  simp only [Fin.val_castSucc] at hp
  calc
    _ = ∫⁻ h,E.indicator (fun _ => (1:ℝ≥0∞)) (adjacentPair N h j) ∂pathKernel K N h₀ :=
      (lintegral_indicator_one ((adjacentPair_measurable N j) hE)).symm
    _ = ∫⁻ x,∫⁻ y,E.indicator (fun _ => (1:ℝ≥0∞)) (x,y) ∂K x ∂(K^j.1) (last 0 h₀) :=
      lintegral_adjacent_pair K N h₀ j hF
    _ = ∫⁻ x,pairProbability K E x ∂(K^j.1) (last 0 h₀) := by simp_rw [pairProbability_integral K hE]
    _ = _ := by rw [← hp,lintegral_map (pairProbability_measurable K hE) hc]
end NumberTheoryLean.FiniteHistoryPairLaw

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_FinitePairOccurrence
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.NumberTheoryLean.ActualCoupledHistories.sourceHistoryLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.FinitePairOccurrence
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open FiniteHistoryTransport FiniteHistoryOccurrence FiniteHistoryPairLaw

variable {X : Type*} [MeasurableSpace X]

theorem pair_occurrence_lintegral_bound (K : Kernel X X) [IsMarkovKernel K]
    {E : Set (X×X)} (hE : MeasurableSet E) (N : ℕ) (h₀ : Hist X 0) :
    pathKernel K N h₀ (pairOccurrence E N) ≤
      ∫⁻ h,∑ j : Fin N,pairProbability K E (atIndex N h j.castSucc) ∂pathKernel K N h₀ := by
  apply (measure_iUnion_fintype_le _ (fun j : Fin N => (fun h => adjacentPair N h j) ⁻¹' E)).trans_eq
  simp_rw [adjacent_pair_probability K hE N h₀]
  symm
  apply lintegral_finsetSum
  intro j _
  have hc : Measurable (fun h : Hist X N => atIndex N h j.castSucc) := measurable_pi_apply _
  exact (pairProbability_measurable K hE).comp hc

theorem pair_occurrence_of_budget (K : Kernel X X) [IsMarkovKernel K]
    {E : Set (X×X)} (hE : MeasurableSet E) (N : ℕ) (h₀ : Hist X 0)
    (g : X → ℝ) (hg : ∀ x,0 ≤ g x) (C : ℝ)
    (hrow : ∀ x,pairProbability K E x ≤ ENNReal.ofReal (g x))
    (hbudget : ∀ᵐ h ∂pathKernel K N h₀,(∑ j : Fin N,g (atIndex N h j.castSucc)) ≤ C) :
    pathKernel K N h₀ (pairOccurrence E N) ≤ ENNReal.ofReal C := by
  calc
    _ ≤ ∫⁻ h,∑ j : Fin N,pairProbability K E (atIndex N h j.castSucc) ∂pathKernel K N h₀ :=
      pair_occurrence_lintegral_bound K hE N h₀
    _ ≤ ∫⁻ h,ENNReal.ofReal (∑ j : Fin N,g (atIndex N h j.castSucc)) ∂pathKernel K N h₀ := by
      apply lintegral_mono
      intro h
      change (∑ j : Fin N,pairProbability K E (atIndex N h j.castSucc)) ≤
        ENNReal.ofReal (∑ j : Fin N,g (atIndex N h j.castSucc))
      rw [ENNReal.ofReal_sum_of_nonneg (fun (j : Fin N) (_ : j ∈ Finset.univ) => hg (atIndex N h j.castSucc))]
      exact Finset.sum_le_sum (fun j _ => hrow _)
    _ ≤ ∫⁻ _h : Hist X N,ENNReal.ofReal C ∂pathKernel K N h₀ :=
      lintegral_mono_ae (hbudget.mono (fun h hh => ENNReal.ofReal_le_ofReal hh))
    _ = _ := by simp

theorem pair_occurrence_of_uniform_row (K : Kernel X X) [IsMarkovKernel K]
    {E : Set (X×X)} (hE : MeasurableSet E) (N : ℕ) (h₀ : Hist X 0)
    {A : ℝ} (hA : 0 ≤ A) (hrow : ∀ x,pairProbability K E x ≤ ENNReal.ofReal A) :
    pathKernel K N h₀ (pairOccurrence E N) ≤ ENNReal.ofReal ((N:ℝ)*A) := by
  apply pair_occurrence_of_budget K hE N h₀ (fun _ => A) (fun _ => hA) ((N:ℝ)*A) hrow
  exact Filter.Eventually.of_forall (fun _ => by simp)
end NumberTheoryLean.FinitePairOccurrence


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
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeHistoryCompactCount
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.PrimeHistoryCompactCount

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeCompactVisits
open FiniteHistoryTransport ActualCoupledHistories ActualProcessCoupling PersistentFailureFlag

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

include hw hell hS0 hS hr hs hsS

theorem pathwise_compact_potential {R : ℝ} (hR : 0 ≤ R) (N : ℕ) :
    ∀ᵐ h ∂pathKernel (chain w ell S start) N (fun _ => some History.empty),
      pathSum (visit R) N h + potential R (last N h) ≤
        potential R (some (History.empty : History w ell S start)) := by
  let := chain_isMarkov hw hell hS0 hS hr hs hsS
  have hv : Measurable (visit (w:=w) (ell:=ell) (S:=S) (start:=start) R) := measurable_of_countable _
  have hp : Measurable (potential (w:=w) (ell:=ell) (S:=S) (start:=start) R) := measurable_of_countable _
  induction N with
  | zero =>
    change ∀ᵐ h ∂Measure.dirac (fun _ => some History.empty), _
    apply (ae_dirac_iff ((measurableSet_le
      ((pathSum_measurable hv 0).add (hp.comp (last_measurable 0))) measurable_const))).mpr
    simp [pathSum,last]
  | succ N ih =>
    apply ae_pathKernel_succ _ N _ (measurableSet_le
      ((pathSum_measurable hv (N+1)).add (hp.comp (last_measurable (N+1)))) measurable_const)
    filter_upwards [ih] with h hh
    filter_upwards [actual_row_drift_ae hell hr hs hR (last N h)] with y hy
    change pathSum (visit R) (N+1) (FiniteHistoryTransport.extend N h y) +
      potential R (last (N+1) (FiniteHistoryTransport.extend N h y)) ≤ _
    rw [pathSum_extend,extend_last]
    linarith

theorem pathwise_compact_count {R : ℝ} (hR : 0 ≤ R) (N : ℕ) :
    ∀ᵐ h ∂pathKernel (chain w ell S start) N (fun _ => some History.empty),
      pathSum (visit R) N h ≤ R+1 := by
  filter_upwards [pathwise_compact_potential hw hell hS0 hS hr hs hsS hR N] with h hh
  have hp := potential_nonneg hR (by linarith : 0 ≤ ell) hr hs (last N h)
  have hinit := potential_le (w:=w) (ell:=ell) (S:=S) (start:=start) hR (some History.empty)
  linarith

theorem sourceHistory_compact_count {R : ℝ} (hR : 0 ≤ R) (mesh : ℝ) (N : ℕ) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      pathSum (visit R) N (mapHist (fun q => q.1.1) N h) ≤ R+1 := by
  have hP : MeasurableSet {h : Hist (ChainState w ell S start) N |
      pathSum (visit R) N h ≤ R+1} :=
    measurableSet_le (pathSum_measurable (measurable_of_countable _) N) measurable_const
  have hh : ∀ᵐ h ∂(sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N).map
      (mapHist (fun q => q.1.1) N), pathSum (visit R) N h ≤ R+1 := by
    rw [sourceHistoryLaw_prime]
    exact pathwise_compact_count hw hell hS0 hS hr hs hsS hR N
  exact (ae_map_iff (mapHist_measurable (by exact measurable_fst.comp measurable_fst) N).aemeasurable hP).mp hh

end NumberTheoryLean.PrimeHistoryCompactCount

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
open RepeatedBinGeometry CandidateTerminalGeometry MarkedPrefixTools
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

theorem actual_same_bin_slack {w ell S top xi : ℝ} {start : Node}
    (hw : 1 < w) (htop : w < top) (hell : 1 ≤ ell) (hxi : 0 < xi)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hcap : w^start.cutoff=top)
    (h : History w ell S start) (hne : h.primes ≠ []) (p : ℕ) (hp : p ∈ nodeChildren w ell S h.node)
    (hl : label (zero_lt_one.trans hw) htop hxi (h.primes.getLastD 0)=label (zero_lt_one.trans hw) htop hxi p) :
    0 ≤ (h.append p hp).node.ratio-(h.node.ratio-1) ∧
      (h.append p hp).node.ratio-(h.node.ratio-1) ≤ h.node.ratio*(xi/Real.log w)/primeExponent w p := by
  have hLast : h.primes.getLastD 0 ∈ h.primes := by
    have he : h.primes.getLastD 0=h.primes.getLast hne := by
      conv_lhs => rw [← List.dropLast_append_getLast hne]
      exact List.getLastD_concat
    rw [he]
    exact List.getLast_mem hne
  have hsrcOld := history_source_primes hw htop hell hcap h _ hLast
  have hsrcNew := history_source_primes hw htop hell hcap (h.append p hp) p (by simp [History.append_primes])
  have hdist := equal_label_exponent_distance hw htop hxi hsrcOld hsrcNew hl
  have hdata := (mem_children_iff hw h.node.side h.node.closed p).mp hp
  have hx : 0 < primeExponent w p := by linarith [hdata.2.1]
  have hcut : primeExponent w p ≤ h.node.cutoff := by
    have hh := hdata.2.2.1
    cases he : h.node.closed with
    | false =>
      simp only [capGuard,he,Bool.false_eq_true,ite_false, if_false] at hh
      exact hh.le
    | true => simpa only [capGuard,he,ite_true, if_true] using hh
  have hlastCut : h.node.cutoff=primeExponent w (h.primes.getLastD 0) := terminal_lastD w start h.primes hne
  have hOld : 0 < primeExponent w (h.primes.getLastD 0) := by linarith [hcut]
  have hratio : h.node.ratio=h.node.gap/primeExponent w (h.primes.getLastD 0) := by
    have hh := terminal_ratio_div_cutoff w start h.primes hne (show h.node.cutoff ≠ 0 by linarith [hcut])
    change h.node.ratio=h.node.gap/h.node.cutoff at hh
    rwa [hlastCut] at hh
  have hrg : 0 < h.node.gap := terminal_gap_positive (by linarith : 0 ≤ ell) hr hs h.admissible
  have hh := adjacent_ratio_slack hrg hx (show primeExponent w p ≤ primeExponent w (h.primes.getLastD 0) by linarith [hcut])
    ((le_abs_self _).trans hdist)
  rw [← hratio] at hh
  simpa only [History.append_node,step,childRatio] using hh
end NumberTheoryLean.ActualRepeatedBinStep


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SourceTransitionSupport
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SourceTransitionSupport
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualCoupledHistories ActualFlagInvariant PersistentFailureFlag
open ActualCouplingUpdates ActualSupportIntervals ContinuousKilledBins LowStateHorizon


variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem sourceTransition_left (mesh : ℝ) (x : FlagState (JointState w ell S start)) :
    (sourceTransition hw hell hS0 hS hr hs hsS mesh x).map (fun y => y.1.1)=chain w ell S start x.1.1 := by
  calc
    _ = ((sourceTransition hw hell hS0 hS hr hs hsS mesh x).map Prod.fst).map Prod.fst :=
      (Measure.map_map measurable_fst measurable_fst).symm
    _ = _ := by
      rw [sourceTransition,marked_map]
      exact jointKernel_left hw hell hS0 hS hr hs hsS (Real.log start.gap) mesh x.1.1 x.1.2

theorem sourceTransition_right (mesh : ℝ) (x : FlagState (JointState w ell S start)) :
    (sourceTransition hw hell hS0 hS hr hs hsS mesh x).map (fun y => y.1.2)=
      continuousChain (Real.log start.gap) ell S x.1.2 := by
  calc
    _ = ((sourceTransition hw hell hS0 hS hr hs hsS mesh x).map Prod.fst).map Prod.snd :=
      (Measure.map_map measurable_snd measurable_fst).symm
    _ = _ := by
      rw [sourceTransition,marked_map]
      exact jointKernel_right hw hell hS0 hS hr hs hsS (Real.log start.gap) mesh x.1.1 x.1.2

theorem sourceTransition_live_support (mesh : ℝ) (h : History w ell S start) (z : CostState) (flag : Bool) :
    ∀ᵐ y ∂sourceTransition hw hell hS0 hS hr hs hsS mesh ((some h,Sum.inl z),flag),
      primeFollows h y.1.1 ∧ liftPredicate
        (fun q : CostState => minRatio (stateSide z.1) (stateRatio z.1) ≤ stateRatio q.1) y.1.2 := by
  have hp : ∀ᵐ y ∂sourceTransition hw hell hS0 hS hr hs hsS mesh ((some h,Sum.inl z),flag),primeFollows h y.1.1 := by
    have hh : ∀ᵐ y ∂(sourceTransition hw hell hS0 hS hr hs hsS mesh ((some h,Sum.inl z),flag)).map
        (fun y => y.1.1),primeFollows h y := by
      rw [sourceTransition_left hw hell hS0 hS hr hs hsS]
      exact prime_follows h
    exact (ae_map_iff (measurable_fst.comp measurable_fst).aemeasurable (show MeasurableSet {y | primeFollows h y} from trivial)).mp hh
  have hP : MeasurableSet {q : CostState | minRatio (stateSide z.1) (stateRatio z.1) ≤ stateRatio q.1} :=
    measurableSet_le measurable_const (stateRatio_measurable.comp measurable_fst)
  have hq : ∀ᵐ y ∂sourceTransition hw hell hS0 hS hr hs hsS mesh ((some h,Sum.inl z),flag),
      liftPredicate (fun q : CostState => minRatio (stateSide z.1) (stateRatio z.1) ≤ stateRatio q.1) y.1.2 := by
    have hh : ∀ᵐ y ∂(sourceTransition hw hell hS0 hS hr hs hsS mesh ((some h,Sum.inl z),flag)).map
        (fun y => y.1.2),liftPredicate (fun q : CostState => minRatio (stateSide z.1) (stateRatio z.1) ≤ stateRatio q.1) y := by
      rw [sourceTransition_right hw hell hS0 hS hr hs hsS]
      apply complete_ae _ z hP
      rw [lowKernel,Kernel.restrict_apply]
      exact ae_restrict_of_ae (costKernel_lower_support z)
    exact (ae_map_iff (measurable_snd.comp measurable_fst).aemeasurable (liftPredicate_measurable hP)).mp hh
  exact hp.and hq
end NumberTheoryLean.SourceTransitionSupport


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RepeatedStepRowBound
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RepeatedStepRowBound
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain ActualProcessCoupling
open ActualCoupledHistories ActualFlagInvariant PersistentFailureFlag ActualCouplingUpdates
open SourceTransitionSupport CompletedParentInterval ContinuousIntervalUpper
open ContinuousKilledBins
open ActualRepeatedBinStep RepeatedBinGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure


theorem repeatDensityConstant_pos : 0 < repeatDensityConstant :=
  (Classical.choose_spec completed_parent_interval_upper).1

variable {w ell S : ℝ} {start : Node}

variable (hwn : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem good_repeat_next_row {top xi U X mesh : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hU : 0 ≤ U) (hX : 0 < X)
    (hm : 0 < mesh) (hmesh : mesh ≤ 1) (hcap : w^start.cutoff=top)
    (N : ℕ) (h : History w ell S start) (hne : h.primes ≠ []) (z : CostState) (flag : Bool)
    (hgood : GoodAt (Real.log start.gap) mesh N (some h,Sum.inl z)) (hparent : h.node.ratio ≤ U) :
    sourceTransition hwn hell hS0 hS hr hs hsS mesh ((some h,Sum.inl z),flag)
      (goodRepeatNext (label (zero_lt_one.trans hw) htop hxi) X (Real.log start.gap) mesh N h) ≤
        ENNReal.ofReal (repeatBudget U X xi w mesh) := by
  let a := minRatio (stateSide z.1) (stateRatio z.1)
  let H := U*(xi/Real.log w)/X+2*mesh
  have hh0 : 0 ≤ xi/Real.log w := div_nonneg hxi.le (Real.log_pos hw).le
  have hH : 0 ≤ H := by dsimp [H] <;> positivity
  have hzU : stateRatio z.1 ≤ U+1 := by linarith [(abs_le.mp hgood.2.2.1).1]
  have hT : MeasurableSet (Sum.inl '' closedCostBin a (a+H) : Set (CemeteryKernel.Space CostState)) :=
    (closedCostBin_measurable a (a+H)).inl_image
  have hdom : ∀ᵐ y ∂sourceTransition hwn hell hS0 hS hr hs hsS mesh ((some h,Sum.inl z),flag),
      y ∈ goodRepeatNext (label (zero_lt_one.trans hw) htop hxi) X (Real.log start.gap) mesh N h →
        y.1.2 ∈ Sum.inl '' closedCostBin a (a+H) := by
    filter_upwards [sourceTransition_live_support hwn hell hS0 hS hr hs hsS mesh h z flag] with y hsupport
    intro hy
    rcases y with ⟨⟨py,ry⟩,fy⟩
    cases py with
    | none => exact False.elim hy.2
    | some k =>
      cases ry with
      | inr u => exact False.elim hy.1
      | inl q =>
        obtain ⟨p,hp,rfl⟩ := hsupport.1
        have hl : label (zero_lt_one.trans hw) htop hxi (h.primes.getLastD 0)=label (zero_lt_one.trans hw) htop hxi p := by
          simpa only [History.append_primes,List.getLastD_concat] using hy.2.1
        have hx : X ≤ primeExponent w p := by simpa only [History.append_node,step] using hy.2.2
        have hslack := (actual_same_bin_slack hw htop hell hxi hr hs hcap h hne p hp hl).2
        have hupper : (h.append p hp).node.ratio-(h.node.ratio-1) ≤ U*(xi/Real.log w)/X := by
          calc
            _ ≤ h.node.ratio*(xi/Real.log w)/primeExponent w p := hslack
            _ ≤ U*(xi/Real.log w)/primeExponent w p :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hparent hh0) (hX.trans_le hx).le
            _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hU hh0) hX hx
        have hInt := matched_repeat_interval (stateSide z.1) hgood.2.2.1 hy.1.2.2.1 hupper hsupport.2
        refine ⟨q,⟨hInt.1,?_⟩,rfl⟩
        simpa only [H,add_assoc] using hInt.2
  calc
    _ ≤ sourceTransition hwn hell hS0 hS hr hs hsS mesh ((some h,Sum.inl z),flag)
        ((fun y => y.1.2) ⁻¹' (Sum.inl '' closedCostBin a (a+H))) := measure_mono_ae hdom
    _ = continuousChain (Real.log start.gap) ell S (.inl z) (Sum.inl '' closedCostBin a (a+H)) := by
      have hmR : Measurable (fun y : FlagState (JointState w ell S start) => y.1.2) :=
        measurable_snd.comp measurable_fst
      rw [← Measure.map_apply hmR hT,
        sourceTransition_right hwn hell hS0 hS hr hs hsS]
    _ ≤ ENNReal.ofReal (repeatDensityConstant*(1+(U+1))^2)*ENNReal.ofReal ((a+H)-a) :=
      (Classical.choose_spec completed_parent_interval_upper).2 _ _ _ _ _ _ z hzU
    _ = _ := by
      rw [add_sub_cancel_left,← ENNReal.ofReal_mul (mul_nonneg repeatDensityConstant_pos.le (sq_nonneg _))]
      congr 1
      unfold repeatBudget H
      ring
end NumberTheoryLean.RepeatedStepRowBound


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

theorem goodRepeatPair_measurable {n : ℕ} (lab : ℕ → Fin n) (X U : ℝ) (G : Set (ChainState w ell S start))
    (v mesh : ℝ) (N : ℕ) : MeasurableSet (goodRepeatPair lab X U G v mesh N) := by
  have hp : MeasurableSet {pq : ChainState w ell S start × ChainState w ell S start | primeRepeatPair lab X U G pq} :=
    (Set.to_countable _).measurableSet
  have hm : Measurable (fun xy : FlagState (JointState w ell S start) × FlagState (JointState w ell S start) =>
      (xy.1.1.1,xy.2.1.1)) := by fun_prop
  exact ((measurable_fst.comp measurable_fst) (GoodAt_measurable v mesh N)).inter
    (((measurable_fst.comp measurable_snd) (GoodAt_measurable v mesh N)).inter (hm hp))

theorem primeRepeatPair_left {n : ℕ} (lab : ℕ → Fin n) {X U : ℝ} {G : Set (ChainState w ell S start)}
    {p q : ChainState w ell S start} (hp : primeRepeatPair lab X U G (p,q)) :
    ∃ h : History w ell S start,p=some h ∧ h.primes ≠ [] ∧ h.node.ratio ≤ U ∧ p ∈ G := by
  cases p with
  | none => exact False.elim hp
  | some h =>
    cases q with
    | none => exact False.elim hp
    | some k => exact ⟨h,rfl,hp.1,hp.2.1,hp.2.2.1⟩

theorem primeRepeatPair_next {n : ℕ} (lab : ℕ → Fin n) {X U : ℝ} {G : Set (ChainState w ell S start)}
    (h : History w ell S start) (y : FlagState (JointState w ell S start))
    (hp : primeRepeatPair lab X U G (some h,y.1.1)) : nextRepeat lab X h y := by
  cases hy : y.1.1 with
  | none => rw [hy] at hp; exact False.elim hp
  | some k =>
    rw [hy] at hp
    unfold nextRepeat
    rw [hy]
    exact hp.2.2.2

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RepeatedPairRow
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RepeatedPairRow
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain ActualProcessCoupling
open ActualCoupledHistories ActualFlagInvariant PersistentFailureFlag
open RepeatedStepRowBound RepeatedPairEvents FiniteHistoryPairLaw
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels

attribute [local instance] Classical.propDecidable

theorem repeatBudget_nonneg {U X xi w mesh : ℝ} (hU : 0 ≤ U) (hX : 0 < X)
    (hxi : 0 ≤ xi) (hw : 1 < w) (hm : 0 ≤ mesh) : 0 ≤ repeatBudget U X xi w mesh := by
  have hC := repeatDensityConstant_pos
  have hlog := Real.log_pos hw
  unfold repeatBudget
  positivity

variable {w ell S : ℝ} {start : Node}
variable (hwn : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem repeated_pair_row_uniform {top xi U X mesh : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hU : 0 ≤ U) (hX : 0 < X)
    (hm : 0 < mesh) (hmesh : mesh ≤ 1) (hcap : w^start.cutoff=top)
    (N : ℕ) (G : Set (ChainState w ell S start)) (x : FlagState (JointState w ell S start)) :
    pairProbability (sourceTransition hwn hell hS0 hS hr hs hsS mesh)
      (goodRepeatPair (label (zero_lt_one.trans hw) htop hxi) X U G (Real.log start.gap) mesh N) x ≤
        ENNReal.ofReal (repeatBudget U X xi w mesh) := by
  let E := goodRepeatPair (label (zero_lt_one.trans hw) htop hxi) X U G (Real.log start.gap) mesh N
  by_cases hmem : ((Prod.mk x) ⁻¹' E).Nonempty
  · obtain ⟨y,hy⟩ := hmem
    obtain ⟨h,hleft,hne,hparent,_hG⟩ := primeRepeatPair_left _ hy.2.2
    rcases x with ⟨⟨px,rx⟩,flag⟩
    change px=some h at hleft
    subst px
    cases rx with
    | inr u => exact False.elim hy.1
    | inl z =>
      have hsub : ((Prod.mk ((some h,Sum.inl z),flag)) ⁻¹' E) ⊆
          goodRepeatNext (label (zero_lt_one.trans hw) htop hxi) X (Real.log start.gap) mesh N h := by
        intro y' hy'
        exact ⟨hy'.2.1,primeRepeatPair_next _ h y' hy'.2.2⟩
      exact (measure_mono hsub).trans
        (good_repeat_next_row hwn hell hS0 hS hr hs hsS hw htop hxi hU hX hm hmesh hcap N h hne z flag hy.1 hparent)
  · have he : ((Prod.mk x) ⁻¹' E)=∅ := Set.not_nonempty_iff_eq_empty.mp hmem
    change sourceTransition hwn hell hS0 hS hr hs hsS mesh x ((Prod.mk x) ⁻¹' E) ≤ _
    rw [he,measure_empty]
    exact zero_le

theorem repeated_pair_row_gated {top xi U X mesh : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hU : 0 ≤ U) (hX : 0 < X)
    (hm : 0 < mesh) (hmesh : mesh ≤ 1) (hcap : w^start.cutoff=top)
    (N : ℕ) (G : Set (ChainState w ell S start)) (x : FlagState (JointState w ell S start)) :
    pairProbability (sourceTransition hwn hell hS0 hS hr hs hsS mesh)
      (goodRepeatPair (label (zero_lt_one.trans hw) htop hxi) X U G (Real.log start.gap) mesh N) x ≤
        ENNReal.ofReal (repeatBudget U X xi w mesh*(if x.1.1 ∈ G then 1 else 0)) := by
  by_cases hx : x.1.1 ∈ G
  · rw [ite_eq_left hx,mul_one]
    exact repeated_pair_row_uniform hwn hell hS0 hS hr hs hsS hw htop hxi hU hX hm hmesh hcap N G x
  · rw [ite_eq_right hx,mul_zero,ENNReal.ofReal_zero]
    let E := goodRepeatPair (label (zero_lt_one.trans hw) htop hxi) X U G (Real.log start.gap) mesh N
    have he : ((Prod.mk x) ⁻¹' E)=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      obtain ⟨h,_he,_hn,_hU,hG⟩ := primeRepeatPair_left _ hy.2.2
      exact hx hG
    change sourceTransition hwn hell hS0 hS hr hs hsS mesh x ((Prod.mk x) ⁻¹' E) ≤ 0
    rw [he,measure_empty]
end NumberTheoryLean.RepeatedPairRow


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_RepeatedPairProbability
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RepeatedPairProbability
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain ActualProcessCoupling
open ActualCoupledHistories ActualFlagInvariant ActualSuccessfulHistories PersistentFailureFlag
open RepeatedStepRowBound RepeatedPairEvents RepeatedPairRow
open FiniteHistoryTransport FiniteHistoryOccurrence FiniteHistoryPairLaw FinitePairOccurrence
open PrimeCompactVisits PrimeHistoryCompactCount
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels

attribute [local instance] Classical.propDecidable
variable {w ell S : ℝ} {start : Node}

theorem compact_gate_visit (L : ℝ) (p : ChainState w ell S start) :
    (if p ∈ compactParentGate L then (1:ℝ) else 0)=visit L p := by
  cases p with
  | none => simp [compactParentGate,visit]
  | some h => rfl

variable (hwn : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem raw_repeat_good_on_success {n : ℕ} (lab : ℕ → Fin n) (X U : ℝ) (G : Set (ChainState w ell S start))
    {mesh : ℝ} (hm : 0 < mesh) (N : ℕ) :
    ∀ᵐ h ∂sourceHistoryLaw hwn hell hS0 hS hr hs hsS mesh N,
      (last N h).2=false → h ∈ pairOccurrence (rawRepeatPair lab X U G) N →
        h ∈ pairOccurrence (goodRepeatPair lab X U G (Real.log start.gap) mesh N) N := by
  filter_upwards [sourceHistory_success_good hwn hell hS0 hS hr hs hsS hm N] with h hh
  intro hf hraw
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hraw
  apply Set.mem_iUnion.mpr
  refine ⟨j,?_,?_,hj⟩
  · exact goodAt_enlarge hm.le j.isLt.le _ (hh hf ⟨j.1,Finset.mem_Iic.mpr j.isLt.le⟩)
  · exact goodAt_enlarge hm.le (show j.1+1 ≤ N by have := j.isLt; omega) _
      (hh hf ⟨j.1+1,Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩)

theorem raw_repeat_probability_le_good {n : ℕ} (lab : ℕ → Fin n) (X U : ℝ) (G : Set (ChainState w ell S start))
    {mesh : ℝ} (hm : 0 < mesh) (N : ℕ) :
    sourceHistoryLaw hwn hell hS0 hS hr hs hsS mesh N (pairOccurrence (rawRepeatPair lab X U G) N) ≤
      FlaggedSourceStart.sourceLaw hwn hell hS0 hS hr hs hsS mesh N failed+
        sourceHistoryLaw hwn hell hS0 hS hr hs hsS mesh N
          (pairOccurrence (goodRepeatPair lab X U G (Real.log start.gap) mesh N) N) := by
  have hsub : ∀ᵐ h ∂sourceHistoryLaw hwn hell hS0 hS hr hs hsS mesh N,
      h ∈ pairOccurrence (rawRepeatPair lab X U G) N → h ∈ {h | (last N h).2=true} ∪
        pairOccurrence (goodRepeatPair lab X U G (Real.log start.gap) mesh N) N := by
    filter_upwards [raw_repeat_good_on_success hwn hell hS0 hS hr hs hsS lab X U G hm N] with h hh
    intro hp
    cases hf : (last N h).2 with
    | false => exact Or.inr (hh hf hp)
    | true => exact Or.inl hf
  calc
    _ ≤ sourceHistoryLaw hwn hell hS0 hS hr hs hsS mesh N ({h | (last N h).2=true} ∪
        pairOccurrence (goodRepeatPair lab X U G (Real.log start.gap) mesh N) N) := measure_mono_ae hsub
    _ ≤ _ := by
      rw [← sourceHistory_failure_probability hwn hell hS0 hS hr hs hsS mesh N]
      exact measure_union_le _ _

theorem good_repeat_probability_uniform {top xi U X mesh : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hU : 0 ≤ U) (hX : 0 < X)
    (hm : 0 < mesh) (hmesh : mesh ≤ 1) (hcap : w^start.cutoff=top)
    (N : ℕ) (G : Set (ChainState w ell S start)) :
    sourceHistoryLaw hwn hell hS0 hS hr hs hsS mesh N
      (pairOccurrence (goodRepeatPair (label (zero_lt_one.trans hw) htop hxi) X U G (Real.log start.gap) mesh N) N) ≤
        ENNReal.ofReal ((N:ℝ)*repeatBudget U X xi w mesh) := by
  exact pair_occurrence_of_uniform_row _ (goodRepeatPair_measurable _ _ _ _ _ _ _) N _
    (repeatBudget_nonneg hU hX hxi.le hw hm.le)
    (repeated_pair_row_uniform hwn hell hS0 hS hr hs hsS hw htop hxi hU hX hm hmesh hcap N G)

theorem good_repeat_probability_compact {top xi L mesh : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hL : 0 ≤ L)
    (hm : 0 < mesh) (hmesh : mesh ≤ 1) (hcap : w^start.cutoff=top) (N : ℕ) :
    sourceHistoryLaw hwn hell hS0 hS hr hs hsS mesh N
      (pairOccurrence (goodRepeatPair (label (zero_lt_one.trans hw) htop hxi) 1 L (compactParentGate L)
        (Real.log start.gap) mesh N) N) ≤ ENNReal.ofReal (repeatBudget L 1 xi w mesh*(L+1)) := by
  let A := repeatBudget L 1 xi w mesh
  have hA : 0 ≤ A := repeatBudget_nonneg hL (by norm_num) hxi.le hw hm.le
  apply pair_occurrence_of_budget _ (goodRepeatPair_measurable _ _ _ _ _ _ _) N _
    (fun x : FlagState (JointState w ell S start) => A*visit L x.1.1)
    (fun x => mul_nonneg hA (visit_nonneg L _)) (A*(L+1))
  · intro x
    have hh := repeated_pair_row_gated hwn hell hS0 hS hr hs hsS hw htop hxi hL (show (0:ℝ)<1 by norm_num) hm hmesh hcap N
      (compactParentGate L) x
    simpa only [compact_gate_visit] using hh
  · filter_upwards [sourceHistory_compact_count hwn hell hS0 hS hr hs hsS hL mesh N] with h hh
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hh hA

theorem raw_repeat_probability_compact {top xi L mesh : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hL : 0 ≤ L)
    (hm : 0 < mesh) (hmesh : mesh ≤ 1) (hcap : w^start.cutoff=top) (N : ℕ) :
    sourceHistoryLaw hwn hell hS0 hS hr hs hsS mesh N
      (pairOccurrence (rawRepeatPair (label (zero_lt_one.trans hw) htop hxi) 1 L (compactParentGate L)) N) ≤
        FlaggedSourceStart.sourceLaw hwn hell hS0 hS hr hs hsS mesh N failed+
          ENNReal.ofReal (repeatBudget L 1 xi w mesh*(L+1)) :=
  (raw_repeat_probability_le_good hwn hell hS0 hS hr hs hsS _ 1 L (compactParentGate L) hm N).trans
    (add_le_add le_rfl (good_repeat_probability_compact hwn hell hS0 hS hr hs hsS hw htop hxi hL hm hmesh hcap N))
end NumberTheoryLean.RepeatedPairProbability


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_SourceRepeatedRates
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RepeatedBudgetRate
open _root_.Filter RepeatedStepRowBound ExponentialMesh
open scoped Topology

theorem search_repeat_budget_small {A κ : ℝ} (hA : 0 ≤ A) (hκ : 0 < κ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ w : ℝ in atTop,∀ S xi : ℝ,0 ≤ S → S ≤ (Real.log w)^3 → 0 ≤ xi → xi ≤ 1 →
      ∀ N : ℕ,(N:ℝ) ≤ A*(Real.log w)^3 →
      (N:ℝ)*repeatBudget S (w^((1/4:ℝ))) xi w (mesh κ w) ≤ eps := by
  have hC := repeatDensityConstant_pos
  have ht : Tendsto (fun w : ℝ => (Real.log w)^12/w^((1/4:ℝ))) atTop (𝓝 0) := by
    simpa only [Real.rpow_ofNat] using
      (isLittleO_log_rpow_rpow_atTop (12:ℝ) (s := (1/4:ℝ)) (by norm_num)).tendsto_div_nhds_zero
  have hsum : Tendsto (fun w : ℝ => 9*A*repeatDensityConstant*((Real.log w)^12/w^((1/4:ℝ)))+
      18*A*repeatDensityConstant*(Real.log w)^9*Real.exp (-κ*Real.sqrt (Real.log w))) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add] using
      (ht.const_mul (9*A*repeatDensityConstant)).add (log_power_exp_tendsto (18*A*repeatDensityConstant) 9 hκ)
  filter_upwards [hsum.eventually (eventually_le_nhds heps),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_gt_atTop (1:ℝ)] with w hbound hlog hw
  intro S xi hS0 hS hxi0 hxi1 N hN
  have hm : 0 ≤ mesh κ w := (mesh_pos κ w).le
  have hX : 0 < w^((1/4:ℝ)) := Real.rpow_pos_of_pos (zero_lt_one.trans hw) _
  have hL3 : 1 ≤ (Real.log w)^3 := one_le_pow₀ hlog
  have hSplus : S+2 ≤ 3*(Real.log w)^3 := by linarith
  have hsrc : xi/Real.log w ≤ 1 := (div_le_self hxi0 hlog).trans hxi1
  have hsrc0 : 0 ≤ xi/Real.log w := div_nonneg hxi0 (Real.log_pos hw).le
  have hcoef : (N:ℝ)*repeatDensityConstant*(S+2)^2 ≤ 9*A*repeatDensityConstant*(Real.log w)^9 := by
    calc
      _ ≤ (A*(Real.log w)^3)*repeatDensityConstant*(3*(Real.log w)^3)^2 := by gcongr
      _ = _ := by ring
  have hnum : S*(xi/Real.log w) ≤ (Real.log w)^3 := by nlinarith [mul_le_mul_of_nonneg_left hsrc hS0]
  have hwidth : S*(xi/Real.log w)/w^((1/4:ℝ))+2*mesh κ w ≤
      (Real.log w)^3/w^((1/4:ℝ))+2*Real.exp (-κ*Real.sqrt (Real.log w)) :=
    add_le_add (div_le_div_of_nonneg_right hnum hX.le) (mul_le_mul_of_nonneg_left (mesh_upper κ w) (by norm_num))
  calc
    _ = ((N:ℝ)*repeatDensityConstant*(S+2)^2)*(S*(xi/Real.log w)/w^((1/4:ℝ))+2*mesh κ w) := by
      unfold repeatBudget
      ring
    _ ≤ (9*A*repeatDensityConstant*(Real.log w)^9)*
        ((Real.log w)^3/w^((1/4:ℝ))+2*Real.exp (-κ*Real.sqrt (Real.log w))) :=
      mul_le_mul hcoef hwidth (show 0 ≤ S*(xi/Real.log w)/w^((1/4:ℝ))+2*mesh κ w by positivity)
        (show 0 ≤ 9*A*repeatDensityConstant*(Real.log w)^9 by positivity)
    _ = 9*A*repeatDensityConstant*((Real.log w)^12/w^((1/4:ℝ)))+
        18*A*repeatDensityConstant*(Real.log w)^9*Real.exp (-κ*Real.sqrt (Real.log w)) := by ring
    _ ≤ _ := hbound

theorem compact_repeat_budget_small {L κ : ℝ} (hL : 0 ≤ L) (hκ : 0 < κ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ w : ℝ in atTop,∀ xi : ℝ,0 ≤ xi → xi ≤ 1 →
      repeatBudget L 1 xi w (mesh κ w)*(L+1) ≤ eps := by
  have hC := repeatDensityConstant_pos
  have ht : Tendsto (fun w : ℝ => 1/Real.log w) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hsum : Tendsto (fun w : ℝ => repeatDensityConstant*(L+2)^2*(L+1)*
      (L*(1/Real.log w)+2*Real.exp (-κ*Real.sqrt (Real.log w)))) atTop (𝓝 0) := by
    have hh := ((ht.const_mul L).add (log_power_exp_tendsto 2 0 hκ)).const_mul (repeatDensityConstant*(L+2)^2*(L+1))
    simpa only [pow_zero,mul_one,mul_zero,add_zero] using hh
  filter_upwards [hsum.eventually (eventually_le_nhds heps),eventually_gt_atTop (1:ℝ)] with w hw hw1
  intro xi hxi0 hxi1
  have hlog := Real.log_pos hw1
  have hxi : xi/Real.log w ≤ 1/Real.log w := div_le_div_of_nonneg_right hxi1 hlog.le
  have hwidth := add_le_add (mul_le_mul_of_nonneg_left hxi hL) (mul_le_mul_of_nonneg_left (mesh_upper κ w) (by norm_num : (0:ℝ)≤2))
  calc
    _ = (repeatDensityConstant*(L+2)^2*(L+1))*(L*(xi/Real.log w)+2*mesh κ w) := by unfold repeatBudget; ring
    _ ≤ (repeatDensityConstant*(L+2)^2*(L+1))*(L*(1/Real.log w)+2*Real.exp (-κ*Real.sqrt (Real.log w))) :=
      mul_le_mul_of_nonneg_left hwidth (by positivity)
    _ ≤ _ := hw
end NumberTheoryLean.RepeatedBudgetRate



namespace NumberTheoryLean.SourceRepeatedRates
open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open ActualCoupledHistories FlaggedSourceStart SourceSelectedCompactOccupation SourceCouplingRate
open RepeatedStepRowBound RepeatedPairEvents RepeatedPairProbability RepeatedBudgetRate
open FinitePairOccurrence ExponentialMesh LowStateHorizon PersistentFailureFlag
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels

theorem source_repeated_pair_probabilities_jb247_oai : ∃ κ₀ : ℝ,0 < κ₀ ∧
    ∀ κ : ℝ,0 < κ → κ ≤ κ₀ → ∀ D L eps : ℝ,0 < D → 0 ≤ L → 0 < eps →
    ∃ w₀ : ℝ,1 < w₀ ∧ ∀ w : ℝ,w₀ ≤ w → ∃ hw : 1 < w,
      ∀ top : ℝ,∀ htop : w < top,∀ ell B : ℝ,
      ∀ start : Node,∀ hs : Valid start.side start.ratio,
      1 ≤ ell → 0 < B → 2 ≤ Real.log B → Real.log B ≤ D*Real.log w →
      0 < start.gap → start.ratio ≤ 23/10 → Consistent start → start.gap ≤ (23/10:ℝ)*B → w^start.cutoff=top →
      ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ 1 →
      let S := (Real.log B)^2
      let N := sourceHorizon S B
      (fullSourceLaw w ell S start hs (mesh κ w) N
        (pairOccurrence (rawRepeatPair (label (zero_lt_one.trans hw) htop hxi) (w^((1/4:ℝ))) S Set.univ) N) ≤ ENNReal.ofReal eps) ∧
      (fullSourceLaw w ell S start hs (mesh κ w) N
        (pairOccurrence (rawRepeatPair (label (zero_lt_one.trans hw) htop hxi) 1 L (compactParentGate L)) N) ≤ ENNReal.ofReal eps) := by
  obtain ⟨κ₀,hκ₀,hCouple⟩ := source_coupling_rate_jb247
  refine ⟨κ₀,hκ₀,?_⟩
  intro κ hκ hκle D L eps hD hL heps
  obtain ⟨WC,hWC,hC⟩ := hCouple κ hκ hκle D hD
  have hA : 0 ≤ 5*D^3 := by positivity
  have hEvents := (search_repeat_budget_small hA hκ (show 0 < eps/2 by positivity)).and
    ((compact_repeat_budget_small hL hκ (show 0 < eps/2 by positivity)).and
      (((log_power_exp_tendsto 1 0 (show 0 < κ/2 by positivity)).eventually
        (eventually_le_nhds (show 0 < eps/2 by positivity))).and
        (Real.tendsto_log_atTop.eventually_ge_atTop (D^2))))
  obtain ⟨W,hW⟩ := eventually_atTop.mp hEvents
  refine ⟨max WC (max normalizationThreshold W),hWC.trans_le (le_max_left _ _),?_⟩
  intro w hw₀
  have hnorm : normalizationThreshold ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw₀
  have hw : 1 < w := normalizationThreshold_gt_one.trans_le hnorm
  refine ⟨hw,?_⟩
  intro top htop ell B start hs hell hB hlogB hcomp hr hs23 hc hsize hcap xi hxi hxi1
  dsimp only
  have hwC : WC ≤ w := (le_max_left _ _).trans hw₀
  have hwe := hW w ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hw₀)
  have hscale := UniformBudgetRate.source_scale_bound hwe.2.2.2 hlogB hcomp
  have hS0 : 0 ≤ (Real.log B)^2 := sq_nonneg _
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  let N := sourceHorizon ((Real.log B)^2) B
  have hf := (hC w hwC ell B start hs hell hB hlogB hcomp hr hs23 hc hsize).1 N le_rfl |>.1
  have hfail : Real.exp (-(κ/2)*Real.sqrt (Real.log w)) ≤ eps/2 := by
    simpa only [pow_zero,mul_one,one_mul] using hwe.2.2.1
  have hf' : FlaggedSourceStart.sourceLaw hnorm hell hS0 hscale.1 hr hs hsS (mesh κ w) N failed ≤ ENNReal.ofReal (eps/2) :=
    hf.trans (ENNReal.ofReal_le_ofReal hfail)
  have hm := mesh_pos κ w
  have hmesh := mesh_le_one hκ.le w
  have hSearch := hwe.1 ((Real.log B)^2) xi hS0 hscale.1 hxi.le hxi1 N hscale.2
  have hCompact := hwe.2.1 xi hxi.le hxi1
  have hsum : ENNReal.ofReal (eps/2)+ENNReal.ofReal (eps/2)=ENNReal.ofReal eps := by
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ eps/2) (by positivity : 0 ≤ eps/2)]
    congr 1
    ring
  constructor
  · have hraw := raw_repeat_probability_le_good hnorm hell hS0 hscale.1 hr hs hsS
      (label (zero_lt_one.trans hw) htop hxi) (w^((1/4:ℝ))) ((Real.log B)^2) Set.univ hm N
    have hgood := good_repeat_probability_uniform hnorm hell hS0 hscale.1 hr hs hsS hw htop hxi hS0
      (Real.rpow_pos_of_pos (zero_lt_one.trans hw) (1/4:ℝ)) hm hmesh hcap N Set.univ
    exact hraw.trans ((add_le_add hf' (hgood.trans (ENNReal.ofReal_le_ofReal hSearch))).trans_eq hsum)
  · have hraw := raw_repeat_probability_compact hnorm hell hS0 hscale.1 hr hs hsS hw htop hxi hL hm hmesh hcap N
    exact hraw.trans ((add_le_add hf' (ENNReal.ofReal_le_ofReal hCompact)).trans_eq hsum)
end NumberTheoryLean.SourceRepeatedRates


end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.NumberTheoryLean.SourceRepeatedRates.source_repeated_pair_probabilities_jb247_oai := @OAI.Erdos970.NumberTheoryLean.SourceRepeatedRates.source_repeated_pair_probabilities_jb247_oai
