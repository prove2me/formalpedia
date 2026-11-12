-- Prove2me | solution 1 for OAI.Erdos970.NumberTheoryLean.MarkedOccurrenceProbability.missing_occurrence_probability_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:05:56.451255+00:00
-- url     : https://prove2.me/submissions/bb187c50-6cb3-43f1-8dbc-278361964ad7

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

theorem nextGap_div_ratio {r t : ℝ} (ht : 0 < t) : nextGap r t / t = nextExponent r t := by
  unfold nextGap nextExponent
  field_simp

theorem nextRatio_identity {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    nextGap r t / nextExponent r t = t := by
  unfold nextGap nextExponent
  field_simp

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_MarkedVisitGeometry
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.RegenerativeOddOccupation.ratioVisits_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.CycleOccupation.pairSampling_isMarkovKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels NumberTheoryLean.RegenerationTails
open NumberTheoryLean.DerivativeWeights NumberTheoryLean.WeightFutureIntegrals
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.KernelDensityBridge

lemma sourceMark_true (t : EvenState) : sourceMark t = true ↔ t.1 ∈ Icc (209/100:ℝ) (213/100) := by
  simp [sourceMark]

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set
open scoped Topology
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathGeometry

lemma marked_draw_slack {b0 b1 r t : ℝ} (hb0 : 0 < b0)
    (hr0 : 10*b0 ≤ r) (hr1 : r ≤ b1) (ht0 : 209/100 ≤ t) (ht1 : t ≤ 213/100) :
    10*b0/(313/100) ≤ nextExponent r t ∧ nextExponent r t ≤ b1/(309/100) ∧
    2*b0 ≤ nextExponent r t ∧ nextExponent r t ≤ b1/2 ∧
    6*b0 < nextGap r t ∧ nextGap r t/nextExponent r t=t := by
  have hr : 0 < r := by linarith
  have ht : 0 < t := by linarith
  have htp : 0 < t+1 := by linarith
  have hlow : 10*b0/(313/100) ≤ nextExponent r t := by
    unfold nextExponent
    exact div_le_div₀ (by positivity) hr0 htp (by linarith)
  have hhi : nextExponent r t ≤ b1/(309/100) := by
    unfold nextExponent
    exact div_le_div₀ (hr.le.trans hr1) hr1 (by norm_num) (by linarith)
  have hlo2 : 2*b0 ≤ nextExponent r t := by
    apply (le_div_iff₀ htp).mpr
    nlinarith
  have hhi2 : nextExponent r t ≤ b1/2 := by
    unfold nextExponent
    exact div_le_div₀ (hr.le.trans hr1) hr1 (by norm_num) (by linarith)
  have hgap : 6*b0 < nextGap r t := by
    unfold nextGap
    apply (lt_div_iff₀ htp).mpr
    have hm := mul_le_mul_of_nonneg_right hr0 ht.le
    nlinarith
  exact ⟨hlow,hhi,hlo2,hhi2,hgap,nextRatio_identity hr ht⟩

lemma gapAt_le_iff {r B : ℝ} (hr : 0 < r) (hB : 0 < B) (T : ℝ) :
    gapAt r T ≤ B ↔ Real.log (r/B) ≤ T := by
  rw [gapAt,Real.exp_neg,← div_eq_mul_inv,div_le_iff₀ (Real.exp_pos T),
    Real.log_le_iff_le_exp (div_pos hr hB),div_le_iff₀ hB]
  simp only [mul_comm]

lemma le_gapAt_iff {r A : ℝ} (hr : 0 < r) (hA : 0 < A) (T : ℝ) :
    A ≤ gapAt r T ↔ T ≤ Real.log (r/A) := by
  rw [gapAt,Real.exp_neg,← div_eq_mul_inv,le_div_iff₀ (Real.exp_pos T),
    Real.le_log_iff_exp_le (div_pos hr hA),le_div_iff₀ hA]
  simp only [mul_comm]

lemma marked_cost_window {r b0 b1 : ℝ} (hr : 0 < r) (hb0 : 0 < b0) (hb1 : 0 < b1) (T : ℝ) :
    10*b0 ≤ gapAt r T ∧ gapAt r T ≤ b1 ↔
      Real.log (r/b1) ≤ T ∧ T ≤ Real.log (r/b1)+Real.log (b1/(10*b0)) := by
  have he : Real.log (r/(10*b0)) = Real.log (r/b1)+Real.log (b1/(10*b0)) := by
    rw [Real.log_div hr.ne' (by positivity),Real.log_div hr.ne' hb1.ne',
      Real.log_div hb1.ne' (by positivity)]
    ring
  rw [le_gapAt_iff hr (by positivity),gapAt_le_iff hr hb1,he,and_comm]

end Erdos970Dependency.MarkedVisits

end

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

theorem currentExponent_update (v : ℝ) (z : CostState) (s : State) :
    currentExponent v (s, z.2 + cost (stateRatio s)) = nextExponent (gapValue v z) (stateRatio s) := by
  change gapValue v (s, z.2 + cost (stateRatio s)) / stateRatio s = _
  rw [gapValue_update, nextGap_div_ratio (stateRatio_pos s)]

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_RawIncreasingPrefix
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarginalDensityMeasures.initialTwoMeasure_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualCoupledHistories.sourceHistoryLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.ActualCoupledHistories.sourceTransition_markov _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointPathLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.continuousParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.jointKernel_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ContinuousKilledBins.continuousChain_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.CostPrefixTransport.costKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedSourceStart.sourceLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.PrimeKilledChain.instMeasurableSpaceChainState _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
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
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.TransitionKernels

lemma actualCostKernel_strict (z : CostState) : ∀ᵐ y ∂costKernel z, z.2 < y.2 := by
  have hm : MeasurableSet {y : CostState | z.2 < y.2} := measurableSet_lt measurable_const measurable_snd
  apply (ae_mem_iff_measure_eq hm.nullMeasurableSet).mpr
  rw [costKernel_apply z hm]
  have he : {s : State | z.2 < (s,z.2+cost (stateRatio s)).2}=univ := by
    apply eq_univ_of_forall
    intro s
    have hp := cost_pos (valid_pos (stateRatio_valid s))
    exact lt_add_of_pos_right z.2 hp
  simp only [mem_ofPred_eq]
  rw [he]
  simp

lemma rawExtension_strict_step (k : ℕ) (h : RawHistory k) :
    ∀ᵐ y ∂rawExtension k (k+1) h,
      (y ⟨k,Finset.mem_Iic.mpr (by omega)⟩).2 < (rawLast (k+1) y).2 := by
  have hs : ∀ᵐ y ∂rawExtension k (k+1) h, (rawLast k h).2 < (rawLast (k+1) y).2 := by
    apply (ae_map_iff (rawLast_measurable (k+1)).aemeasurable
      (measurableSet_lt measurable_const measurable_snd)).mp
    rw [rawExtension_last_step]
    exact actualCostKernel_strict _
  filter_upwards [hs,rawExtension_retains_prefix (show k ≤ k+1 by omega) h] with y hy hp
  have he := congrFun hp (⟨k,by simp⟩ : Finset.Iic k)
  change y ⟨k,_⟩=rawLast k h at he
  rw [he]
  exact hy

lemma rawExtension_strict_coordinate {a b k : ℕ} (hak : a ≤ k) (hkb : k < b) (h : RawHistory a) :
    ∀ᵐ y ∂rawExtension a b h,
      (y ⟨k,Finset.mem_Iic.mpr (by omega)⟩).2 <
        (y ⟨k+1,Finset.mem_Iic.mpr (by omega)⟩).2 := by
  have hm : MeasurableSet {y : RawHistory (k+1) |
      (y ⟨k,Finset.mem_Iic.mpr (by omega)⟩).2 < (rawLast (k+1) y).2} :=
    measurableSet_lt (measurable_snd.comp (measurable_pi_apply _))
      (measurable_snd.comp (rawLast_measurable _))
  have he : (rawExtension a b h).map (rawPrefix (show k+1 ≤ b by omega))=rawExtension a (k+1) h :=
    Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ => CostState) (κ := historyKernel) h (show k+1 ≤ b by omega)
  have ht : ∀ᵐ y ∂rawExtension a (k+1) h,
      (y ⟨k,Finset.mem_Iic.mpr (by omega)⟩).2 < (rawLast (k+1) y).2 := by
    have hc : rawExtension a (k+1)=rawExtension k (k+1) ∘ₖ rawExtension a k :=
      (Kernel.partialTraj_comp_partialTraj hak (by omega)).symm
    rw [hc]
    exact Kernel.ae_comp_of_ae_ae hm (Eventually.of_forall (rawExtension_strict_step k))
  rw [← he] at ht
  exact (ae_map_iff (rawPrefix_measurable (show k+1 ≤ b by omega)).aemeasurable hm).mp ht

lemma increasingCosts_of_steps {a b : ℕ} (h : RawHistory b)
    (hs : ∀ k : Fin b, a ≤ k.1 →
      (h ⟨k.1,Finset.mem_Iic.mpr (by have hk:=k.2; omega)⟩).2 ≤
        (h ⟨k.1+1,Finset.mem_Iic.mpr (by have hk:=k.2; omega)⟩).2) :
    h ∈ increasingCosts a b := by
  intro i j hai hij
  have aux : ∀ m, i.1 ≤ m → ∀ hm : m ≤ b, (h i).2 ≤ (h ⟨m,Finset.mem_Iic.mpr hm⟩).2 := by
    intro m him
    induction m,him using Nat.le_induction with
    | base => intro hm; exact le_rfl
    | succ m him ih =>
      intro hmb
      have hmb' : m < b := by omega
      exact (ih (by omega)).trans (hs ⟨m,hmb'⟩ (hai.trans him))
  exact aux j.1 hij (Finset.mem_Iic.mp j.2)

theorem rawExtension_increasingCosts (a b : ℕ) (h : RawHistory a) :
    ∀ᵐ y ∂rawExtension a b h, y ∈ increasingCosts a b := by
  have hs : ∀ᵐ y ∂rawExtension a b h, ∀ k : Fin b, a ≤ k.1 →
      (y ⟨k.1,Finset.mem_Iic.mpr (by have hk:=k.2; omega)⟩).2 <
        (y ⟨k.1+1,Finset.mem_Iic.mpr (by have hk:=k.2; omega)⟩).2 := by
    rw [ae_all_iff]
    intro k
    by_cases hak : a ≤ k.1
    · filter_upwards [rawExtension_strict_coordinate hak k.2 h] with y hy
      exact fun _ => hy
    · exact Eventually.of_forall (fun _ hy => (hak hy).elim)
  filter_upwards [hs] with y hy
  exact increasingCosts_of_steps y (fun k hk => (hy k hk).le)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RawSuppliedPast
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ActualCoupledHistories.sourceHistoryLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.ActualCoupledHistories.sourceTransition_markov _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointKernel_pow_markov _root_.OAI.Erdos970.NumberTheoryLean.ActualCouplingFinite.jointPathLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.continuousParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.jointKernel_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.ActualProcessCoupling.primeParent_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.AdmittedHarmonicPaths.admittedTilted_isFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.ContinuousKilledBins.continuousChain_isMarkov _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedSourceStart.sourceLaw_probability _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.TransitionKernels NumberTheoryLean.RegeneratingInverseBands
open NumberTheoryLean.ArrivalKernelGeometry

lemma gapValue_log_eq_gapAt {r : ℝ} (hr : 0 < r) (z : CostState) :
    gapValue (Real.log r) z=gapAt r z.2 := by
  unfold gapValue gapAt
  rw [Real.exp_sub,Real.exp_log hr,Real.exp_neg,div_eq_mul_inv]

end Erdos970Dependency.MarkedVisits

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
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
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

theorem live_prefix_preserved (E : Set X) (N k : ℕ) (hk : k ≤ N)
    (h : Hist X N) (z : X)
    (hz : killHist E N h ⟨k,Finset.mem_Iic.mpr hk⟩ = Sum.inl z)
    (j : ℕ) (hj : j ≤ k) :
    killHist E N h ⟨j,Finset.mem_Iic.mpr (hj.trans hk)⟩ =
      Sum.inl (h ⟨j,Finset.mem_Iic.mpr (hj.trans hk)⟩) := by
  have ha := (live_coordinate_original E N k hk h z hz).2
  have hjA : aliveThrough E j (frestrictLe₂ (π := fun _ => X) (hj.trans hk) h) := by
    intro i hi
    exact ha ⟨i,Finset.mem_Iic.mpr ((Finset.mem_Iic.mp i.2).trans hj)⟩ hi
  rw [killHist_coordinate E N j (hj.trans hk) h,ite_eq_left hjA]

end NumberTheoryLean.LiveKilledPrefixes

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_CompletedMarkEvents
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.CanonicalMarkSlack

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open FinitePathMeasures FinitePathGeometry ArrivalKernelGeometry RegeneratingInverseBands
open CanonicalCostCoordinates Erdos970Dependency.MarkedVisits

theorem firstArrivalMark_bounds (z : CostState) (hz : firstArrivalMark z = true) :
    stateSide z.1 = .even ∧ 209/100 ≤ stateRatio z.1 ∧ stateRatio z.1 ≤ 213/100 := by
  rcases z with ⟨s,T⟩
  cases s with
  | inl s =>
    have h := (sourceMark_true s).mp hz
    exact ⟨rfl,h.1,h.2⟩
  | inr s => exact Bool.noConfusion hz

theorem pair_hit_slack {r b₀ b₁ : ℝ} (hr : 0 < r) (hb₀ : 0 < b₀) (hb₁ : 0 < b₁)
    (a k N : ℕ) (hk : a+2*k+1 ≤ N) (h : RawHistory N)
    (htime : (h ⟨a+2*k+1,Finset.mem_Iic.mpr hk⟩).2 =
      (h ⟨a+2*k,Finset.mem_Iic.mpr (by omega)⟩).2 +
        cost (stateRatio (h ⟨a+2*k+1,Finset.mem_Iic.mpr hk⟩).1))
    (hHit : h ∈ pairHitTest a k N hk (Real.log (r/b₁)) (Real.log (b₁/(10*b₀)))) :
    let z := h ⟨a+2*k+1,Finset.mem_Iic.mpr hk⟩
    stateSide z.1 = .even ∧ 209/100 ≤ stateRatio z.1 ∧ stateRatio z.1 ≤ 213/100 ∧
      10*b₀/(313/100) ≤ currentExponent (Real.log r) z ∧
      currentExponent (Real.log r) z ≤ b₁/(309/100) ∧ 6*b₀ < gapValue (Real.log r) z := by
  dsimp only
  let pre := h ⟨a+2*k,Finset.mem_Iic.mpr (show a+2*k ≤ N by omega)⟩
  let z := h ⟨a+2*k+1,Finset.mem_Iic.mpr hk⟩
  have hmark := firstArrivalMark_bounds z hHit.2.1
  have hwindow := (marked_cost_window hr hb₀ hb₁ pre.2).mpr hHit.2.2
  have hslack := marked_draw_slack hb₀ hwindow.1 hwindow.2 hmark.2.1 hmark.2.2
  have hz : z = (z.1,pre.2+cost (stateRatio z.1)) := Prod.ext rfl htime
  have he : currentExponent (Real.log r) z = nextExponent (gapAt r pre.2) (stateRatio z.1) := by
    calc
      _ = currentExponent (Real.log r) (z.1,pre.2+cost (stateRatio z.1)) := congrArg _ hz
      _ = nextExponent (gapValue (Real.log r) pre) (stateRatio z.1) := currentExponent_update _ pre z.1
      _ = _ := by rw [gapValue_log_eq_gapAt hr]
  have hg : gapValue (Real.log r) z = nextGap (gapAt r pre.2) (stateRatio z.1) := by
    calc
      _ = gapValue (Real.log r) (z.1,pre.2+cost (stateRatio z.1)) := congrArg _ hz
      _ = nextGap (gapValue (Real.log r) pre) (stateRatio z.1) := gapValue_update _ pre z.1
      _ = _ := by rw [gapValue_log_eq_gapAt hr]
  exact ⟨hmark.1,hmark.2.1,hmark.2.2,he ▸ hslack.1,he ▸ hslack.2.1,hg ▸ hslack.2.2.2.2.1⟩

theorem canonical_all_marks_slack {r b₀ b₁ : ℝ} (hr : 0 < r) (hb₀ : 0 < b₀) (hb₁ : 0 < b₁)
    (s : State) (N : ℕ) :
    ∀ᵐ h ∂finitePathMeasure s N, ∀ a k : ℕ, ∀ hk : a+2*k+1 ≤ N,
      h ∈ pairHitTest a k N hk (Real.log (r/b₁)) (Real.log (b₁/(10*b₀))) →
      let z := h ⟨a+2*k+1,Finset.mem_Iic.mpr hk⟩
      stateSide z.1 = .even ∧ 209/100 ≤ stateRatio z.1 ∧ stateRatio z.1 ≤ 213/100 ∧
        10*b₀/(313/100) ≤ currentExponent (Real.log r) z ∧
        currentExponent (Real.log r) z ≤ b₁/(309/100) ∧ 6*b₀ < gapValue (Real.log r) z := by
  have hall : ∀ᵐ h ∂finitePathMeasure s N, ∀ j : Fin N,
      (h ⟨j.1+1,Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩).2 =
        (h ⟨j.1,Finset.mem_Iic.mpr j.isLt.le⟩).2 +
          cost (stateRatio (h ⟨j.1+1,Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩).1) := by
    apply ae_all_iff.mpr
    intro j
    exact raw_cost_coordinate (Nat.zero_le _) j.isLt (fun _ => (s,0))
  filter_upwards [hall] with h hh
  intro a k hk hHit
  exact pair_hit_slack hr hb₀ hb₁ a k N hk h
    (hh ⟨a+2*k,by omega⟩) hHit

end NumberTheoryLean.CanonicalMarkSlack

end

section

namespace NumberTheoryLean.CompletedMarkEvents

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures FiniteHistoryTransport CemeteryKernel
open ArrivalKernelGeometry RegeneratingInverseBands ActualCouplingUpdates

theorem strongMark_measurable (v b₀ b₁ : ℝ) : MeasurableSet {z | strongMark v b₀ b₁ z} :=
  (measurable_fst (side_set_measurable .even)).inter
    ((measurableSet_le measurable_const (stateRatio_measurable.comp measurable_fst)).inter
      ((measurableSet_le (stateRatio_measurable.comp measurable_fst) measurable_const).inter
        ((measurableSet_le measurable_const (currentExponent_measurable v)).inter
          (measurableSet_le (currentExponent_measurable v) measurable_const))))

theorem markedPoint_measurable (v b₀ b₁ : ℝ) : MeasurableSet {z | markedPoint v b₀ b₁ z} :=
  measurableSet_sum_iff.mpr ⟨strongMark_measurable _ _ _,MeasurableSet.empty⟩

theorem compactPoint_measurable (v R : ℝ) : MeasurableSet {z | compactPoint v R z} :=
  measurableSet_sum_iff.mpr ⟨measurableSet_le (gapValue_measurable v) measurable_const,MeasurableSet.empty⟩

theorem noStrongBefore_measurable (v b₀ b₁ : ℝ) (N k : ℕ) :
    MeasurableSet {h | noStrongBefore v b₀ b₁ N k h} := by
  simp only [noStrongBefore,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _hi
  exact ((measurable_pi_apply i) (markedPoint_measurable v b₀ b₁)).compl

theorem badCompactPath_measurable (v R b₀ b₁ : ℝ) (N : ℕ) :
    MeasurableSet (badCompactPath v R b₀ b₁ N) := by
  simp only [badCompactPath,Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro j
  exact ((measurable_pi_apply j) (compactPoint_measurable v R)).inter
    (noStrongBefore_measurable v b₀ b₁ N j.1)

end NumberTheoryLean.CompletedMarkEvents

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_CanonicalBadCompact
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.CanonicalBadCompact

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open FinitePathMeasures FinitePathGeometry FiniteHistoryTransport CemeteryKernel CemeteryHistoryMap
open LiveKilledPrefixes CompletedMarkEvents CanonicalMarkSlack CanonicalCoupledHistories
open RegeneratingInverseBands ArrivalKernelGeometry ContinuousKilledBins
open Erdos970Dependency.MarkedVisits

theorem canonical_bad_compact_subset {r R b₀ b₁ : ℝ}
    (hr : 0 < r) (hb₀ : 0 < b₀) (hb₁ : 0 < b₁) (hR : R < 6*b₀)
    (E : Set CostState) (s : State) (N : ℕ) :
    ∀ᵐ h ∂finitePathMeasure s N,
      killHist E N h ∈ badCompactPath (Real.log r) R b₀ b₁ N →
        h ∈ closedNoHitEvent 1 N r b₀ b₁ 1 := by
  have hCosts : ∀ᵐ h ∂finitePathMeasure s N, h ∈ increasingCosts 0 N :=
    rawExtension_increasingCosts 0 N (fun _ => (s,0))
  filter_upwards [canonical_all_marks_slack hr hb₀ hb₁ s N,hCosts] with h hMarks hCost
  rintro ⟨j,hcompact,hNo⟩
  cases hz : killHist E N h j with
  | inr u => rw [hz] at hcompact; exact False.elim hcompact
  | inl z =>
    rw [hz] at hcompact
    have horig := (live_coordinate_original E N j.1 (Finset.mem_Iic.mp j.2) h z hz).1
    have hgapj : gapValue (Real.log r) (h j) ≤ R := by rw [horig]; exact hcompact
    have hNoHit : h ∉ anyPairHit 1 N (Real.log (r/b₁)) (Real.log (b₁/(10*b₀))) := by
      rintro ⟨k,hk,hHit⟩
      have hslack := hMarks 1 k hk hHit
      let m : Finset.Iic N := ⟨1+2*k+1,Finset.mem_Iic.mpr hk⟩
      by_cases hmj : m.1 ≤ j.1
      · have hp := live_prefix_preserved E N j.1 (Finset.mem_Iic.mp j.2) h z hz m.1 hmj
        have hn := hNo m hmj
        rw [hp] at hn
        exact hn ⟨hslack.1,hslack.2.1,hslack.2.2.1,hslack.2.2.2.1,hslack.2.2.2.2.1⟩
      · have hcm := hCost j m (Nat.zero_le _) (by omega)
        have hgm : gapValue (Real.log r) (h m) ≤ gapValue (Real.log r) (h j) :=
          Real.exp_le_exp.mpr (sub_le_sub_left hcm _)
        have hsGap : 6*b₀ < gapValue (Real.log r) (h m) := hslack.2.2.2.2.2
        linarith
    refine ⟨hNoHit,Or.inl ?_⟩
    have hcN := hCost j ⟨N,by simp⟩ (Nat.zero_le _) (Finset.mem_Iic.mp j.2)
    have hgN : gapValue (Real.log r) (rawLast N h) ≤ gapValue (Real.log r) (h j) :=
      Real.exp_le_exp.mpr (sub_le_sub_left hcN _)
    rw [gapValue_log_eq_gapAt hr] at hgN
    linarith

theorem canonical_bad_compact_mass {r R b₀ b₁ : ℝ}
    (hr : 0 < r) (hb₀ : 0 < b₀) (hb₁ : 0 < b₁) (hR : R < 6*b₀)
    {E : Set CostState} (hE : MeasurableSet E) (s : State) (N : ℕ) :
    ((finitePathMeasure s N).map (killHist E N)) (badCompactPath (Real.log r) R b₀ b₁ N) ≤
      finitePathMeasure s N (closedNoHitEvent 1 N r b₀ b₁ 1) := by
  rw [Measure.map_apply (killHist_measurable hE N) (badCompactPath_measurable _ _ _ _ _)]
  exact measure_mono_ae (canonical_bad_compact_subset hr hb₀ hb₁ hR E s N)

theorem completed_bad_compact_mass {r R b₀ b₁ : ℝ}
    (hr : 0 < r) (hb₀ : 0 < b₀) (hb₁ : 0 < b₁) (hR : R < 6*b₀)
    (ell S : ℝ) (s : State) (N : ℕ) :
    pathKernel (continuousChain (Real.log r) ell S) N (fun _ => Sum.inl (s,0))
      (badCompactPath (Real.log r) R b₀ b₁ N) ≤
        finitePathMeasure s N (closedNoHitEvent 1 N r b₀ b₁ 1) := by
  rw [← canonical_killing_image s N (Real.log r) ell S]
  exact canonical_bad_compact_mass hr hb₀ hb₁ hR (LowStateHorizon.lowDomain_measurable _ _ _) s N

end NumberTheoryLean.CanonicalBadCompact

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SuccessfulMarkedCoordinates
attribute [-instance] _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.canonicalPairVisitKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedMarkedKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.completedPairHit_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveCapture_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.consecutiveFirstContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.cycleBranch_pow_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.extendFinitePrefix_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.firstNoHitHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.fullPairTraceKernel_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.instMeasurableSpaceRawCycleWordTrace _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markContinuation_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.markedReturnKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.noHitPairHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.nonregenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.oddConsecutiveContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryMarkedLoop_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.ordinaryWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairBranchKernel_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairStoppedHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairSurvivingHistory_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.pairWindowContinue_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawBeginningKernel_isSFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.rawExtension_isMarkovKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.regenerationInput_isFiniteKernel _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.sourceCycleLaw_isProbabilityMeasure _root_.OAI.Erdos970.Erdos970Dependency.MarkedVisits.unmarkedStar_isSFiniteKernel _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.MarkedWindowCouplingGeometry

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeBinMembership
open ActualFlagInvariant NearbyParentGeometry RegeneratingInverseBands ArrivalKernelGeometry

theorem window_stability {b₀ b₁ rp rc sp tc x : ℝ} (hb₀ : 0 < b₀)
    (ht₀ : 209/100 ≤ tc) (ht₁ : tc ≤ 213/100)
    (hx₀ : 10*b₀/(313/100) ≤ x) (hx₁ : x ≤ b₁/(309/100))
    (hcurve : rc = x*tc) (hpq : rp ≤ (11/10)*rc) (hqp : rc ≤ (11/10)*rp)
    (hnear : |sp-tc| ≤ 1/100) :
    208/100 ≤ sp ∧ sp ≤ 214/100 ∧ 2*b₀ ≤ rp/sp ∧ rp/sp ≤ b₁/2 ∧ 6*b₀ < rp := by
  have hs₀ : 208/100 ≤ sp := by linarith [(abs_le.mp hnear).1]
  have hs₁ : sp ≤ 214/100 := by linarith [(abs_le.mp hnear).2]
  have hsp : 0 < sp := by linarith
  have hx0 : 0 < x := (div_pos (by positivity) (by norm_num : 0 < (313/100:ℝ))).trans_le hx₀
  have hl : 10*b₀ ≤ x*(313/100) := (div_le_iff₀ (by norm_num : 0 < (313/100:ℝ))).mp hx₀
  have hu : x*(309/100) ≤ b₁ := (le_div_iff₀ (by norm_num : 0 < (309/100:ℝ))).mp hx₁
  have hb₁ : 0 < b₁ := by nlinarith
  have hrc₀ : (209/100)*x ≤ rc := by nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr ht₀)]
  have hrc₁ : rc ≤ (213/100)*x := by nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr ht₁)]
  have hgap : 6*b₀ < rp := by nlinarith
  refine ⟨hs₀,hs₁,?_,?_,hgap⟩
  · apply (le_div_iff₀ hsp).mpr
    nlinarith [mul_nonneg hb₀.le (sub_nonneg.mpr hs₁)]
  · apply (div_le_iff₀ hsp).mpr
    nlinarith [mul_nonneg hb₁.le (sub_nonneg.mpr hs₀)]

theorem actual_marked_window {w ell S v mesh b₀ b₁ : ℝ} {start : Node}
    {n : ℕ} (h : History w ell S start) (z : CostState)
    (hb₀ : 0 < b₀)
    (hpositive : 0 < h.node.gap) (hconsistent : Consistent h.node)
    (hgood : GoodAt v mesh n (some h,Sum.inl z))
    (heven : stateSide z.1 = .even)
    (ht₀ : 209/100 ≤ stateRatio z.1) (ht₁ : stateRatio z.1 ≤ 213/100)
    (hx₀ : 10*b₀/(313/100) ≤ currentExponent v z)
    (hx₁ : currentExponent v z ≤ b₁/(309/100))
    (hmesh : mesh ≤ 1/100) (herror : 4*(n:ℝ)*mesh ≤ Real.log (11/10)) :
    h.node.side = .even ∧ 208/100 ≤ h.node.ratio ∧ h.node.ratio ≤ 214/100 ∧
      2*b₀ ≤ h.node.cutoff ∧ h.node.cutoff ≤ b₁/2 ∧ 6*b₀ < h.node.gap := by
  change liveGood v mesh n h z at hgood
  have hrel := log_gap_relative hpositive (Real.exp_pos _) hgood.2.2.2
  have he : Real.exp (4*(n:ℝ)*mesh) ≤ (11/10:ℝ) := by
    rw [← Real.exp_log (by norm_num : 0 < (11/10:ℝ))]
    exact Real.exp_le_exp.mpr herror
  have hpq : h.node.gap ≤ (11/10)*gapValue v z :=
    hrel.1.trans (mul_le_mul_of_nonneg_right he (Real.exp_pos _).le)
  have hqp : gapValue v z ≤ (11/10)*h.node.gap :=
    hrel.2.trans (mul_le_mul_of_nonneg_right he hpositive.le)
  have hcurve : gapValue v z = currentExponent v z*stateRatio z.1 := by
    unfold currentExponent
    exact (div_mul_cancel₀ _ (OccupationBoundaries.stateRatio_pos z.1).ne').symm
  have hg := window_stability hb₀ ht₀ ht₁ hx₀ hx₁ hcurve hpq hqp (hgood.2.2.1.trans hmesh)
  refine ⟨hgood.2.1.trans heven,hg.1,hg.2.1,?_,?_,hg.2.2.2.2⟩
  · rw [hconsistent]
    exact hg.2.2.1
  · rw [hconsistent]
    exact hg.2.2.2.1

end NumberTheoryLean.MarkedWindowCouplingGeometry

end

section

namespace NumberTheoryLean.SuccessfulMarkedCoordinates

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open ActualProcessCoupling ActualFlagInvariant ActualCoupledHistories ActualSuccessfulHistories
open FiniteHistoryTransport MarkedWindowCouplingGeometry ArrivalKernelGeometry

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem sourceHistory_transports_marked_window (hc : Consistent start)
    {mesh : ℝ} (hm : 0 < mesh) (hmesh : mesh ≤ 1/100) (N : ℕ)
    (herror : 4*(N:ℝ)*mesh ≤ Real.log (11/10)) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      (last N h).2 = false → ∀ j : Finset.Iic N, ∀ z : CostState,
      (h j).1.2 = Sum.inl z → ∀ b₀ b₁ : ℝ, 0 < b₀ →
      stateSide z.1 = .even → 209/100 ≤ stateRatio z.1 → stateRatio z.1 ≤ 213/100 →
      10*b₀/(313/100) ≤ currentExponent (Real.log start.gap) z →
      currentExponent (Real.log start.gap) z ≤ b₁/(309/100) →
      ∃ p : History w ell S start, (h j).1.1 = some p ∧ primeWindow b₀ b₁ p.node := by
  filter_upwards [sourceHistory_success_good hw hell hS0 hS hr hs hsS hm N] with h hh
  intro hflag j z hz b₀ b₁ hb₀ heven ht₀ ht₁ hx₀ hx₁
  have hg := hh hflag j
  have he : 4*(j.1:ℝ)*mesh ≤ Real.log (11/10) := by
    have hj : (j.1:ℝ) ≤ N := by exact_mod_cast Finset.mem_Iic.mp j.2
    exact (by nlinarith : 4*(j.1:ℝ)*mesh ≤ 4*(N:ℝ)*mesh).trans herror
  have hg' : GoodAt (Real.log start.gap) mesh j.1 ((h j).1.1,Sum.inl z) := by
    simpa only [← hz] using hg
  cases hp : (h j).1.1 with
  | none =>
    rw [hp] at hg'
    exact False.elim hg'
  | some p =>
    rw [hp] at hg'
    refine ⟨p,rfl,?_⟩
    exact actual_marked_window p z hb₀
      (terminal_gap_positive (by linarith : 0 ≤ ell) hr hs p.admissible)
      (PrimeBinMembership.history_consistent (by linarith : 0 ≤ ell) hr hs hc p)
      hg' heven ht₀ ht₁ hx₀ hx₁ hmesh he

end NumberTheoryLean.SuccessfulMarkedCoordinates

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

theorem sourceHistory_prior_mark (hc : Consistent start)
    {mesh : ℝ} (hm : 0 < mesh) (hmesh : mesh ≤ 1/100) (N : ℕ)
    (herror : 4*(N:ℝ)*mesh ≤ Real.log (11/10)) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      (last N h).2 = false → ∀ i j : Finset.Iic N, i.1 ≤ j.1 →
      ∀ p : History w ell S start, (h j).1.1 = some p → ∀ z : CostState,
      (h i).1.2 = Sum.inl z → ∀ b₀ b₁ : ℝ, 0 < b₀ →
      stateSide z.1 = .even → 209/100 ≤ stateRatio z.1 → stateRatio z.1 ≤ 213/100 →
      10*b₀/(313/100) ≤ currentExponent (Real.log start.gap) z →
      currentExponent (Real.log start.gap) z ≤ b₁/(309/100) →
      hasPrimeWindow w b₀ b₁ start p.primes := by
  filter_upwards [sourceHistory_prior_live hw hell hS0 hS hr hs hsS mesh N,
    sourceHistory_transports_marked_window hw hell hS0 hS hr hs hsS hc hm hmesh N herror] with h hp hmks
  intro hflag i j hij p hpj z hzi b₀ b₁ hb₀ heven ht₀ ht₁ hx₀ hx₁
  obtain ⟨q,hqi,hwin⟩ := hmks hflag i z hzi b₀ b₁ hb₀ heven ht₀ ht₁ hx₀ hx₁
  obtain ⟨q',hqi',tail,happend⟩ := hp i j hij p hpj
  have heq : q' = q := Option.some.inj (hqi'.symm.trans hqi)
  subst q'
  exact ⟨q.primes,tail,happend,hwin⟩

end NumberTheoryLean.PriorPrimeWindow

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_SourceBadCompactOccurrence
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceBadCompactOccurrence

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open ActualCoupledHistories ActualSuccessfulHistories ActualFlagInvariant ActualProcessCoupling
open FiniteHistoryTransport PriorPrimeWindow CompactPrefixOccurrence CompletedMarkEvents
open RegeneratingInverseBands NearbyParentGeometry

variable {w ell S R b₀ b₁ : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem missing_occurrence_inclusion (hc : Consistent start) (hb₀ : 0 < b₀)
    {mesh : ℝ} (hm : 0 < mesh) (hmesh : mesh ≤ 1/100) (N : ℕ)
    (herror : 4*(N:ℝ)*mesh ≤ Real.log (11/10)) (E : Set (List ℕ))
    (hE : ∀ p : History w ell S start,p.primes ∈ E →
      p.node.gap ≤ R ∧ ¬hasPrimeWindow w b₀ b₁ start p.primes) :
    ∀ᵐ h ∂sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N,
      occurs E N h → (last N h).2 = true ∨
        mapHist (fun q => q.1.2) N h ∈ badCompactPath (Real.log start.gap) ((11/10)*R) b₀ b₁ N := by
  filter_upwards [sourceHistory_success_good hw hell hS0 hS hr hs hsS hm N,
    sourceHistory_prior_mark hw hell hS0 hS hr hs hsS hc hm hmesh N herror] with h hg hprior
  intro hocc
  by_cases hf : (last N h).2 = true
  · exact Or.inl hf
  have hfalse : (last N h).2 = false := by cases hval : (last N h).2 <;> simp_all
  obtain ⟨j,hjE⟩ := hocc
  let j' : Finset.Iic N := ⟨j,Finset.mem_Iic.mpr j.isLt.le⟩
  cases hp : (h j').1.1 with
  | none =>
    change selectedNode E (h j').1.1 at hjE
    rw [hp] at hjE
    exact False.elim hjE
  | some p =>
    change selectedNode E (h j').1.1 at hjE
    rw [hp] at hjE
    have hpE := hE p hjE
    have hgj : GoodAt (Real.log start.gap) mesh j'.1 (some p,(h j').1.2) := by
      simpa only [← hp] using hg hfalse j'
    cases hz : (h j').1.2 with
    | inr u => rw [hz] at hgj; exact False.elim hgj
    | inl z =>
      rw [hz] at hgj
      have hn : (j'.1:ℝ) ≤ N := by exact_mod_cast Finset.mem_Iic.mp j'.2
      have herr : 4*(j'.1:ℝ)*mesh ≤ Real.log (11/10) :=
        (by nlinarith : 4*(j'.1:ℝ)*mesh ≤ 4*(N:ℝ)*mesh).trans herror
      have he : Real.exp (4*(j'.1:ℝ)*mesh) ≤ (11/10:ℝ) := by
        rw [← Real.exp_log (by norm_num : 0 < (11/10:ℝ))]
        exact Real.exp_le_exp.mpr herr
      have hpPos := terminal_gap_positive (by linarith : 0 ≤ ell) hr hs p.admissible
      have hrel := log_gap_relative hpPos (Real.exp_pos _) hgj.2.2.2
      have hgap : gapValue (Real.log start.gap) z ≤ (11/10)*R :=
        hrel.2.trans ((mul_le_mul_of_nonneg_right he hpPos.le).trans
          (mul_le_mul_of_nonneg_left hpE.1 (by norm_num)))
      apply Or.inr
      refine ⟨j',?_,?_⟩
      · change compactPoint (Real.log start.gap) ((11/10)*R) (h j').1.2
        rw [hz]
        exact hgap
      · intro i hij hMark
        change markedPoint (Real.log start.gap) b₀ b₁ (h i).1.2 at hMark
        cases hi : (h i).1.2 with
        | inr u => rw [hi] at hMark; exact False.elim hMark
        | inl y =>
          rw [hi] at hMark
          exact hpE.2 (hprior hfalse i j' hij p hp y hi b₀ b₁ hb₀
            hMark.1 hMark.2.1 hMark.2.2.1 hMark.2.2.2.1 hMark.2.2.2.2)

end NumberTheoryLean.SourceBadCompactOccurrence

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_MarkedOccurrenceProbability
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicPaths.kernel_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.FlaggedHarmonicTransform.tiltedFlagged_sfinite _root_.OAI.Erdos970.NumberTheoryLean.OriginalHarmonicOccupation.occupation_isSFinite _root_.OAI.Erdos970.NumberTheoryLean.SubMarkovFlagPowers.marked_sfinite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.MarkedOccurrenceProbability

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open ActualCoupledHistories ActualSuccessfulHistories ActualProcessCoupling FlaggedSourceStart
open FiniteHistoryTransport PriorPrimeWindow CompactPrefixOccurrence CompletedMarkEvents
open SourceBadCompactOccurrence CanonicalBadCompact ContinuousKilledBins PersistentFailureFlag
open Erdos970Dependency.MarkedVisits

variable {w ell S R b₀ b₁ : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem missing_occurrence_probability_jb247_oai (hc : Consistent start)
    (hb₀ : 0 < b₀) (hb₁ : 0 < b₁) (hR : (11/10)*R < 6*b₀)
    {mesh : ℝ} (hm : 0 < mesh) (hmesh : mesh ≤ 1/100) (N : ℕ)
    (herror : 4*(N:ℝ)*mesh ≤ Real.log (11/10)) (E : Set (List ℕ))
    (hE : ∀ p : History w ell S start,p.primes ∈ E →
      p.node.gap ≤ R ∧ ¬hasPrimeWindow w b₀ b₁ start p.primes) :
    sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N {h | occurs E N h} ≤
      sourceLaw hw hell hS0 hS hr hs hsS mesh N failed +
      finitePathMeasure (typedState start.side start.ratio hs) N
        (closedNoHitEvent 1 N start.gap b₀ b₁ 1) := by
  let μ := sourceHistoryLaw hw hell hS0 hS hr hs hsS mesh N
  let F : Set (Hist (FlagState (JointState w ell S start)) N) := {h | (last N h).2 = true}
  let C : Set (Hist (FlagState (JointState w ell S start)) N) :=
    mapHist (fun q => q.1.2) N ⁻¹' badCompactPath (Real.log start.gap) ((11/10)*R) b₀ b₁ N
  have hF : μ F = sourceLaw hw hell hS0 hS hr hs hsS mesh N failed :=
    sourceHistory_failure_probability hw hell hS0 hS hr hs hsS mesh N
  have hC : μ C ≤ finitePathMeasure (typedState start.side start.ratio hs) N
      (closedNoHitEvent 1 N start.gap b₀ b₁ 1) := by
    dsimp [μ,C]
    rw [← Measure.map_apply
      (by exact mapHist_measurable (by exact measurable_snd.comp measurable_fst) N)
      (badCompactPath_measurable _ _ _ _ _),sourceHistoryLaw_continuous]
    exact completed_bad_compact_mass hr hb₀ hb₁ hR ell S (typedState start.side start.ratio hs) N
  calc
    _ ≤ μ (F ∪ C) := measure_mono_ae
      (missing_occurrence_inclusion hw hell hS0 hS hr hs hsS hc hb₀ hm hmesh N herror E hE)
    _ ≤ μ F + μ C := measure_union_le F C
    _ ≤ _ := by rw [hF]; exact add_le_add le_rfl hC

end NumberTheoryLean.MarkedOccurrenceProbability

end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.NumberTheoryLean.MarkedOccurrenceProbability.missing_occurrence_probability_jb247_oai := @OAI.Erdos970.NumberTheoryLean.MarkedOccurrenceProbability.missing_occurrence_probability_jb247_oai
