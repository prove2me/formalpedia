-- Prove2me | solution 1 for OAI.Erdos970.NumberTheoryLean.MovingPrimeWindowProbability.source_missing_window_probability_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:07:41.858196+00:00
-- url     : https://prove2.me/submissions/0196c14f-be40-43fb-9344-91d3e0d77da5

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
import Definitions.Def_OAIQ247J010
import Theorems.Thm_OAI_Erdos970_Erdos970Dependency_MarkedVisits_moving_canonical_missing_visit_jb247
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_MarkedOccurrenceProbability_missing_occurrence_probability_jb247
import Theorems.Thm_OAI_Erdos970_NumberTheoryLean_SourceCouplingRate_source_coupling_rate_jb247

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
open ArrivalKernelGeometry RegeneratingInverseBands HarmonicWeightKernel

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
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SourceCompactCoupling
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.MarkedSourceSmallness

open _root_.Filter
open scoped Topology
open ExponentialMesh

theorem mark_mesh_smallness {A κ : ℝ} (hA : 0 ≤ A) (hκ : 0 < κ) :
    ∀ᶠ w : ℝ in atTop, mesh κ w ≤ 1/100 ∧ ∀ N : ℕ,
      (N:ℝ) ≤ A*(Real.log w)^3 → 4*(N:ℝ)*mesh κ w ≤ Real.log (11/10) := by
  have hlog : 0 < Real.log (11/10:ℝ) := Real.log_pos (by norm_num)
  filter_upwards [
    (log_power_exp_tendsto 1 0 hκ).eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1/100)),
    (log_power_exp_tendsto (4*A) 3 hκ).eventually (eventually_le_nhds hlog),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0:ℝ))] with w hm hN hL
  refine ⟨(mesh_upper κ w).trans (by simpa using hm),?_⟩
  intro N hbound
  calc
    _ ≤ (4*(A*(Real.log w)^3))*Real.exp (-κ*Real.sqrt (Real.log w)) :=
      mul_le_mul (by nlinarith) (mesh_upper κ w) (mesh_pos κ w).le (by positivity)
    _ = (4*A)*(Real.log w)^3*Real.exp (-κ*Real.sqrt (Real.log w)) := by ring
    _ ≤ _ := hN

theorem moving_compact_gap_small (R : ℝ) {K : ℝ} (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop, R < 6*(K*(Real.log w)^2) := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max (1:ℝ) (1+R/(6*K))))] with w hw
  have hL : 1 ≤ Real.log w := (le_max_left _ _).trans hw
  have hR : 1+R/(6*K) ≤ Real.log w := (le_max_right _ _).trans hw
  have hm := mul_le_mul_of_nonneg_left hR (show 0 ≤ 6*K by positivity)
  have he : 6*K*(1+R/(6*K)) = 6*K+R := by field_simp [hK.ne']
  rw [he] at hm
  have hSq : Real.log w ≤ (Real.log w)^2 := by nlinarith
  have hs := mul_le_mul_of_nonneg_left hSq (show 0 ≤ 6*K by positivity)
  nlinarith

end NumberTheoryLean.MarkedSourceSmallness

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PaperMissingPrimeWindow
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.MovingPrimeWindowProbability

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open ActualCoupledHistories FlaggedSourceStart FiniteHistoryTransport PriorPrimeWindow
open CompactPrefixOccurrence MarkedOccurrenceProbability MarkedSourceSmallness ExponentialMesh
open SourceSelectedCompactOccupation SourceCouplingRate
open Erdos970Dependency.MarkedVisits

theorem source_missing_window_probability_jb247_oai : ∃ κ₀ : ℝ, 0 < κ₀ ∧
    ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ R d eps : ℝ, 0 < d → 0 < eps →
      ∃ rho : ℝ, 10 < rho ∧ ∀ K : ℝ, 0 < K → ∃ w₀ : ℝ, 1 < w₀ ∧
      ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ, ∀ start : Node, ∀ hs : Valid start.side start.ratio,
      1 ≤ ell → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
      start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      Consistent start → start.cutoff = B → w ≤ start.gap →
      let S := (Real.log B)^2
      let N := LowStateHorizon.sourceHorizon S B
      ∀ E : Set (List ℕ),
        (∀ p : History w ell S start,p.primes ∈ E → p.node.gap ≤ R ∧
          ¬hasPrimeWindow w (K*(Real.log w)^2) (rho*K*(Real.log w)^2) start p.primes) →
        fullSourceLaw w ell S start hs (mesh κ w) N {h | occurs E N h} ≤ ENNReal.ofReal eps := by
  obtain ⟨κ₀,hκ₀,hCouple⟩ := source_coupling_rate_jb247
  refine ⟨κ₀,hκ₀,?_⟩
  intro κ hκ hκle R d eps hd heps
  obtain ⟨WC,hWC,hC⟩ := hCouple κ hκ hκle d hd
  obtain ⟨rho,hrho,hMoving⟩ := moving_canonical_missing_visit_jb247 (show 0 < eps/2 by positivity)
  refine ⟨rho,hrho,?_⟩
  intro K hK
  have hA : 0 ≤ 5*d^3 := by positivity
  have hEvents := (hMoving K hK).and ((mark_mesh_smallness hA hκ).and
    ((moving_compact_gap_small ((11/10)*R) hK).and
      (((log_power_exp_tendsto 1 0 (show 0 < κ/2 by positivity)).eventually
        (eventually_le_nhds (show 0 < eps/2 by positivity))).and
          (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (d^2))))))
  obtain ⟨W,hW⟩ := eventually_atTop.mp hEvents
  refine ⟨max WC (max normalizationThreshold W),hWC.trans_le (le_max_left _ _),?_⟩
  intro w hw ell B start hs hell hB hlogB hcomp hi h199 h23 hc hcut hgap
  dsimp only
  intro E hE
  have hwC : WC ≤ w := (le_max_left _ _).trans hw
  have hnorm : normalizationThreshold ≤ w :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw
  have hwe := hW w ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hw)
  have hw3 : 3 ≤ w := hwe.1.1
  have hr : 0 < start.gap := (by linarith : 0 < w).trans_le hgap
  have hscale := UniformBudgetRate.source_scale_bound hwe.2.2.2.2 hlogB hcomp
  have hS0 : 0 ≤ (Real.log B)^2 := sq_nonneg _
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  have he : start.gap = B*start.ratio := by
    have hh : start.cutoff = start.gap/start.ratio := hc
    rw [hcut] at hh
    exact ((eq_div_iff (valid_pos hs).ne').mp hh).symm
  have hsize : start.gap ≤ (23/10:ℝ)*B := by rw [he]; nlinarith
  have hf := (hC w hwC ell B start hs hell hB hlogB hcomp hr h23 hc hsize).1
    (LowStateHorizon.sourceHorizon ((Real.log B)^2) B) le_rfl |>.1
  have hfailSmall : Real.exp (-(κ/2)*Real.sqrt (Real.log w)) ≤ eps/2 := by
    simpa only [pow_zero,mul_one,one_mul] using hwe.2.2.2.1
  have hf' : sourceLaw hnorm hell hS0 hscale.1 hr hs hsS (mesh κ w)
      (LowStateHorizon.sourceHorizon ((Real.log B)^2) B) PersistentFailureFlag.failed ≤ ENNReal.ofReal (eps/2) :=
    hf.trans (ENNReal.ofReal_le_ofReal hfailSmall)
  let s : TransitionKernels.EvenState := ⟨start.ratio,by simpa only [hi,Valid] using hs⟩
  have htyped : typedState start.side start.ratio hs = Sum.inl s := by
    have aux : ∀ (i : Side) (t : ℝ) (ht : Valid i t) (hi : i = .even),
        typedState i t ht = Sum.inl (⟨t,by simpa only [hi,Valid] using ht⟩ : TransitionKernels.EvenState) := by
      intro i t ht hi
      subst i
      rfl
    exact aux start.side start.ratio hs hi
  have hcanon := hwe.1.2 start.gap hgap s h199 h23
    (LowStateHorizon.sourceHorizon ((Real.log B)^2) B)
  have hb₀ : 0 < K*(Real.log w)^2 := by
    have hL : 0 < Real.log w := Real.log_pos (by linarith)
    positivity
  have hb₁ : 0 < rho*K*(Real.log w)^2 := by
    have : 0 < rho := by linarith
    have hL : 0 < Real.log w := Real.log_pos (by linarith)
    positivity
  have hProb := missing_occurrence_probability_jb247 hnorm hell hS0 hscale.1 hr hs hsS hc
    hb₀ hb₁ hwe.2.2.1 (mesh_pos κ w) hwe.2.1.1 _ (hwe.2.1.2 _ hscale.2) E hE
  rw [htyped] at hProb
  calc
    _ ≤ _ := hProb
    _ ≤ ENNReal.ofReal (eps/2)+ENNReal.ofReal (eps/2) := add_le_add hf' hcanon
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity : 0 ≤ eps/2) (by positivity : 0 ≤ eps/2)]; congr 1; ring

end NumberTheoryLean.MovingPrimeWindowProbability

end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.NumberTheoryLean.MovingPrimeWindowProbability.source_missing_window_probability_jb247_oai := @OAI.Erdos970.NumberTheoryLean.MovingPrimeWindowProbability.source_missing_window_probability_jb247_oai
