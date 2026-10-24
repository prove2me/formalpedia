-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.exists_continuousAdapted_modification_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:45:12.742756+00:00
-- url     : https://prove2.me/submissions/2b495250-fd08-4b99-8f50-2116c032de36

import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Algebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_DenseCountable
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_ENNReal
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_FiniteInf
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_LinearAlgebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeanInequalities
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeasureTheory
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Metric
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Nat
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Topology
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_Chaining
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_CoveringNumber
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_HasBoundedInternalCoveringNumber
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_IsKolmogorovProcess
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_KolmogorovChentsov
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_KolmogorovChentsovInequality
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_LimitModification
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_BrownianMotion
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_Moment
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_ProjectiveLimit
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_StochasticProcesses
import Definitions.Def_KLS408915f_KolmogorovExtension4_CompactSystem
import Definitions.Def_KLS408915f_KolmogorovExtension4_KolmogorovExtension
import Definitions.Def_KLS408915f_KolmogorovExtension4_RegularContent
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_AugmentedFiltration
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ContinuityDyadicChaining
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Existence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoAlgebraAssociativity
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoAlgebraProduct
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityDyadicAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPointwise
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPredictableL2
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityShiftedAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityUnbounded
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoFourthMomentIncrements
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoFourthMomentLintegral
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoIncrementMomentRestrict
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionApi
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionConvergence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionExistence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionLp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionQuadVar
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoMartingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoQuadVarSum
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIntegrand
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleMoments
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoVersionExists
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Martingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MartingaleCondExp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Multidim
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineAppend
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineCommon
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineInvariance
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Augmentation
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Progressive
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Transport
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_TrivialSigma
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.FiniteExhaustion
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.SesquilinearForm.Star
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Order.CompleteLattice.Group
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.CompactSystem
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.EMetricSpace.PairReduction
import Mathlib.Topology.IsClosedRestrict
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Topology.MetricSpace.MetricSeparated
import Mathlib.Topology.Order.MonotoneContinuity
import Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_continuous_modification_stochasticIntegralBrownian_408915f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoVersionExists.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Brownian
end LevyStochCalc.Brownian
open LevyStochCalc LevyStochCalc.Brownian
section
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- A measurable null set outside which an almost-everywhere property holds. -/
theorem LevyStochCalc.Brownian.Ito.exists_measurable_null_of_ae {μ : Measure Ω} {p : Ω → Prop} (h : ∀ᵐ ω ∂μ, p ω) :
    ∃ N : Set Ω, MeasurableSet N ∧ μ N = 0 ∧ ∀ ω, ω ∉ N → p ω := by
  obtain ⟨N, hsub, hmeas, hzero⟩ :=
    MeasureTheory.exists_measurable_superset_of_null (MeasureTheory.ae_iff.mp h)
  exact ⟨N, hmeas, hzero, fun ω hω => by_contra fun hp => hω (hsub hp)⟩
theorem LevyStochCalc.Brownian.Ito.dyadicApprox_le {u : ℝ} (hu : 0 ≤ u) (n : ℕ) : dyadicApprox n u ≤ u := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [dyadicApprox, div_le_iff₀ h2]
  exact Nat.floor_le (by positivity)
theorem LevyStochCalc.Brownian.Ito.sub_dyadicApprox_lt (u : ℝ) (n : ℕ) : u - dyadicApprox n u < 1 / 2 ^ n := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hfl := Nat.lt_floor_add_one (u * 2 ^ n)
  rw [dyadicApprox, sub_lt_iff_lt_add,
    show (1 : ℝ) / 2 ^ n + (⌊u * 2 ^ n⌋₊ : ℝ) / 2 ^ n
      = ((⌊u * 2 ^ n⌋₊ : ℝ) + 1) / 2 ^ n by ring, lt_div_iff₀ h2]
  linarith
theorem LevyStochCalc.Brownian.Ito.tendsto_dyadicApprox {u : ℝ} (hu : 0 ≤ u) :
    Filter.Tendsto (fun n : ℕ => dyadicApprox n u) Filter.atTop (nhds u) := by
  have hlo : ∀ n : ℕ, u - 1 / 2 ^ n ≤ dyadicApprox n u := fun n => by
    have := sub_dyadicApprox_lt u n
    linarith
  have hhi : ∀ n : ℕ, dyadicApprox n u ≤ u := dyadicApprox_le hu
  have hpow : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) Filter.atTop (nhds 0) := by
    simpa using tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)
  have hsub : Filter.Tendsto (fun n : ℕ => u - 1 / 2 ^ n) Filter.atTop (nhds u) := by
    simpa using (tendsto_const_nhds (x := u) (f := Filter.atTop (α := ℕ))).sub hpow
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hsub tendsto_const_nhds hlo hhi
section Exists
variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Ito in
include hℱ hC0 hCH in
/-- **A continuous adapted modification of the Itô integral exists** when the filtration is
constant before time `0` and contains the measurable null sets. -/
theorem solution
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) :
    ∃ Y : ℝ → Ω → ℝ, (∀ ω : Ω, Continuous fun t => Y t ω)
      ∧ (∀ u : ℝ, Measurable[ℱ u] (Y u))
      ∧ ∀ t : ℝ, 0 ≤ t → Y t =ᵐ[P] LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t := by
  classical
  obtain ⟨Y, hYcont, hYmod⟩ :=
    LevyStochCalc.Brownian.Ito.exists_continuous_modification_stochasticIntegralBrownian_408915f W ℱ hℱ H hm hp hq hC0 hCH
  obtain ⟨N₁, hN₁meas, hN₁zero, hN₁cont⟩ := LevyStochCalc.Brownian.Ito.exists_measurable_null_of_ae hYcont
  -- the modification agrees with the integral at every nonnegative dyadic time
  have hdnn : ∀ p : ℕ × ℕ, (0 : ℝ) ≤ ((p.1 : ℝ) / 2 ^ p.2) := fun p => by positivity
  choose Nd hNdmeas hNdzero hNdout using fun p : ℕ × ℕ =>
    LevyStochCalc.Brownian.Ito.exists_measurable_null_of_ae (hYmod ((p.1 : ℝ) / 2 ^ p.2) (hdnn p))
  set N : Set Ω := N₁ ∪ ⋃ p : ℕ × ℕ, Nd p with hNdef
  have hNmeas : MeasurableSet N :=
    hN₁meas.union (MeasurableSet.iUnion fun p => hNdmeas p)
  have hNzero : P N = 0 :=
    MeasureTheory.measure_union_null hN₁zero
      (MeasureTheory.measure_iUnion_null fun p => hNdzero p)
  have hNcont : ∀ ω : Ω, ω ∉ N → Continuous fun t => Y t ω := fun ω hω =>
    hN₁cont ω fun h => hω (Or.inl h)
  have hNdyad : ∀ (p : ℕ × ℕ) (ω : Ω), ω ∉ N →
      Y ((p.1 : ℝ) / 2 ^ p.2) ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq ((p.1 : ℝ) / 2 ^ p.2) ω :=
    fun p ω hω => hNdout p ω fun h => hω (Or.inr (Set.mem_iUnion.mpr ⟨p, h⟩))
  -- `ℱ t` contains `ℱ 0` at every time, hence contains `N`
  have hle0 : ∀ t : ℝ, ℱ 0 ≤ ℱ t := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · exact ℱ.mono ht
    · exact hℱ0 t ht.le
  have hNm : ∀ t : ℝ, MeasurableSet[ℱ t] N := fun t =>
    hle0 t N (hnull N hNmeas hNzero)
  -- the truncated modification is adapted, as a pointwise limit along dyadic times
  have hYind : ∀ u : ℝ, 0 ≤ u →
      Measurable[ℱ u] fun ω => if ω ∈ N then (0 : ℝ) else Y u ω := by
    intro u hu
    have hstep : ∀ n : ℕ, Measurable[ℱ u] fun ω => if ω ∈ N then (0 : ℝ)
        else LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.dyadicApprox n u) ω := by
      intro n
      have hSI : Measurable[ℱ u]
          (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.dyadicApprox n u)) := by
        have h1 := (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq
          (LevyStochCalc.Brownian.Ito.dyadicApprox n u)).measurable
        exact fun A hA => ℱ.mono (LevyStochCalc.Brownian.Ito.dyadicApprox_le hu n) _ (h1 hA)
      exact Measurable.ite (hNm u) measurable_const hSI
    have hlim : Filter.Tendsto (fun (n : ℕ) (ω : Ω) => if ω ∈ N then (0 : ℝ)
          else LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.dyadicApprox n u) ω)
        Filter.atTop (nhds fun ω => if ω ∈ N then (0 : ℝ) else Y u ω) := by
      rw [tendsto_pi_nhds]
      intro ω
      by_cases hω : ω ∈ N
      · simp only [hω, if_true]
        exact tendsto_const_nhds
      · simp only [hω, if_false]
        have heq : (fun n : ℕ => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq
            (LevyStochCalc.Brownian.Ito.dyadicApprox n u) ω) = fun n => Y (LevyStochCalc.Brownian.Ito.dyadicApprox n u) ω := by
          funext n
          exact (hNdyad (⌊u * 2 ^ n⌋₊, n) ω hω).symm
        rw [heq]
        exact Filter.Tendsto.comp ((hNcont ω hω).continuousAt (x := u))
          (LevyStochCalc.Brownian.Ito.tendsto_dyadicApprox hu)
    letI : MeasurableSpace Ω := ℱ u
    exact measurable_of_tendsto_metrizable hstep hlim
  refine ⟨fun t ω => if ω ∈ N then 0 else Y (max t 0) ω, ?_, ?_, ?_⟩
  · intro ω
    by_cases hω : ω ∈ N
    · simpa [hω] using continuous_const
    · simp only [hω, if_false]
      exact (hNcont ω hω).comp (continuous_id.max continuous_const)
  · intro u
    rcases le_or_gt 0 u with hu | hu
    · simp only [max_eq_left hu]
      exact hYind u hu
    · simp only [max_eq_right hu.le]
      exact fun A hA => hle0 u _ (hYind 0 le_rfl hA)
  · intro t ht
    filter_upwards [hYmod t ht,
      MeasureTheory.compl_mem_ae_iff.mpr hNzero] with ω hω hωN
    rw [if_neg hωN, max_eq_left ht]
    exact hω
