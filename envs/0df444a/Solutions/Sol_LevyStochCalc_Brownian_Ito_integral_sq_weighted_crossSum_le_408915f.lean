-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integral_sq_weighted_crossSum_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:30:52.33731+00:00
-- url     : https://prove2.me/submissions/2684c27b-52cd-4fc1-af9e-80ee45906667

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CrossVariation
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CrossVariationSum
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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIntegrand
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleMoments
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Martingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MartingaleCondExp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Multidim
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MultidimFiltered
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
import Mathlib.Data.Finset.Max
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.FiniteExhaustion
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.SesquilinearForm.Star
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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_condExp_mul_cross_increment_eq_zero_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integrable_sq_mul_and_le_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_sub_pow_four_le_408915f
import Theorems.Thm_LevyStochCalc_Probability_integral_sq_sum_of_condExp_eq_zero_408915f

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoIncrementMomentBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
section ThirdMoment
variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
include hℱ in
/-- The increment of the `L²` Itô integral is measurable. -/
theorem LevyStochCalc.Brownian.Ito.measurable_sub_stochasticIntegralBrownian (a b : ℝ) :
    Measurable fun ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω :=
  (((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq b).mono
      (ℱ.le b)).measurable).sub
    (((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq a).mono
      (ℱ.le a)).measurable)
end ThirdMoment
end
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossVariationSum.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
section CrossSum
open LevyStochCalc.Brownian.Multidim
variable {d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  {H K : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
  (hHp : Probability.ProgressivelyMeasurable ℱ H)
  (hHs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hKm : Measurable (Function.uncurry K))
  (hKp : Probability.ProgressivelyMeasurable ℱ K)
  (hKs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
/-- The cross increment is measurable. -/
theorem LevyStochCalc.Brownian.Ito.measurable_crossIncrement (i j : Fin d) (a b : ℝ) :
    Measurable (crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b) :=
  (measurable_sub_stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs a b).mul
    (measurable_sub_stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs a b)
/-- The cross increment across `(a, b]` is measurable for the σ-algebra at `b`. -/
theorem LevyStochCalc.Brownian.Ito.stronglyMeasurable_crossIncrement (i j : Fin d) {a b : ℝ} (hab : a ≤ b) :
    StronglyMeasurable[ℱ b] (crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b) := by
  have hib := stochasticIntegralBrownian_stronglyAdapted (W.W i) ℱ (hcoord i) H hHm hHp hHs b
  have hia := (stochasticIntegralBrownian_stronglyAdapted (W.W i) ℱ (hcoord i) H hHm hHp hHs
    a).mono (ℱ.mono hab)
  have hjb := stochasticIntegralBrownian_stronglyAdapted (W.W j) ℱ (hcoord j) K hKm hKp hKs b
  have hja := (stochasticIntegralBrownian_stronglyAdapted (W.W j) ℱ (hcoord j) K hKm hKp hKs
    a).mono (ℱ.mono hab)
  exact (hib.sub hia).mul (hjb.sub hja)
variable {CH CK : ℝ} (hCH0 : 0 ≤ CH) (hCH : ∀ ω s, |H ω s| ≤ CH)
  (hCK0 : 0 ≤ CK) (hCK : ∀ ω s, |K ω s| ≤ CK)
include hCH0 hCH hCK0 hCK in
/-- **Second moment of a cross increment.** Both increments have fourth moments bounded through
the integrand bounds, and the square of a product is dominated by half the sum of the fourth
powers. -/
theorem LevyStochCalc.Brownian.Ito.integrable_sq_crossIncrement_and_le (i j : Fin d) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Integrable (fun ω =>
        (crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b ω) ^ 2) P
      ∧ ∫ ω, (crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b ω) ^ 2 ∂P
        ≤ (6 + gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2 * (b - a) ^ 2 := by
  obtain ⟨hA4, hA4le⟩ :=
    integral_sub_pow_four_le_408915f (W.W i) ℱ (hcoord i) H hHm hHp hHs hCH0 hCH ha hab
  obtain ⟨hB4, hB4le⟩ :=
    integral_sub_pow_four_le_408915f (W.W j) ℱ (hcoord j) K hKm hKp hKs hCK0 hCK ha hab
  obtain ⟨hint, hle⟩ := integrable_sq_mul_and_le_408915f
    (measurable_sub_stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs a b)
    (measurable_sub_stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs a b) hA4 hB4
  refine ⟨hint, le_trans hle ?_⟩
  linarith [hA4le, hB4le]
include hCH0 hCH hCK0 hCK in
/-- The cross increment lies in `L²`. -/
theorem LevyStochCalc.Brownian.Ito.memLp_two_crossIncrement (i j : Fin d) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MemLp (crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b) 2 P :=
  (memLp_two_iff_integrable_sq
      (measurable_crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b).aestronglyMeasurable).2
    (integrable_sq_crossIncrement_and_le W hcoord hHm hHp hHs hKm hKp hKs hCH0 hCH hCK0 hCK
      i j ha hab).1
/-- The cross increment is conditionally centred at the left endpoint of its cell. -/
theorem LevyStochCalc.Brownian.Ito.condExp_crossIncrement {i j : Fin d} (hij : i ≠ j) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    P[crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b | ℱ a] =ᵐ[P] 0 :=
  condExp_mul_cross_increment_eq_zero_408915f W hcoord hHm hHp hHs hKm hKp hKs hij ha hab
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Ito in
include hCH0 hCH hCK0 hCK in
/-- **Second moment of a weighted sum of cross increments.** The cross increments are martingale
differences for the weights at the left endpoints, so the weighted sum's second moment is
controlled by the sum of the squared cell lengths. -/
theorem solution {i j : Fin d} (hij : i ≠ j)
    (t : ℕ → ℝ) (h0 : 0 ≤ t 0) (ht : ∀ k, t k < t (k + 1))
    (g : ℕ → Ω → ℝ) (hg : ∀ k, StronglyMeasurable[ℱ (t k)] (g k))
    {D : ℝ} (hD0 : 0 ≤ D) (hgD : ∀ (k : ℕ) (ω : Ω), |g k ω| ≤ D) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n, g k ω *
        LevyStochCalc.Brownian.Ito.crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1)) ω) ^ 2 ∂P
      ≤ D ^ 2 * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2)
        * ∑ k ∈ Finset.range n, (t (k + 1) - t k) ^ 2 := by
  have htmono : StrictMono t := strictMono_nat_of_lt_succ ht
  have ht0 : ∀ k, 0 ≤ t k := fun k => h0.trans (htmono.monotone (Nat.zero_le k))
  set 𝒢 : ℕ → MeasurableSpace Ω := fun k => ℱ (t k) with h𝒢
  have h𝒢le : ∀ k, 𝒢 k ≤ ‹MeasurableSpace Ω› := fun k => ℱ.le (t k)
  have h𝒢mono : Monotone 𝒢 := fun p q hpq => ℱ.mono (htmono.monotone hpq)
  set Y : ℕ → Ω → ℝ := fun k ω =>
    g k ω * LevyStochCalc.Brownian.Ito.crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1)) ω with hY
  have hζmem : ∀ k, MemLp
      (LevyStochCalc.Brownian.Ito.crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1))) 2 P :=
    fun k => LevyStochCalc.Brownian.Ito.memLp_two_crossIncrement W hcoord hHm hHp hHs hKm hKp hKs hCH0 hCH hCK0 hCK
      i j (ht0 k) (ht k)
  have hgmeas : ∀ k, Measurable (g k) := fun k => ((hg k).mono (h𝒢le k)).measurable
  have hYmem : ∀ k, MemLp (Y k) 2 P := by
    intro k
    refine MeasureTheory.MemLp.mono ((hζmem k).const_mul D)
      ((hgmeas k).aestronglyMeasurable.mul (hζmem k).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hD0]
    exact mul_le_mul_of_nonneg_right (hgD k ω) (abs_nonneg _)
  have hYmeas : ∀ k, @MeasureTheory.StronglyMeasurable Ω ℝ _ (𝒢 (k + 1)) (Y k) := fun k =>
    ((hg k).mono (h𝒢mono (Nat.le_succ k))).mul
      (LevyStochCalc.Brownian.Ito.stronglyMeasurable_crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (ht k).le)
  have hYcond : ∀ k, P[Y k | 𝒢 k] =ᵐ[P] 0 := by
    intro k
    have hprod : Integrable
        (g k * LevyStochCalc.Brownian.Ito.crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1))) P :=
      (hYmem k).integrable (by norm_num)
    have hkey := MeasureTheory.condExp_mul_of_stronglyMeasurable_left (m := 𝒢 k) (hg k)
      hprod ((hζmem k).integrable (by norm_num))
    have hfun : Y k
        = g k * LevyStochCalc.Brownian.Ito.crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1)) := rfl
    rw [hfun]
    filter_upwards [hkey, LevyStochCalc.Brownian.Ito.condExp_crossIncrement W hcoord hHm hHp hHs hKm hKp hKs hij
      (ht0 k) (ht k)] with ω hω hω'
    rw [hω, Pi.mul_apply, hω', Pi.zero_apply, mul_zero]
  rw [LevyStochCalc.Probability.integral_sq_sum_of_condExp_eq_zero_408915f 𝒢 h𝒢le h𝒢mono Y hYmem
    hYmeas hYcond n]
  have hterm : ∀ k ∈ Finset.range n, ∫ ω, (Y k ω) ^ 2 ∂P
      ≤ D ^ 2 * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2) * (t (k + 1) - t k) ^ 2 := by
    intro k _
    obtain ⟨hζint, hζle⟩ := LevyStochCalc.Brownian.Ito.integrable_sq_crossIncrement_and_le W hcoord hHm hHp hHs hKm hKp hKs
      hCH0 hCH hCK0 hCK i j (ht0 k) (ht k)
    have hYint : Integrable (fun ω => (Y k ω) ^ 2) P := by
      have hfun : (fun ω => (Y k ω) ^ 2) = Y k * Y k := by funext ω; rw [pow_two]; rfl
      rw [hfun]
      exact (hYmem k).integrable_mul (hYmem k)
    have hstep : ∫ ω, (Y k ω) ^ 2 ∂P ≤ D ^ 2 * ∫ ω,
        (LevyStochCalc.Brownian.Ito.crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1)) ω) ^ 2 ∂P := by
      have hle : ∫ ω, (Y k ω) ^ 2 ∂P ≤ ∫ ω, D ^ 2 *
          (LevyStochCalc.Brownian.Ito.crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1)) ω) ^ 2 ∂P := by
        refine MeasureTheory.integral_mono hYint (hζint.const_mul _) fun ω => ?_
        have hgi : (g k ω) ^ 2 ≤ D ^ 2 := by
          have h := pow_le_pow_left₀ (abs_nonneg (g k ω)) (hgD k ω) 2
          rwa [← abs_pow, abs_of_nonneg (sq_nonneg (g k ω))] at h
        have hsq : (Y k ω) ^ 2 = (g k ω) ^ 2
            * (LevyStochCalc.Brownian.Ito.crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1)) ω) ^ 2 := by
          simp only [hY]; ring
        rw [hsq]
        exact mul_le_mul_of_nonneg_right hgi (sq_nonneg _)
      rwa [MeasureTheory.integral_const_mul] at hle
    have hD2 : (0 : ℝ) ≤ D ^ 2 := sq_nonneg D
    calc ∫ ω, (Y k ω) ^ 2 ∂P
        ≤ D ^ 2 * ∫ ω,
            (LevyStochCalc.Brownian.Ito.crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1)) ω) ^ 2 ∂P :=
          hstep
      _ ≤ D ^ 2 * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2 * (t (k + 1) - t k) ^ 2) :=
          mul_le_mul_of_nonneg_left hζle hD2
      _ = D ^ 2 * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2)
            * (t (k + 1) - t k) ^ 2 := by ring
  calc ∑ k ∈ Finset.range n, ∫ ω, (Y k ω) ^ 2 ∂P
      ≤ ∑ k ∈ Finset.range n,
          D ^ 2 * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2)
            * (t (k + 1) - t k) ^ 2 := Finset.sum_le_sum hterm
    _ = D ^ 2 * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2)
          * ∑ k ∈ Finset.range n, (t (k + 1) - t k) ^ 2 := by rw [Finset.mul_sum]
