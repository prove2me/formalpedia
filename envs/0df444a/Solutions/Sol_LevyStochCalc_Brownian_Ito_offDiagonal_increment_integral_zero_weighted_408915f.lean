-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.offDiagonal_increment_integral_zero_weighted_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:22:01.210428+00:00
-- url     : https://prove2.me/submissions/4f058018-97a6-4ccc-b31a-98c17584a607

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ContinuityDyadicChaining
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Existence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityDyadicAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPointwise
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPredictableL2
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityShiftedAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityUnbounded
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionConvergence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionExistence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionLp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoMartingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIntegrand
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleMoments
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Martingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MartingaleCondExp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Multidim
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineAppend
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineCommon
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineInvariance
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
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

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionCompensator.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- `∫ (W_b − W_a) = 0` for `0 ≤ a < b`. -/
lemma LevyStochCalc.Brownian.Ito.brownian_incr_mean
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (W.W b ω - W.W a ω) ∂P = 0 := by
  have h_meas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  rw [show (∫ ω, (W.W b ω - W.W a ω) ∂P)
        = ∫ x : ℝ, x ∂(P.map (fun ω => W.W b ω - W.W a ω)) from
      (MeasureTheory.integral_map h_meas.aemeasurable
        (by fun_prop : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => x) _)).symm,
    W.increment_gaussian ha hab]
  exact ProbabilityTheory.integral_id_gaussianReal
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Ito in
/-- **Weighted off-diagonal vanishing.** For two increments with the second
strictly after the first (`a₁ < b₁ ≤ a₂ < b₂`), `Fᵢ`-measurable coefficients, and
a bounded `F_{a₁}`-measurable weight `g`,
`∫ g · (ξ₁·ΔW₁)·(ξ₂·ΔW₂) = 0`. The weighted analogue of
`offDiagonal_increment_integral_zero`: `f := g·ξ₁·ΔW₁·ξ₂` is `F_{a₂}`-measurable
and `ΔW₂ ⟂ F_{a₂}` is centred, so `𝔼[f·ΔW₂] = 𝔼[f]·0 = 0`. With `g = 1_B`
(`B ∈ F_s`, `s ≤ a₁`) this gives the off-diagonal of the set-level Itô isometry. -/
lemma solution
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (h₁ : a₁ < b₁) (h₁₂ : b₁ ≤ a₂) (h₂ : a₂ < b₂)
    (ξ₁ ξ₂ g : Ω → ℝ)
    (hadapt₁ : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₁) ξ₁)
    (hadapt₂ : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) ξ₂)
    (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₁) g) :
    ∫ ω, g ω * ((ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * (W.W b₂ ω - W.W a₂ ω))) ∂P
      = 0 := by
  set ΔW₂ : Ω → ℝ := fun ω => W.W b₂ ω - W.W a₂ ω with hΔW₂_def
  have ha₂_nn : 0 ≤ a₂ := le_trans ha₁ (le_trans (le_of_lt h₁) h₁₂)
  have ha₁a₂ : a₁ ≤ a₂ := le_trans (le_of_lt h₁) h₁₂
  have hξ₁meas : Measurable ξ₁ :=
    (hadapt₁.mono (ℱ.le a₁)).measurable
  have hξ₂meas : Measurable ξ₂ :=
    (hadapt₂.mono (ℱ.le a₂)).measurable
  have hgmeas : Measurable g :=
    (hg.mono (ℱ.le a₁)).measurable
  set f : Ω → ℝ := fun ω => g ω * (ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * ξ₂ ω with hf_def
  rw [show (fun ω => g ω * ((ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * ΔW₂ ω)))
        = fun ω => f ω * ΔW₂ ω from by funext ω; simp only [hf_def]; ring]
  have h_Wb₁_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) (W.W b₁) :=
    ((hℱ.measurable b₁).stronglyMeasurable).mono
      (ℱ.mono h₁₂)
  have h_Wa₁_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) (W.W a₁) :=
    ((hℱ.measurable a₁).stronglyMeasurable).mono
      (ℱ.mono
        (le_trans (le_of_lt h₁) h₁₂))
  have h_ξ₁_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) ξ₁ :=
    hadapt₁.mono (ℱ.mono ha₁a₂)
  have h_g_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) g :=
    hg.mono (ℱ.mono ha₁a₂)
  have h_f_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) f :=
    (h_g_F_meas.mul (h_ξ₁_F_meas.mul (h_Wb₁_meas.sub h_Wa₁_meas))).mul hadapt₂
  have h_indep_F_ΔW₂ := hℱ.indep ha₂_nn h₂
  have h_f_meas : Measurable f :=
    (hgmeas.mul (hξ₁meas.mul ((W.measurable_eval b₁).sub (W.measurable_eval a₁)))).mul hξ₂meas
  have h_ΔW₂_meas : Measurable ΔW₂ := (W.measurable_eval b₂).sub (W.measurable_eval a₂)
  have h_f_comap_le : MeasurableSpace.comap f inferInstance ≤ ℱ a₂ :=
    h_f_F_meas.measurable.comap_le
  have h_indep_f_ΔW₂ : ProbabilityTheory.IndepFun f ΔW₂ P := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    rw [ProbabilityTheory.Indep_iff] at h_indep_F_ΔW₂
    exact h_indep_F_ΔW₂ u v (h_f_comap_le u hu) hv
  have h_ΔW₂_mean : ∫ ω, ΔW₂ ω ∂P = 0 := LevyStochCalc.Brownian.Ito.brownian_incr_mean W ha₂_nn h₂
  rw [show (fun ω => f ω * ΔW₂ ω) = f * ΔW₂ from rfl,
    h_indep_f_ΔW₂.integral_mul_eq_mul_integral h_f_meas.aestronglyMeasurable
    h_ΔW₂_meas.aestronglyMeasurable, h_ΔW₂_mean, mul_zero]
