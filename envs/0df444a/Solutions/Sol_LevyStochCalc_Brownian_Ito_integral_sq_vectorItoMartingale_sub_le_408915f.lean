-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integral_sq_vectorItoMartingale_sub_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:25:10.912097+00:00
-- url     : https://prove2.me/submissions/13b8f2c1-4b97-4614-b156-b32ee946663d

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_VectorItoProcess
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Progressive
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Transport
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_TrivialSigma
import Mathlib.Algebra.Order.Chebyshev
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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integrable_sq_sum_and_le_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_sub_sq_le_408915f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcess.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
section VectorProcess
open LevyStochCalc.Brownian.Multidim
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
/-- Each entry's Itô integral is measurable for the σ-algebra at its time. -/
theorem LevyStochCalc.Brownian.Ito.stronglyMeasurable_coordItoIntegral (m : Fin n) (k : Fin d) (t : ℝ) :
    StronglyMeasurable[ℱ t] (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t) :=
  stochasticIntegralBrownian_stronglyAdapted (W.W k) ℱ (hcoord k) (H m k) (hHm m k) (hHp m k)
    (hHs m k) t
/-- Each entry's Itô integral is measurable. -/
theorem LevyStochCalc.Brownian.Ito.measurable_coordItoIntegral (m : Fin n) (k : Fin d) (t : ℝ) :
    Measurable (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t) :=
  ((stronglyMeasurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t).mono (ℱ.le t)).measurable
/-- The increment of the martingale part is the sum of the entries' increments. -/
theorem LevyStochCalc.Brownian.Ito.vectorItoMartingale_sub (m : Fin n) (u v : ℝ) (ω : Ω) :
    vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
        - vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω
      = ∑ k : Fin d, (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
        - coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω) := by
  simp only [vectorItoMartingale, Finset.sum_sub_distrib]
variable {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Ito in
include hC0 hCH in
/-- **Second moment of the martingale part's increment.** -/
theorem solution (m : Fin n) {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    Integrable (fun ω => (LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
        - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω) ^ 2) P
      ∧ ∫ ω, (LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
          - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω) ^ 2 ∂P
        ≤ (d : ℝ) ^ 2 * (C ^ 2 * (v - u)) := by
  have hk : ∀ k : Fin d,
      Integrable (fun ω => (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
          - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω) ^ 2) P
        ∧ ∫ ω, (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
            - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω) ^ 2 ∂P ≤ C ^ 2 * (v - u) :=
    fun k => LevyStochCalc.Brownian.Ito.integral_sub_sq_le_408915f (W.W k) ℱ (hcoord k) (H m k) (hHm m k) (hHp m k) (hHs m k)
      hC0 (hCH m k) hu huv
  obtain ⟨hint, hle⟩ := LevyStochCalc.Brownian.Ito.integrable_sq_sum_and_le_408915f (P := P)
    (f := fun (k : Fin d) ω => LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
      - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω)
    (fun k => (LevyStochCalc.Brownian.Ito.measurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v).sub
      (LevyStochCalc.Brownian.Ito.measurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u))
    (fun k => (hk k).1)
  simp_rw [LevyStochCalc.Brownian.Ito.vectorItoMartingale_sub W ℱ hcoord H hHm hHp hHs m u v]
  refine ⟨hint, ?_⟩
  have hsum : ∑ k : Fin d, ∫ ω, (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
        - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω) ^ 2 ∂P
      ≤ (d : ℝ) * (C ^ 2 * (v - u)) := by
    calc ∑ k : Fin d, ∫ ω, (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
          - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω) ^ 2 ∂P
        ≤ ∑ _k : Fin d, C ^ 2 * (v - u) := Finset.sum_le_sum fun k _ => (hk k).2
      _ = (d : ℝ) * (C ^ 2 * (v - u)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcard : (Fintype.card (Fin d) : ℝ) = (d : ℝ) := by simp
  calc ∫ ω, (∑ k : Fin d, (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
        - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω)) ^ 2 ∂P
      ≤ (Fintype.card (Fin d) : ℝ) * ∑ k : Fin d,
          ∫ ω, (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
            - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω) ^ 2 ∂P := hle
    _ = (d : ℝ) * ∑ k : Fin d, ∫ ω, (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
          - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω) ^ 2 ∂P := by rw [hcard]
    _ ≤ (d : ℝ) * ((d : ℝ) * (C ^ 2 * (v - u))) :=
        mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg d)
    _ = (d : ℝ) ^ 2 * (C ^ 2 * (v - u)) := by ring
