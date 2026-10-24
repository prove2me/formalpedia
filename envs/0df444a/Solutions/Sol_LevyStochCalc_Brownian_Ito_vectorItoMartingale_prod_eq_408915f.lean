-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.vectorItoMartingale_prod_eq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:23:26.949305+00:00
-- url     : https://prove2.me/submissions/b7215e50-d475-4a05-a8e4-817a9c6b6621

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoFormulaGrid
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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Martingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MartingaleCondExp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Multidim
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MultidimFiltered
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_PolarisedQuadVar
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineAppend
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineCommon
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineInvariance
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_VectorItoProcess
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_VectorItoProcessVersion
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Augmentation
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
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

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/DriftIncrement.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
open MeasureTheory
/-- A bounded measurable function is integrable on any set of finite measure. -/
theorem LevyStochCalc.integrableOn_of_bounded_of_measurable {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ s, |f s| ≤ B) {s : Set ℝ} (hs : volume s ≠ ⊤) :
    MeasureTheory.IntegrableOn f s volume := by
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := B) hs hf.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hB u
/-- The increment of `t ↦ ∫_{[0,t]} f` across `(a, b]` is the integral over `(a, b]`. -/
theorem LevyStochCalc.setIntegral_Icc_sub_Icc {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ s, |f s| ≤ B) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ s in Set.Icc (0 : ℝ) b, f s ∂volume) - ∫ s in Set.Icc (0 : ℝ) a, f s ∂volume
      = ∫ s in Set.Ioc a b, f s ∂volume := by
  have hsplit : Set.Icc (0 : ℝ) b = Set.Icc (0 : ℝ) a ∪ Set.Ioc a b := by
    rw [Set.Icc_union_Ioc_eq_Icc ha hab]
  have hdisj : Disjoint (Set.Icc (0 : ℝ) a) (Set.Ioc a b) :=
    Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le.mpr hx'.1)
  have hint1 : MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) a) volume :=
    integrableOn_of_bounded_of_measurable hf hB (by simp)
  have hint2 : MeasureTheory.IntegrableOn f (Set.Ioc a b) volume :=
    integrableOn_of_bounded_of_measurable hf hB (by simp)
  rw [hsplit, MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hint1 hint2,
    add_sub_cancel_left]
end
end

section
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
/-- The increment of the martingale part is the sum of the entries' increments. -/
theorem LevyStochCalc.Brownian.Ito.vectorItoMartingale_sub (m : Fin n) (u v : ℝ) (ω : Ω) :
    vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
        - vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω
      = ∑ k : Fin d, (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
        - coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω) := by
  simp only [vectorItoMartingale, Finset.sum_sub_distrib]
variable {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)
end VectorProcess
end
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoQuadVarRiemannDecomposition.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
section VectorQuadVar
open LevyStochCalc.Brownian.Multidim
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ m k, Measurable (Function.uncurry (H m k))}
  {hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k)}
  {hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Ito in
include hC0 hCH in
/-- The product of the martingale parts' increments splits into the compensated products on the
diagonal in the Brownian index, their compensators, and the cross terms off that diagonal. -/
theorem solution (p q : Fin n) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (ω : Ω) :
    (LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs p v ω
        - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs p u ω)
      * (LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs q v ω
        - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs q u ω)
      = (∑ k : Fin d, LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k)
            (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k) u v ω)
        + (∑ k : Fin d, ∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume)
        + ∑ k : Fin d, ∑ l ∈ Finset.univ.erase k,
            LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
              (hHs q l) k l u v ω := by
  have hcomp : ∀ k : Fin d,
      (∫ s in Set.Icc (0 : ℝ) v, H p k ω s * H q k ω s ∂volume)
        - ∫ s in Set.Icc (0 : ℝ) u, H p k ω s * H q k ω s ∂volume
      = ∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume := by
    intro k
    refine LevyStochCalc.setIntegral_Icc_sub_Icc (B := C ^ 2)
      ((Measurable.of_uncurry_left (hHm p k)).mul (Measurable.of_uncurry_left (hHm q k)))
      (fun s => ?_) hu huv
    change |H p k ω s * H q k ω s| ≤ C ^ 2
    rw [abs_mul, pow_two]
    exact mul_le_mul (hCH p k ω s) (hCH q k ω s) (abs_nonneg _) hC0
  have key : ∀ k : Fin d,
      (∑ l : Fin d, (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k v ω
          - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k u ω)
        * (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs q l v ω
          - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs q l u ω))
      = LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
          (hHp p k) (hHp q k) (hHs p k) (hHs q k) u v ω
        + (∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume)
        + ∑ l ∈ Finset.univ.erase k,
            LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
              (hHs q l) k l u v ω := by
    intro k
    have hcross : ∀ l : Fin d,
        (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k v ω
            - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k u ω)
          * (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs q l v ω
            - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs q l u ω)
        = LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
            (hHs q l) k l u v ω := fun l => rfl
    simp only [hcross]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k)]
    have hdiag : LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q k) (hHp q k)
          (hHs q k) k k u v ω
        = LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
            (hHp p k) (hHp q k) (hHs p k) (hHs q k) u v ω
          + ∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume := by
      simp only [LevyStochCalc.Brownian.Ito.crossIncrement, LevyStochCalc.Brownian.Ito.polarQuadVarIncrement]
      rw [← hcomp k]
      ring
    rw [hdiag]
  calc (LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs p v ω
          - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs p u ω)
        * (LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs q v ω
          - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs q u ω)
      = (∑ k : Fin d, (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k v ω
            - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k u ω))
          * ∑ l : Fin d, (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs q l v ω
            - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs q l u ω) := by
        rw [LevyStochCalc.Brownian.Ito.vectorItoMartingale_sub W ℱ hcoord H hHm hHp hHs p u v,
          LevyStochCalc.Brownian.Ito.vectorItoMartingale_sub W ℱ hcoord H hHm hHp hHs q u v]
    _ = ∑ k : Fin d, ∑ l : Fin d, (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k v ω
          - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k u ω)
        * (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs q l v ω
          - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs q l u ω) := Finset.sum_mul_sum _ _ _ _
    _ = ∑ k : Fin d, (LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k)
            (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k) u v ω
          + (∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume)
          + ∑ l ∈ Finset.univ.erase k,
              LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                (hHs q l) k l u v ω) := Finset.sum_congr rfl fun k _ => key k
    _ = (∑ k : Fin d, LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k)
            (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k) u v ω)
          + (∑ k : Fin d, ∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume)
          + ∑ k : Fin d, ∑ l ∈ Finset.univ.erase k,
              LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                (hHs q l) k l u v ω := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
