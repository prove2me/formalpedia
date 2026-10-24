-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_quadVarRiemann_sub_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:39:00.413756+00:00
-- url     : https://prove2.me/submissions/86b14127-1380-4a39-a5d5-e859b92ccd98

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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_integral_abs_frozenRiemann_sub_le_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_integral_abs_sum_driftCross_le_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_integral_abs_sum_drift_sq_le_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_integral_abs_sum_offDiagCross_le_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_integral_abs_sum_polarQuadVar_le_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_quadVarRiemann_decomp_ae_408915f

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoQuadVarRiemannTermBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
section CellSums
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
omit [IsProbabilityMeasure P] in
/-- The first absolute moment of a sum is at most the sum of the bounds. -/
theorem LevyStochCalc.Brownian.Ito.integral_abs_add_le {f g : Ω → ℝ} (hf : Integrable f P) (hg : Integrable g P)
    {a b : ℝ} (ha : ∫ ω, |f ω| ∂P ≤ a) (hb : ∫ ω, |g ω| ∂P ≤ b) :
    ∫ ω, |f ω + g ω| ∂P ≤ a + b := by
  calc ∫ ω, |f ω + g ω| ∂P ≤ ∫ ω, (|f ω| + |g ω|) ∂P :=
        MeasureTheory.integral_mono (hf.add hg).abs (hf.abs.add hg.abs)
          (fun ω => abs_add_le _ _)
    _ = (∫ ω, |f ω| ∂P) + ∫ ω, |g ω| ∂P := MeasureTheory.integral_add hf.abs hg.abs
    _ ≤ a + b := add_le_add ha hb
omit [IsProbabilityMeasure P] in
/-- The first absolute moment of a finite sum is at most the sum of the bounds. -/
theorem LevyStochCalc.Brownian.Ito.integral_abs_finsetSum_le {ι : Type*} (s : Finset ι) (F : ι → Ω → ℝ)
    (hF : ∀ j ∈ s, Integrable (F j) P) (c : ι → ℝ) (hc : ∀ j ∈ s, ∫ ω, |F j ω| ∂P ≤ c j) :
    ∫ ω, |∑ j ∈ s, F j ω| ∂P ≤ ∑ j ∈ s, c j := by
  have hsum : Integrable (fun ω => ∑ j ∈ s, F j ω) P :=
    MeasureTheory.integrable_finsetSum _ hF
  have habs : Integrable (fun ω => ∑ j ∈ s, |F j ω|) P :=
    MeasureTheory.integrable_finsetSum _ fun j hj => (hF j hj).abs
  calc ∫ ω, |∑ j ∈ s, F j ω| ∂P ≤ ∫ ω, ∑ j ∈ s, |F j ω| ∂P :=
        MeasureTheory.integral_mono hsum.abs habs fun ω => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ s, ∫ ω, |F j ω| ∂P :=
        MeasureTheory.integral_finsetSum _ fun j hj => (hF j hj).abs
    _ ≤ ∑ j ∈ s, c j := Finset.sum_le_sum hc
end CellSums
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
namespace LevyStochCalc.Brownian.Ito.IsVectorItoVersion
end LevyStochCalc.Brownian.Ito.IsVectorItoVersion
open LevyStochCalc.Brownian.Ito.IsVectorItoVersion in
include hC0 hCH in
/-- **The weighted quadratic-variation Riemann sum converges in `L¹` at rate `√(T/m)`.** The
product of the increments of two coordinates, weighted by a bounded Lipschitz `φ(X)`, approximates
`∫_0^T φ(X_s)·(∑ₖ H^{p,k}_s H^{q,k}_s) ds`; the six groups of the decomposition contribute the six
summands of the bound. -/
theorem solution
    (h : LevyStochCalc.Brownian.Ito.IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) (p q : Fin n)
    (hma : ∀ k : Fin d, Measurable (Function.uncurry fun ω s => H p k ω s + H q k ω s))
    (hpa : ∀ k : Fin d, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => H p k ω s + H q k ω s)
    (hqa : ∀ (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ)
    (hφbd : ∀ x, |φ x| ≤ Kφ) {Mφ L : ℝ} (hMφ0 : 0 ≤ Mφ) (hL0 : 0 ≤ L)
    (hφaff : ∀ x y : Fin n → ℝ, |φ x - φ y| ≤ Mφ + L * ‖x - y‖)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => (∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * ((X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω p - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω p)
            * (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω q - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω q)))
        - ∫ s in Set.Ioc (0 : ℝ) T,
            φ (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume) P
      ∧ ∫ ω, |(∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * ((X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω p - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω p)
            * (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω q - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω q)))
        - ∫ s in Set.Ioc (0 : ℝ) T,
            φ (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume| ∂P
      ≤ (m : ℝ) * (Kφ * (B * (T / (m : ℝ))) ^ 2)
        + (m : ℝ) * (Kφ * (B * (T / (m : ℝ)) * ((d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))
        + (m : ℝ) * (Kφ * (B * (T / (m : ℝ)) * ((d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))
        + (d : ℝ) * Real.sqrt (Kφ ^ 2
            * (3 * ((2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * (2 * C) ^ 4)) * (T ^ 2 / (m : ℝ)))
        + (d : ℝ) ^ 2 * Real.sqrt (Kφ ^ 2
            * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ)))
        + (Mφ * ((d : ℝ) * C ^ 2) * T
          + L * ((d : ℝ) * C ^ 2)
            * (T * ((n : ℝ) * (B * (T / (m : ℝ))
              + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))) := by
  classical
  -- the weight of the frozen Riemann sum
  have hwm : Measurable (Function.uncurry fun ω s => ∑ k : Fin d, H p k ω s * H q k ω s) :=
    Finset.measurable_sum _ fun k _ => (hHm p k).mul (hHm q k)
  have hA0 : (0 : ℝ) ≤ (d : ℝ) * C ^ 2 := by positivity
  have hA : ∀ (ω : Ω) (s : ℝ), |∑ k : Fin d, H p k ω s * H q k ω s| ≤ (d : ℝ) * C ^ 2 := by
    intro ω s
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ k ∈ (Finset.univ : Finset (Fin d)), |H p k ω s * H q k ω s| ≤ C ^ 2 := by
      intro k _
      rw [abs_mul, pow_two]
      exact mul_le_mul (hCH p k ω s) (hCH q k ω s) (abs_nonneg _) hC0
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the six groups
  obtain ⟨i1, b1⟩ := h.integral_abs_sum_drift_sq_le_408915f hbm hB0 hB p q hφc hKφ0 hφbd hT hm0
  obtain ⟨i2, b2⟩ := h.integral_abs_sum_driftCross_le_408915f hC0 hCH hbm hB0 hB p q hφc hKφ0 hφbd hT hm0
  obtain ⟨i3, b3⟩ := h.integral_abs_sum_driftCross_le_408915f hC0 hCH hbm hB0 hB q p hφc hKφ0 hφbd hT hm0
  have hpol : ∀ k : Fin d, Integrable (fun ω : Ω => ∑ i ∈ Finset.range m,
        φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
              (hHp p k) (hHp q k) (hHs p k) (hHs q k)
              (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω) P
      ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
                (hHp p k) (hHp q k) (hHs p k) (hHs q k)
                (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω| ∂P
        ≤ Real.sqrt (Kφ ^ 2 * (3 * ((2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * (2 * C) ^ 4))
          * (T ^ 2 / (m : ℝ))) := fun k =>
    h.integral_abs_sum_polarQuadVar_le_408915f hC0 hCH p q k (hma k) (hpa k) (hqa k) hφc hKφ0 hφbd hT hm0
  have hcr : ∀ (k : Fin d), ∀ l ∈ Finset.univ.erase k,
      Integrable (fun ω : Ω => ∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
              (hHs q l) k l (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω) P
        ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                  (hHs q l) k l (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω| ∂P
          ≤ Real.sqrt (Kφ ^ 2 * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2)
            * (T ^ 2 / (m : ℝ))) := fun k l hl =>
    h.integral_abs_sum_offDiagCross_le_408915f hC0 hCH p q ((Finset.mem_erase.mp hl).1.symm)
      hφc hKφ0 hφbd hT hm0
  obtain ⟨i6, b6⟩ := h.integral_abs_frozenRiemann_sub_le_408915f hC0 hCH hbm hB0 hB
    (fun ω s => ∑ k : Fin d, H p k ω s * H q k ω s) hwm hA0 hA hφc hφbd hMφ0 hL0 hφaff hT hm0
  -- integrability of the grouped sums
  have i4 : Integrable (fun ω : Ω => ∑ k : Fin d, ∑ i ∈ Finset.range m,
      φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        * LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
            (hHp p k) (hHp q k) (hHs p k) (hHs q k)
            (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω) P :=
    MeasureTheory.integrable_finsetSum _ fun k _ => (hpol k).1
  have i5 : Integrable (fun ω : Ω => ∑ k : Fin d, ∑ l ∈ Finset.univ.erase k,
      ∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        * LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
            (hHs q l) k l (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω) P :=
    MeasureTheory.integrable_finsetSum _ fun k _ =>
      MeasureTheory.integrable_finsetSum _ fun l hl => (hcr k l hl).1
  -- the bounds on the two grouped sums
  have b4 : ∫ ω, |∑ k : Fin d, ∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        * LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
            (hHp p k) (hHp q k) (hHs p k) (hHs q k)
            (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω| ∂P
      ≤ (d : ℝ) * Real.sqrt (Kφ ^ 2
        * (3 * ((2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * (2 * C) ^ 4)) * (T ^ 2 / (m : ℝ))) := by
    refine (LevyStochCalc.Brownian.Ito.integral_abs_finsetSum_le _ _ (fun k _ => (hpol k).1) _
      (fun k _ => (hpol k).2)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have b5 : ∫ ω, |∑ k : Fin d, ∑ l ∈ Finset.univ.erase k, ∑ i ∈ Finset.range m,
        φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
              (hHs q l) k l (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω| ∂P
      ≤ (d : ℝ) ^ 2 * Real.sqrt (Kφ ^ 2
        * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ))) := by
    have hsqrt0 : (0 : ℝ) ≤ Real.sqrt (Kφ ^ 2
        * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ))) :=
      Real.sqrt_nonneg _
    refine (LevyStochCalc.Brownian.Ito.integral_abs_finsetSum_le _ _
      (fun k _ => MeasureTheory.integrable_finsetSum _ fun l hl => (hcr k l hl).1)
      (fun k => ∑ _l ∈ Finset.univ.erase k, Real.sqrt (Kφ ^ 2
        * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ))))
      (fun k _ => LevyStochCalc.Brownian.Ito.integral_abs_finsetSum_le _ _ (fun l hl => (hcr k l hl).1) _
        (fun l hl => (hcr k l hl).2))).trans ?_
    have hk : ∀ k : Fin d, ∑ _l ∈ Finset.univ.erase k, Real.sqrt (Kφ ^ 2
          * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ)))
        ≤ (d : ℝ) * Real.sqrt (Kφ ^ 2
          * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ))) := by
      intro k
      refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun l _ _ => hsqrt0)).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    refine (Finset.sum_le_sum fun k _ => hk k).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring_nf
    exact le_rfl
  -- assemble
  have hae : (fun ω : Ω => |(∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        * ((X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω p - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω p)
          * (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω q - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω q)))
      - ∫ s in Set.Ioc (0 : ℝ) T,
          φ (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume|)
      =ᵐ[P] fun ω => |((((∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * ((∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
                    bdrift p ω s ∂volume)
                * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
                    bdrift q ω s ∂volume))
            + (∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * ((∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
                    bdrift p ω s ∂volume)
                * (LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
                  - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω))))
            + (∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * ((∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
                    bdrift q ω s ∂volume)
                * (LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
                  - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω))))
            + (∑ k : Fin d, ∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
                  (hHp p k) (hHp q k) (hHs p k) (hHs q k)
                  (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω))
            + (∑ k : Fin d, ∑ l ∈ Finset.univ.erase k, ∑ i ∈ Finset.range m,
              φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
                * LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                    (hHs q l) k l (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω)
          + ((∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
                  ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)
            - ∫ s in Set.Ioc (0 : ℝ) T,
                φ (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)| := by
    filter_upwards [h.quadVarRiemann_decomp_ae_408915f hC0 hCH hbm hB p q φ hT hm0] with ω hω
    rw [hω]
    congr 1
    ring
  refine ⟨?_, ?_⟩
  · refine (((((i1.add i2).add i3).add i4).add i5).add i6).congr ?_
    filter_upwards [h.quadVarRiemann_decomp_ae_408915f hC0 hCH hbm hB p q φ hT hm0] with ω hω
    simp only [Pi.add_apply]
    rw [hω]
    ring
  rw [MeasureTheory.integral_congr_ae hae]
  exact LevyStochCalc.Brownian.Ito.integral_abs_add_le ((((i1.add i2).add i3).add i4).add i5) i6
    (LevyStochCalc.Brownian.Ito.integral_abs_add_le (((i1.add i2).add i3).add i4) i5
      (LevyStochCalc.Brownian.Ito.integral_abs_add_le ((i1.add i2).add i3) i4
        (LevyStochCalc.Brownian.Ito.integral_abs_add_le (i1.add i2) i3 (LevyStochCalc.Brownian.Ito.integral_abs_add_le i1 i2 b1 b2) b3) b4) b5) b6
