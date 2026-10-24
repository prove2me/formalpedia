-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormula_localise_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:19:21.896235+00:00
-- url     : https://prove2.me/submissions/21ec94fd-1b7d-462f-98be-fa1731fa92b8

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CoordDerivative
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CrossVariation
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_CrossVariationSum
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Existence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoAlgebraAssociativity
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoAlgebraProduct
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoCutoff
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityDyadicAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPointwise
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPredictableL2
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityShiftedAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityUnbounded
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoFormulaGrid
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoFourthMomentIncrements
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoFourthMomentLintegral
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoIncrementMomentRestrict
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionApi
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionConvergence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionExistence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionLp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionQuadVar
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoLocality
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoMartingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoOptionalStopping
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoPullOut
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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SmoothCutoff
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_TaylorTwoVector
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_VectorItoFormula
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_VectorItoProcess
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_VectorItoProcessVersion
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Augmentation
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_ExitTime
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Progressive
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_StoppedProgressive
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Transport
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_TrivialSigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Rat.Denumerable
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
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.CompactSystem
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.EMetricSpace.PairReduction
import Mathlib.Topology.IsClosedRestrict
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Topology.MetricSpace.MetricSeparated
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.UniformSpace.HeineCantor
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_congr_of_le_408915f
import Theorems.Thm_LevyStochCalc_Probability_exists_lt_exitTime_408915f
import Theorems.Thm_LevyStochCalc_Probability_exitTime_le_iff_408915f
import Theorems.Thm_LevyStochCalc_Probability_exitTime_le_iff_forall_408915f
import Theorems.Thm_LevyStochCalc_Probability_norm_le_of_le_exitTime_408915f
import Theorems.Thm_LevyStochCalc_norm_le_sum_abs_apply_408915f
import Theorems.Thm_LevyStochCalc_norm_le_sum_abs_apply_two_408915f

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcessVersion.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
section VectorVersion
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
variable {W ℱ hcoord H hHm hHp hHs} {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ}
  {X : ℝ → Ω → Fin n → ℝ}
/-- A version's time slices are measurable. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.measurable
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) (t : ℝ) :
    Measurable (X t) := ((h.adapted t).mono (ℱ.le t)).measurable
/-- A version's paths are jointly measurable in the sample point and the time. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.measurable_uncurry
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) :
    Measurable (Function.uncurry fun ω s => X s ω) := by
  have hjoint : Measurable (Function.uncurry X) :=
    measurable_uncurry_of_continuous_of_measurable h.continuous_path h.measurable
  exact hjoint.comp measurable_swap
/-- A continuous function of a version is progressively measurable. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.progressivelyMeasurable_comp
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) {φ : (Fin n → ℝ) → ℝ}
    (hφ : Continuous φ) : Probability.ProgressivelyMeasurable ℱ fun ω s => φ (X s ω) := by
  refine Probability.ProgressivelyMeasurable.of_isStronglyProgressive ?_
  refine MeasureTheory.StronglyAdapted.isStronglyProgressive_of_continuous
    (fun t => hφ.comp_stronglyMeasurable (h.adapted t)) fun ω => ?_
  exact hφ.comp (h.continuous_path ω)
/-- A measurable function of a version is jointly measurable. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.measurable_uncurry_comp
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) {φ : (Fin n → ℝ) → ℝ}
    (hφ : Measurable φ) : Measurable (Function.uncurry fun ω s => φ (X s ω)) :=
  hφ.comp h.measurable_uncurry
end VectorVersion
end
end
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CoordDerivative.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
open ContinuousLinearMap
variable {n : ℕ}
section Coord
variable {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
/-- A partial derivative is bounded by the operator norm of the Fréchet derivative. -/
theorem LevyStochCalc.abs_coordDeriv_le {K₁ : ℝ} (h : ∀ x, ‖f' x‖ ≤ K₁) (p : Fin n) (x : Fin n → ℝ) :
    |coordDeriv f' p x| ≤ K₁ := by
  have hnorm : ‖(Pi.single p 1 : Fin n → ℝ)‖ = 1 := by
    rw [Pi.norm_single, norm_one]
  calc |coordDeriv f' p x| = ‖f' x (Pi.single p 1)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖f' x‖ * ‖(Pi.single p 1 : Fin n → ℝ)‖ := (f' x).le_opNorm _
    _ = ‖f' x‖ := by rw [hnorm, mul_one]
    _ ≤ K₁ := h x
/-- Continuity of a partial derivative. -/
theorem LevyStochCalc.continuous_coordDeriv (hf'c : Continuous f') (p : Fin n) :
    Continuous (coordDeriv f' p) :=
  hf'c.clm_apply continuous_const
end Coord
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/SmoothCutoff.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
open scoped Topology
section OneDim
theorem LevyStochCalc.contDiff_smoothCut (k : ℝ) {N : ℕ∞} : ContDiff ℝ N (smoothCut k) := by
  unfold smoothCut
  exact Real.smoothTransition.contDiff.comp (by fun_prop)
theorem LevyStochCalc.smoothCut_eq_one {k t : ℝ} (hk : 0 < k) (ht : |t| ≤ 3 * k / 2) : smoothCut k t = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 7 * k ^ 2)]
  nlinarith [abs_nonneg t, sq_abs t, ht, hk]
theorem LevyStochCalc.smoothCut_eq_zero {k t : ℝ} (hk : 0 < k) (ht : 2 * k ≤ |t|) : smoothCut k t = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  refine div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
  nlinarith [abs_nonneg t, sq_abs t, ht, hk]
end OneDim
section Box
variable {n : ℕ}
theorem LevyStochCalc.contDiff_boxCut (k : ℝ) {N : ℕ∞} : ContDiff ℝ N (boxCut (n := n) k) := by
  unfold boxCut
  exact contDiff_prod fun i _ => (contDiff_smoothCut k).comp (contDiff_apply ℝ ℝ i)
theorem LevyStochCalc.boxCut_eq_one {k : ℝ} (hk : 0 < k) {z : Fin n → ℝ} (hz : ‖z‖ ≤ 3 * k / 2) :
    boxCut k z = 1 := by
  refine Finset.prod_eq_one fun i _ => smoothCut_eq_one hk ?_
  have := (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * k / 2)).mp hz i
  simpa [Real.norm_eq_abs] using this
theorem LevyStochCalc.boxCut_eventuallyEq_one {k : ℝ} (hk : 0 < k) {z : Fin n → ℝ} (hz : ‖z‖ < 3 * k / 2) :
    boxCut (n := n) k =ᶠ[𝓝 z] fun _ => (1 : ℝ) := by
  have hopen : IsOpen {w : Fin n → ℝ | ‖w‖ < 3 * k / 2} :=
    isOpen_lt continuous_norm continuous_const
  filter_upwards [hopen.mem_nhds hz] with w hw
  exact boxCut_eq_one hk (le_of_lt hw)
theorem LevyStochCalc.boxCut_eq_zero {k : ℝ} (hk : 0 < k) {z : Fin n → ℝ} (hz : 2 * k < ‖z‖) :
    boxCut k z = 0 := by
  have hex : ∃ i : Fin n, 2 * k ≤ |z i| := by
    by_contra hcon
    have hcon' : ∀ i : Fin n, |z i| < 2 * k := fun i => not_le.mp fun h => hcon ⟨i, h⟩
    have hle : ‖z‖ ≤ 2 * k := by
      refine (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * k)).mpr fun i => ?_
      simpa [Real.norm_eq_abs] using (hcon' i).le
    linarith
  obtain ⟨i, hi⟩ := hex
  exact Finset.prod_eq_zero (Finset.mem_univ i) (smoothCut_eq_zero hk hi)
end Box
section UniformContinuity
/-- **A continuous function with compact support on a proper normed space is uniformly
continuous**, in `ε`–`δ` form. -/
theorem LevyStochCalc.exists_delta_of_hasCompactSupport {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {u : E → F} (hu : Continuous u) (hsupp : HasCompactSupport u)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ ∀ z w : E, ‖z - w‖ < δ → ‖u z - u w‖ ≤ ε := by
  have huc : UniformContinuous u :=
    hu.uniformContinuous_of_tendsto_cocompact hsupp.is_zero_at_infty
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuous_iff.mp huc ε hε
  refine ⟨δ, hδ0, fun z w hzw => ?_⟩
  have hd : dist z w < δ := by rwa [dist_eq_norm]
  have := hδ hd
  rw [dist_eq_norm] at this
  exact this.le
end UniformContinuity
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/ExitTime.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc LevyStochCalc.Probability
universe u v
variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [NormedAddCommGroup E]
theorem LevyStochCalc.Probability.gridPt_mem_Icc {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : gridPt t n ∈ Set.Icc (0 : ℝ) t :=
  ⟨le_max_left _ _, max_le ht (min_le_left _ _)⟩
theorem LevyStochCalc.Probability.measurable_norm_of_adapted [MeasurableSpace E] [OpensMeasurableSpace E]
    {ℱ : Filtration ℝ mΩ} {X : Ω → ℝ → E} (hadapt : Adapted ℱ fun r ω => X ω r) (r : ℝ) :
    Measurable[ℱ r] fun ω => ‖X ω r‖ := by
  letI : MeasurableSpace Ω := ℱ r
  exact Measurable.norm (hadapt r)
theorem LevyStochCalc.Probability.measurableSet_exitTime_le {ℱ : Filtration ℝ mΩ} [MeasurableSpace E]
    [OpensMeasurableSpace E] {X : Ω → ℝ → E} (hadapt : Adapted ℱ fun r ω => X ω r)
    (hcont : ∀ ω, Continuous (X ω)) (k t : ℝ) :
    MeasurableSet[ℱ t] {ω | exitTime X k ω ≤ (t : WithTop ℝ)} := by
  rcases lt_or_ge t 0 with ht | ht
  · have hempty : {ω | exitTime X k ω ≤ (t : WithTop ℝ)} = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hle
      obtain ⟨s, hs, -⟩ := (exitTime_le_iff_408915f (hcont ω) k t).1 hle
      exact absurd (hs.1.trans hs.2) (not_le.2 ht)
    rw [hempty]
    exact @MeasurableSet.empty Ω (ℱ t)
  · have hset : {ω | exitTime X k ω ≤ (t : WithTop ℝ)}
        = ⋂ n : ℕ, ⋃ m : ℕ, {ω | k - ((n : ℝ) + 1)⁻¹ < ‖X ω (gridPt t m)‖} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
      exact exitTime_le_iff_forall_408915f (hcont ω) k ht
    rw [hset]
    have hmeas : ∀ m : ℕ, Measurable[ℱ t] fun ω => ‖X ω (gridPt t m)‖ := fun m =>
      (measurable_norm_of_adapted hadapt (gridPt t m)).mono
        (ℱ.mono (gridPt_mem_Icc ht m).2) le_rfl
    letI : MeasurableSpace Ω := ℱ t
    exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun m =>
      measurableSet_lt measurable_const (hmeas m)
/-- The exit time of a continuous adapted process is a stopping time. -/
theorem LevyStochCalc.Probability.isStoppingTime_exitTime {ℱ : Filtration ℝ mΩ} [MeasurableSpace E]
    [OpensMeasurableSpace E] {X : Ω → ℝ → E} (hadapt : Adapted ℱ fun r ω => X ω r)
    (hcont : ∀ ω, Continuous (X ω)) (k : ℝ) :
    IsStoppingTime ℱ (exitTime X k) := fun t => measurableSet_exitTime_le hadapt hcont k t
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoCutoff.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
open scoped Topology
section Cutoff
variable {n : ℕ}
theorem LevyStochCalc.contDiff_cutoffFun {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (k : ℝ) :
    ContDiff ℝ 2 (cutoffFun f k) :=
  hf.mul (contDiff_boxCut (n := n) k)
theorem LevyStochCalc.cutoffFun_eventuallyEq {f : (Fin n → ℝ) → ℝ} {k : ℝ} (hk : 0 < k) {z : Fin n → ℝ}
    (hz : ‖z‖ < 3 * k / 2) : cutoffFun f k =ᶠ[𝓝 z] f := by
  filter_upwards [boxCut_eventuallyEq_one (n := n) hk hz] with w hw
  simp [cutoffFun, hw]
theorem LevyStochCalc.fderiv_cutoffFun {f : (Fin n → ℝ) → ℝ} {k : ℝ} (hk : 0 < k) {z : Fin n → ℝ}
    (hz : ‖z‖ < 3 * k / 2) : fderiv ℝ (cutoffFun f k) z = fderiv ℝ f z :=
  (cutoffFun_eventuallyEq hk hz).fderiv_eq
theorem LevyStochCalc.fderiv_fderiv_cutoffFun {f : (Fin n → ℝ) → ℝ} {k : ℝ} (hk : 0 < k) {z : Fin n → ℝ}
    (hz : ‖z‖ < 3 * k / 2) :
    fderiv ℝ (fderiv ℝ (cutoffFun f k)) z = fderiv ℝ (fderiv ℝ f) z := by
  have hopen : IsOpen {w : Fin n → ℝ | ‖w‖ < 3 * k / 2} :=
    isOpen_lt continuous_norm continuous_const
  have hev : fderiv ℝ (cutoffFun f k) =ᶠ[𝓝 z] fderiv ℝ f := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact fderiv_cutoffFun hk hw
  exact hev.fderiv_eq
theorem LevyStochCalc.continuous_fderiv_cutoffFun {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (k : ℝ) :
    Continuous (fderiv ℝ (cutoffFun f k)) :=
  ((contDiff_cutoffFun hf k).fderiv_right (m := 1) (by norm_num)).continuous
theorem LevyStochCalc.continuous_fderiv_fderiv_cutoffFun {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (k : ℝ) :
    Continuous (fderiv ℝ (fderiv ℝ (cutoffFun f k))) :=
  (((contDiff_cutoffFun hf k).fderiv_right (m := 1) (by norm_num)).fderiv_right
    (m := 0) (by norm_num)).continuous
theorem LevyStochCalc.differentiable_cutoffFun {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (k : ℝ) :
    Differentiable ℝ (cutoffFun f k) :=
  (contDiff_cutoffFun hf k).differentiable (by norm_num)
theorem LevyStochCalc.differentiable_fderiv_cutoffFun {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (k : ℝ) :
    Differentiable ℝ (fderiv ℝ (cutoffFun f k)) :=
  ((contDiff_cutoffFun hf k).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
theorem LevyStochCalc.cutoffFun_eventuallyEq_zero {f : (Fin n → ℝ) → ℝ} {k : ℝ} (hk : 0 < k) {z : Fin n → ℝ}
    (hz : 2 * k < ‖z‖) : cutoffFun f k =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
  have hopen : IsOpen {w : Fin n → ℝ | 2 * k < ‖w‖} :=
    isOpen_lt continuous_const continuous_norm
  filter_upwards [hopen.mem_nhds hz] with w hw
  simp [cutoffFun, boxCut_eq_zero hk hw]
theorem LevyStochCalc.fderiv_cutoffFun_eq_zero {f : (Fin n → ℝ) → ℝ} {k : ℝ} (hk : 0 < k) {z : Fin n → ℝ}
    (hz : 2 * k < ‖z‖) : fderiv ℝ (cutoffFun f k) z = 0 := by
  rw [(cutoffFun_eventuallyEq_zero (f := f) hk hz).fderiv_eq]
  simp
theorem LevyStochCalc.fderiv_fderiv_cutoffFun_eq_zero {f : (Fin n → ℝ) → ℝ} {k : ℝ} (hk : 0 < k)
    {z : Fin n → ℝ} (hz : 2 * k < ‖z‖) : fderiv ℝ (fderiv ℝ (cutoffFun f k)) z = 0 := by
  have hopen : IsOpen {w : Fin n → ℝ | 2 * k < ‖w‖} :=
    isOpen_lt continuous_const continuous_norm
  have hev : fderiv ℝ (cutoffFun f k) =ᶠ[𝓝 z] fun _ => (0 : (Fin n → ℝ) →L[ℝ] ℝ) := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact fderiv_cutoffFun_eq_zero (f := f) hk hw
  rw [hev.fderiv_eq]
  simp
theorem LevyStochCalc.continuous_gradVec {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (k : ℝ) :
    Continuous (gradVec (cutoffFun f k)) :=
  continuous_pi fun _ => (continuous_fderiv_cutoffFun hf k).clm_apply continuous_const
theorem LevyStochCalc.continuous_hessVec {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (k : ℝ) :
    Continuous (hessVec (cutoffFun f k)) :=
  continuous_pi fun _ =>
    ((continuous_fderiv_fderiv_cutoffFun hf k).clm_apply continuous_const).clm_apply
      continuous_const
theorem LevyStochCalc.hasCompactSupport_gradVec (f : (Fin n → ℝ) → ℝ) {k : ℝ} (hk : 0 < k) :
    HasCompactSupport (gradVec (cutoffFun f k)) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin n → ℝ) (2 * k)) fun z hz => ?_
  have hz' : 2 * k < ‖z‖ := by
    by_contra hcon
    exact hz (by simpa [Metric.mem_closedBall, dist_eq_norm] using not_lt.mp hcon)
  funext p
  simp [gradVec, fderiv_cutoffFun_eq_zero (f := f) hk hz']
theorem LevyStochCalc.hasCompactSupport_hessVec (f : (Fin n → ℝ) → ℝ) {k : ℝ} (hk : 0 < k) :
    HasCompactSupport (hessVec (cutoffFun f k)) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin n → ℝ) (2 * k)) fun z hz => ?_
  have hz' : 2 * k < ‖z‖ := by
    by_contra hcon
    exact hz (by simpa [Metric.mem_closedBall, dist_eq_norm] using not_lt.mp hcon)
  funext pq
  simp [hessVec, fderiv_fderiv_cutoffFun_eq_zero (f := f) hk hz']
theorem LevyStochCalc.exists_bound_fderiv_cutoffFun {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {k : ℝ}
    (hk : 0 < k) : ∃ K₁ : ℝ, ∀ z, ‖fderiv ℝ (cutoffFun f k) z‖ ≤ K₁ := by
  obtain ⟨M, hM⟩ := (hasCompactSupport_gradVec f hk).exists_bound_of_continuous
    (continuous_gradVec hf k)
  refine ⟨(n : ℝ) * M, fun z => ?_⟩
  refine (norm_le_sum_abs_apply_408915f (fderiv ℝ (cutoffFun f k) z)).trans ?_
  have hterm : ∀ p ∈ (Finset.univ : Finset (Fin n)),
      |fderiv ℝ (cutoffFun f k) z (Pi.single p 1)| ≤ M := by
    intro p _
    have := norm_le_pi_norm (gradVec (cutoffFun f k) z) p
    have h2 := hM z
    simp only [gradVec, Real.norm_eq_abs] at this
    linarith
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
theorem LevyStochCalc.exists_bound_fderiv_fderiv_cutoffFun {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {k : ℝ}
    (hk : 0 < k) :
    ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ z, ‖fderiv ℝ (fderiv ℝ (cutoffFun f k)) z‖ ≤ K₂ := by
  obtain ⟨M, hM⟩ := (hasCompactSupport_hessVec f hk).exists_bound_of_continuous
    (continuous_hessVec hf k)
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) (hM 0)
  refine ⟨(n : ℝ) * ((n : ℝ) * M), by positivity, fun z => ?_⟩
  refine (norm_le_sum_abs_apply_two_408915f (fderiv ℝ (fderiv ℝ (cutoffFun f k)) z)).trans ?_
  have hterm : ∀ p ∈ (Finset.univ : Finset (Fin n)),
      (∑ q, |fderiv ℝ (fderiv ℝ (cutoffFun f k)) z (Pi.single p 1) (Pi.single q 1)|)
        ≤ (n : ℝ) * M := by
    intro p _
    have hq : ∀ q ∈ (Finset.univ : Finset (Fin n)),
        |fderiv ℝ (fderiv ℝ (cutoffFun f k)) z (Pi.single p 1) (Pi.single q 1)| ≤ M := by
      intro q _
      have h1 := norm_le_pi_norm (hessVec (cutoffFun f k) z) (p, q)
      have h2 := hM z
      simp only [hessVec, Real.norm_eq_abs] at h1
      linarith
    refine (Finset.sum_le_sum hq).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
theorem LevyStochCalc.exists_delta_fderiv_fderiv_cutoffFun {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {k : ℝ}
    (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z w : Fin n → ℝ, ‖z - w‖ < δ →
      ‖fderiv ℝ (fderiv ℝ (cutoffFun f k)) z - fderiv ℝ (fderiv ℝ (cutoffFun f k)) w‖ ≤ ε := by
  have hpos : (0 : ℝ) < ε / ((n : ℝ) * (n : ℝ) + 1) := by positivity
  obtain ⟨δ, hδ0, hδ⟩ := exists_delta_of_hasCompactSupport (continuous_hessVec hf k)
    (hasCompactSupport_hessVec f hk) hpos
  refine ⟨δ, hδ0, fun z w hzw => ?_⟩
  set c : ℝ := ε / ((n : ℝ) * (n : ℝ) + 1) with hc
  have hcnn : (0 : ℝ) ≤ c := hpos.le
  have hcoord : ∀ p q : Fin n,
      |fderiv ℝ (fderiv ℝ (cutoffFun f k)) z (Pi.single p 1) (Pi.single q 1)
        - fderiv ℝ (fderiv ℝ (cutoffFun f k)) w (Pi.single p 1) (Pi.single q 1)| ≤ c := by
    intro p q
    have h1 := norm_le_pi_norm
      (hessVec (cutoffFun f k) z - hessVec (cutoffFun f k) w) (p, q)
    have h2 := hδ z w hzw
    simp only [Pi.sub_apply, hessVec, Real.norm_eq_abs] at h1
    linarith
  have hsub : fderiv ℝ (fderiv ℝ (cutoffFun f k)) z - fderiv ℝ (fderiv ℝ (cutoffFun f k)) w
      = (fderiv ℝ (fderiv ℝ (cutoffFun f k)) z - fderiv ℝ (fderiv ℝ (cutoffFun f k)) w) := rfl
  refine (norm_le_sum_abs_apply_two_408915f
    (fderiv ℝ (fderiv ℝ (cutoffFun f k)) z - fderiv ℝ (fderiv ℝ (cutoffFun f k)) w)).trans ?_
  have hterm : ∀ p ∈ (Finset.univ : Finset (Fin n)),
      (∑ q, |(fderiv ℝ (fderiv ℝ (cutoffFun f k)) z
          - fderiv ℝ (fderiv ℝ (cutoffFun f k)) w) (Pi.single p 1) (Pi.single q 1)|)
        ≤ (n : ℝ) * c := by
    intro p _
    have hq : ∀ q ∈ (Finset.univ : Finset (Fin n)),
        |(fderiv ℝ (fderiv ℝ (cutoffFun f k)) z
          - fderiv ℝ (fderiv ℝ (cutoffFun f k)) w) (Pi.single p 1) (Pi.single q 1)| ≤ c := by
      intro q _
      simpa using hcoord p q
    refine (Finset.sum_le_sum hq).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hc]
  have hd : (0 : ℝ) < (n : ℝ) * (n : ℝ) + 1 := by positivity
  have hrw : (n : ℝ) * ((n : ℝ) * (ε / ((n : ℝ) * (n : ℝ) + 1)))
      = (n : ℝ) * (n : ℝ) * ε / ((n : ℝ) * (n : ℝ) + 1) := by ring
  rw [hrw, div_le_iff₀ hd]
  nlinarith [hε.le]
end Cutoff
section
namespace LevyStochCalc.Brownian
end LevyStochCalc.Brownian
open LevyStochCalc LevyStochCalc.Brownian
section
namespace LevyStochCalc.Brownian.Ito
end LevyStochCalc.Brownian.Ito
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim LevyStochCalc.Probability
open scoped NNReal ENNReal
universe u
section Bounded
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
omit [IsProbabilityMeasure P] in
/-- A pointwise bound `|u| ≤ c|v|` squares into a bound on the extended norms. -/
theorem LevyStochCalc.Brownian.Ito.sq_enorm_le_of_abs_le {c : ℝ} (hc : 0 ≤ c) {u v : ℝ} (h : |u| ≤ c * |v|) :
    (‖u‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (c ^ 2) * (‖v‖₊ : ℝ≥0∞) ^ 2 := by
  have h1 : ‖u‖₊ ≤ Real.toNNReal c * ‖v‖₊ := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [Real.coe_toNNReal c hc]
    simpa [Real.norm_eq_abs] using h
  calc (‖u‖₊ : ℝ≥0∞) ^ 2 ≤ ((Real.toNNReal c * ‖v‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 := by
        exact pow_le_pow_left' (by exact_mod_cast h1) 2
    _ = ENNReal.ofReal (c ^ 2) * (‖v‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.coe_mul, mul_pow, ← ENNReal.coe_pow, ← Real.toNNReal_pow hc]
        rfl
omit [IsProbabilityMeasure P] in
/-- The energy of an integrand dominated by a multiple of another one is finite whenever the
dominating integrand's is. -/
theorem LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le_mul {K G : Ω → ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hbd : ∀ (ω : Ω) (s : ℝ), |K ω s| ≤ c * |G ω s|)
    (hG : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro T hT
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          ENNReal.ofReal (c ^ 2) * (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        MeasureTheory.lintegral_mono fun ω =>
          MeasureTheory.lintegral_mono fun s => sq_enorm_le_of_abs_le hc (hbd ω s)
    _ = ENNReal.ofReal (c ^ 2) * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        simp only [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hG T hT)
end Bounded
section Formula
open LevyStochCalc.Brownian.Multidim
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
  {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)}
  {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H p k ω s| ≤ C)
namespace LevyStochCalc.Brownian.Ito.IsVectorItoVersion
end LevyStochCalc.Brownian.Ito.IsVectorItoVersion
open LevyStochCalc.Brownian.Ito.IsVectorItoVersion in
/-- **The localisation step of Itô's formula.** The formula for a `C²` function follows from the
formula for functions with bounded first and second derivatives. -/
theorem solution
    (h : LevyStochCalc.Brownian.Ito.IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d), LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
      fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (hbase : ∀ (g : (Fin n → ℝ) → ℝ) (g' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ)
      (g'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) (K₁ K₂ : ℝ),
      (∀ z, HasFDerivAt g (g' z) z) → (∀ z, HasFDerivAt g' (g'' z) z) →
      (∀ z, ‖g' z‖ ≤ K₁) → 0 ≤ K₂ → (∀ z, ‖g'' z‖ ≤ K₂) →
      Continuous g' → Continuous g'' →
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ z w : Fin n → ℝ, ‖z - w‖ < δ → ‖g'' z - g'' w‖ ≤ ε) →
      ∀ (hmG : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
          fun ω s => LevyStochCalc.coordDeriv g' p (X s ω) * H p k ω s))
        (hpG : ∀ (p : Fin n) (k : Fin d), LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
          fun ω s => LevyStochCalc.coordDeriv g' p (X s ω) * H p k ω s)
        (hqG : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
            (‖LevyStochCalc.coordDeriv g' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      (fun ω : Ω => g (X T ω) - g (X 0 ω)) =ᵐ[P] fun ω : Ω =>
        (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            LevyStochCalc.coordDeriv g' p (X s ω) * bdrift p ω s ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => LevyStochCalc.coordDeriv g' p (X s ω) * H p k ω s)
              (hmG p k) (hpG p k) (hqG p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              LevyStochCalc.coordDeriv₂ g'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume) :
    (fun ω : Ω => f (X T ω) - f (X 0 ω)) =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
        + (∑ p : Fin n, ∑ j : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hcoord j)
            (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p j ω s)
            (hmg p j) (hpg p j) (hqg p j) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            LevyStochCalc.coordDeriv₂ f'' p q (X s ω) * ∑ j : Fin d, H p j ω s * H q j ω s ∂volume := by
  classical
  have hf'eq : f' = fderiv ℝ f := funext fun z => (hf z).fderiv.symm
  have hf''eq : f'' = fderiv ℝ (fderiv ℝ f) := by
    funext z
    have hz := (hf' z).fderiv
    rw [← hf'eq]
    exact hz.symm
  have hstep : ∀ m : ℕ, 0 < m → ∀ᵐ ω ∂P,
      ((T : ℝ) : WithTop ℝ) < LevyStochCalc.Probability.exitTime (fun ω t => X t ω) (m : ℝ) ω →
        f (X T ω) - f (X 0 ω)
          = (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
            + (∑ p : Fin n, ∑ j : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hcoord j)
                (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p j ω s)
                (hmg p j) (hpg p j) (hqg p j) T ω)
            + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
                  * ∑ j : Fin d, H p j ω s * H q j ω s ∂volume := by
    intro m hm0
    have hR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
    set R : ℝ := (m : ℝ) with hRdef
    set g : (Fin n → ℝ) → ℝ := LevyStochCalc.cutoffFun f R with hgdef
    set τ : Ω → WithTop ℝ := LevyStochCalc.Probability.exitTime (fun ω t => X t ω) R with hτdef
    have hadapt : MeasureTheory.Adapted ℱ (fun r ω => X r ω) :=
      fun r => (h.adapted r).measurable
    have hτ : MeasureTheory.IsStoppingTime ℱ τ :=
      LevyStochCalc.Probability.isStoppingTime_exitTime (X := fun ω t => X t ω) hadapt
        (fun ω => h.continuous_path ω) R
    have hR32 : R < 3 * R / 2 := by linarith
    have hg'c : Continuous (fderiv ℝ g) := LevyStochCalc.continuous_fderiv_cutoffFun hfC R
    have hg''c : Continuous (fderiv ℝ (fderiv ℝ g)) := LevyStochCalc.continuous_fderiv_fderiv_cutoffFun hfC R
    have hgf : ∀ z, HasFDerivAt g (fderiv ℝ g z) z :=
      fun z => (LevyStochCalc.differentiable_cutoffFun hfC R z).hasFDerivAt
    have hgf' : ∀ z, HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) z) z :=
      fun z => (LevyStochCalc.differentiable_fderiv_cutoffFun hfC R z).hasFDerivAt
    obtain ⟨K₁, hK₁⟩ := LevyStochCalc.exists_bound_fderiv_cutoffFun hfC hR
    obtain ⟨K₂, hK₂0, hK₂⟩ := LevyStochCalc.exists_bound_fderiv_fderiv_cutoffFun hfC hR
    have hK₁0 : (0 : ℝ) ≤ K₁ := le_trans (norm_nonneg _) (hK₁ 0)
    have hunif : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ z w : Fin n → ℝ, ‖z - w‖ < δ →
          ‖fderiv ℝ (fderiv ℝ g) z - fderiv ℝ (fderiv ℝ g) w‖ ≤ ε :=
      fun ε hε => LevyStochCalc.exists_delta_fderiv_fderiv_cutoffFun hfC hR hε
    -- the two families of integrands agree on the cube
    have hd1 : ∀ (p : Fin n) (z : Fin n → ℝ), ‖z‖ < 3 * R / 2 →
        LevyStochCalc.coordDeriv (fderiv ℝ g) p z = LevyStochCalc.coordDeriv f' p z := by
      intro p z hz
      rw [hf'eq]
      unfold LevyStochCalc.coordDeriv
      rw [LevyStochCalc.fderiv_cutoffFun (f := f) hR hz]
    have hd2 : ∀ (p q : Fin n) (z : Fin n → ℝ), ‖z‖ < 3 * R / 2 →
        LevyStochCalc.coordDeriv₂ (fderiv ℝ (fderiv ℝ g)) p q z = LevyStochCalc.coordDeriv₂ f'' p q z := by
      intro p q z hz
      rw [hf''eq]
      unfold LevyStochCalc.coordDeriv₂
      rw [LevyStochCalc.fderiv_fderiv_cutoffFun (f := f) hR hz]
    have hd0 : ∀ z : Fin n → ℝ, ‖z‖ < 3 * R / 2 → g z = f z := by
      intro z hz
      rw [hgdef, LevyStochCalc.cutoffFun, LevyStochCalc.boxCut_eq_one hR hz.le, mul_one]
    -- the cut integrands
    have hmgG : ∀ (p : Fin n) (j : Fin d),
        Measurable (Function.uncurry fun ω s =>
          LevyStochCalc.coordDeriv (fderiv ℝ g) p (X s ω) * H p j ω s) :=
      fun p j =>
        (h.measurable_uncurry_comp (LevyStochCalc.continuous_coordDeriv hg'c p).measurable).mul (hHm p j)
    have hpgG : ∀ (p : Fin n) (j : Fin d), LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
        fun ω s => LevyStochCalc.coordDeriv (fderiv ℝ g) p (X s ω) * H p j ω s :=
      fun p j => (h.progressivelyMeasurable_comp (LevyStochCalc.continuous_coordDeriv hg'c p)).mul (hHp p j)
    have hqgG : ∀ (p : Fin n) (j : Fin d) (T' : ℝ), 0 < T' →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖LevyStochCalc.coordDeriv (fderiv ℝ g) p (X s ω) * H p j ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro p j
      refine LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le_mul (c := K₁) hK₁0 (fun ω s => ?_) (hHs p j)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (LevyStochCalc.abs_coordDeriv_le hK₁ p _) (abs_nonneg _)
    have hform := hbase g (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g)) K₁ K₂ hgf hgf' hK₁ hK₂0 hK₂
      hg'c hg''c hunif hmgG hpgG hqgG
    have hSI : ∀ᵐ ω ∂P, ∀ (p : Fin n) (j : Fin d), ((T : ℝ) : WithTop ℝ) ≤ τ ω →
        LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hcoord j)
            (fun ω s => LevyStochCalc.coordDeriv (fderiv ℝ g) p (X s ω) * H p j ω s)
            (hmgG p j) (hpgG p j) (hqgG p j) T ω
          = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hcoord j)
            (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p j ω s)
            (hmg p j) (hpg p j) (hqg p j) T ω := by
      rw [MeasureTheory.ae_all_iff]
      intro p
      rw [MeasureTheory.ae_all_iff]
      intro j
      refine LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_le_408915f τ (W.W j) ℱ (hcoord j) hτ
        (hmgG p j) (hpgG p j) (hqgG p j) (hmg p j) (hpg p j) (hqg p j) (fun ω s hs hle => ?_) hT
      have hnorm : ‖X s ω‖ ≤ R :=
        LevyStochCalc.Probability.norm_le_of_le_exitTime_408915f (h.continuous_path ω) hs hle
      rw [hd1 p (X s ω) (lt_of_le_of_lt hnorm hR32)]
    filter_upwards [hform, hSI] with ω hω hSIω hlt
    have hball : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖X s ω‖ < R := by
      intro s hs
      by_contra hcon
      have hmem : ∃ u ∈ Set.Icc (0 : ℝ) T, R ≤ ‖X u ω‖ := ⟨s, hs, not_lt.mp hcon⟩
      have := (LevyStochCalc.Probability.exitTime_le_iff_408915f (X := fun ω t => X t ω)
        (h.continuous_path ω) R T).2 hmem
      exact absurd this (not_le.mpr hlt)
    have hballs : ∀ s ∈ Set.Ioc (0 : ℝ) T, ‖X s ω‖ < 3 * R / 2 := fun s hs =>
      lt_trans (hball s ⟨hs.1.le, hs.2⟩) hR32
    have hT' : ‖X T ω‖ < 3 * R / 2 :=
      lt_trans (hball T ⟨hT.le, le_rfl⟩) hR32
    have h0' : ‖X 0 ω‖ < 3 * R / 2 :=
      lt_trans (hball 0 ⟨le_rfl, hT.le⟩) hR32
    have hleτ : ((T : ℝ) : WithTop ℝ) ≤ τ ω := le_of_lt hlt
    have e1 : (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          LevyStochCalc.coordDeriv (fderiv ℝ g) p (X s ω) * bdrift p ω s ∂volume)
        = ∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s ∂volume := by
      refine Finset.sum_congr rfl fun p _ => ?_
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
      rw [hd1 p (X s ω) (hballs s hs)]
    have e2 : (∑ p : Fin n, ∑ j : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hcoord j)
            (fun ω s => LevyStochCalc.coordDeriv (fderiv ℝ g) p (X s ω) * H p j ω s)
            (hmgG p j) (hpgG p j) (hqgG p j) T ω)
        = ∑ p : Fin n, ∑ j : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hcoord j)
            (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p j ω s)
            (hmg p j) (hpg p j) (hqg p j) T ω :=
      Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun j _ => hSIω p j hleτ
    have e3 : (1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            LevyStochCalc.coordDeriv₂ (fderiv ℝ (fderiv ℝ g)) p q (X s ω)
              * ∑ j : Fin d, H p j ω s * H q j ω s ∂volume)
        = 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
              * ∑ j : Fin d, H p j ω s * H q j ω s ∂volume := by
      refine congrArg (fun x => 1 / 2 * x) ?_
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
      rw [hd2 p q (X s ω) (hballs s hs)]
    rw [← hd0 _ hT', ← hd0 _ h0', hω, e1, e2, e3]
  have hall : ∀ᵐ ω ∂P, ∀ m : ℕ, 0 < m →
      ((T : ℝ) : WithTop ℝ) < LevyStochCalc.Probability.exitTime (fun ω t => X t ω) (m : ℝ) ω →
        f (X T ω) - f (X 0 ω)
          = (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
            + (∑ p : Fin n, ∑ j : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hcoord j)
                (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p j ω s)
                (hmg p j) (hpg p j) (hqg p j) T ω)
            + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
                  * ∑ j : Fin d, H p j ω s * H q j ω s ∂volume := by
    rw [MeasureTheory.ae_all_iff]
    intro m
    by_cases hm : 0 < m
    · filter_upwards [hstep m hm] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun ω hcon => absurd hcon hm
  filter_upwards [hall] with ω hω
  obtain ⟨K, hK⟩ := LevyStochCalc.Probability.exists_lt_exitTime_408915f (X := fun ω t => X t ω)
    (h.continuous_path ω) hT.le
  exact hω (max K 1) (lt_of_lt_of_le Nat.zero_lt_one (le_max_right K 1))
    (hK (max K 1) (le_max_left K 1))
