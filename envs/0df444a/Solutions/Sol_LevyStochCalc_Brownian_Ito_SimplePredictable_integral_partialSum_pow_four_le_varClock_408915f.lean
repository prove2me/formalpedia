-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.SimplePredictable.integral_partialSum_pow_four_le_varClock_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:21:16.915171+00:00
-- url     : https://prove2.me/submissions/77cfc7c4-22ca-4843-9a56-6a9c4cd19af7

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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_integral_partialSum_pow_four_succ_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_integral_partialSum_sq_le_varClock_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_varClock_mono_408915f

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
theorem LevyStochCalc.Brownian.Ito.gaussianFourthMoment_nonneg : 0 ≤ gaussianFourthMoment :=
  integral_nonneg fun x => by positivity
section Increments
variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
/-- A Brownian increment has moments of every order. -/
theorem LevyStochCalc.Brownian.Ito.memLp_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (fun ω => W.W b ω - W.W a ω) p P := by
  have hmeas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  have h := (memLp_map_measure_iff (g := (id : ℝ → ℝ)) (μ := P)
    (f := fun ω => W.W b ω - W.W a ω) (p := p)
    (by fun_prop) hmeas.aemeasurable).1
  rw [W.increment_gaussian ha hab] at h
  exact h (memLp_id_gaussianReal' p hp)
/-- A bounded random variable times a Brownian increment has moments of every order. -/
theorem LevyStochCalc.Brownian.Ito.memLp_mul_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (p : ℝ≥0∞) (hp : p ≠ ⊤)
    {Y : Ω → ℝ} (hYm : Measurable Y) {C : ℝ} (hC : ∀ ω, |Y ω| ≤ C) :
    MemLp (fun ω => Y ω * (W.W b ω - W.W a ω)) p P := by
  have hmeas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  refine MemLp.mono ((memLp_increment W ha hab p hp).const_mul C)
    (hYm.mul hmeas).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  have hC0 : 0 ≤ C := (abs_nonneg (Y ω)).trans (hC ω)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hC0]
  exact mul_le_mul_of_nonneg_right (hC ω) (abs_nonneg _)
end Increments
section
namespace LevyStochCalc.Brownian.Ito.SimplePredictable
end LevyStochCalc.Brownian.Ito.SimplePredictable
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Ito.SimplePredictable
variable {T : ℝ} (G : SimplePredictable Ω T)
  {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.partialSum_zero (ω : Ω) : G.partialSum W 0 ω = 0 := by simp [partialSum]
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.measurable_term (i : ℕ) : Measurable (G.term W i) := by
  unfold term
  split_ifs with h
  · exact (G.ξ_measurable _).mul ((W.measurable_eval _).sub (W.measurable_eval _))
  · exact measurable_const
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.measurable_partialSum (k : ℕ) : Measurable (G.partialSum W k) :=
  Finset.measurable_sum _ fun i _ => G.measurable_term W i
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.memLp_term {C : ℝ} (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
    (p : ℝ≥0∞) (hp : p ≠ ⊤) (i : ℕ) : MemLp (G.term W i) p P := by
  by_cases h : i < G.N
  · have hterm : G.term W i = fun ω => G.ξ ⟨i, h⟩ ω
        * (W.W (G.partition (⟨i, h⟩ : Fin G.N).succ) ω
          - W.W (G.partition (⟨i, h⟩ : Fin G.N).castSucc) ω) := by
      funext ω; rw [term, dif_pos h]
    rw [hterm]
    exact memLp_mul_increment W (G.partition_nonneg _)
      (G.partition_strictMono Fin.castSucc_lt_succ) p hp (G.ξ_measurable _) (hC ⟨i, h⟩)
  · have hterm : G.term W i = fun _ => (0 : ℝ) := by funext ω; rw [term, dif_neg h]
    rw [hterm]; exact memLp_const 0
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.memLp_partialSum {C : ℝ} (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
    (p : ℝ≥0∞) (hp : p ≠ ⊤) (k : ℕ) : MemLp (G.partialSum W k) p P :=
  memLp_finsetSum _ fun i _ => G.memLp_term W hC p hp i
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.varClock_zero (c : Fin G.N → ℝ) : G.varClock c 0 = 0 := by simp [varClock]
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.varClock_succ (c : Fin G.N → ℝ) {k : ℕ} (hk : k < G.N) :
    G.varClock c (k + 1) = G.varClock c k
      + c ⟨k, hk⟩ ^ 2 * (G.partition (⟨k, hk⟩ : Fin G.N).succ
        - G.partition (⟨k, hk⟩ : Fin G.N).castSucc) := by
  unfold varClock
  rw [Finset.sum_range_succ, dif_pos hk]
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.varClock_nonneg (c : Fin G.N → ℝ) (k : ℕ) : 0 ≤ G.varClock c k := by
  unfold varClock
  refine Finset.sum_nonneg fun j _ => ?_
  by_cases h : j < G.N
  · rw [dif_pos h]
    exact mul_nonneg (sq_nonneg _)
      (sub_nonneg.mpr (G.partition_strictMono Fin.castSucc_lt_succ).le)
  · rw [dif_neg h]
end
end
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentPartialSums.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
section
namespace LevyStochCalc.Brownian.Ito.SimplePredictable
end LevyStochCalc.Brownian.Ito.SimplePredictable
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Ito.SimplePredictable
variable {T : ℝ} (G : SimplePredictable Ω T)
  {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
omit [IsProbabilityMeasure P] in
/-- A real random variable in `Lᵐ` has an integrable `m`-th power. -/
private theorem LevyStochCalc.Brownian.Ito.SimplePredictable.integrable_pow_of_memLp {f : Ω → ℝ} {m : ℕ} (hm : m ≠ 0)
    {p : ℝ≥0∞} (hp : p = (m : ℝ≥0∞)) (h : MemLp f p P) : Integrable (fun ω => f ω ^ m) P := by
  subst hp
  refine (h.integrable_norm_pow hm).mono ((continuous_pow m).comp_aestronglyMeasurable h.1)
    (Filter.Eventually.of_forall fun ω => ?_)
  simp
section Moments
variable (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
/-- A coefficient bounded by `c` has even moments at most the matching power of `c`. -/
private theorem LevyStochCalc.Brownian.Ito.SimplePredictable.integral_xi_even_le {c : ℝ} (i : Fin G.N)
    (hci : ∀ ω, |G.ξ i ω| ≤ c) (m : ℕ) :
    ∫ ω, (G.ξ i ω) ^ (2 * m) ∂P ≤ c ^ (2 * m) := by
  have hnn : ∀ ω, (0 : ℝ) ≤ (G.ξ i ω) ^ (2 * m) := fun ω => by
    rw [pow_mul]; positivity
  have hcnn : (0 : ℝ) ≤ c ^ (2 * m) := by rw [pow_mul]; positivity
  have hpow : ∀ ω, (G.ξ i ω) ^ (2 * m) ≤ c ^ (2 * m) := fun ω => by
    have h : |G.ξ i ω| ^ (2 * m) ≤ c ^ (2 * m) :=
      pow_le_pow_left₀ (abs_nonneg _) (hci ω) _
    rwa [← abs_pow, abs_of_nonneg (hnn ω)] at h
  have hint : Integrable (fun ω => (G.ξ i ω) ^ (2 * m)) P := by
    refine (integrable_const (c ^ (2 * m))).mono
      ((G.ξ_measurable _).pow_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hnn ω), abs_of_nonneg hcnn]
    exact hpow ω
  calc ∫ ω, (G.ξ i ω) ^ (2 * m) ∂P ≤ ∫ _ω : Ω, c ^ (2 * m) ∂P :=
        integral_mono hint (integrable_const _) hpow
    _ = c ^ (2 * m) := by simp
namespace LevyStochCalc.Brownian.Ito.SimplePredictable
end LevyStochCalc.Brownian.Ito.SimplePredictable
open LevyStochCalc.Brownian.Ito.SimplePredictable in
include hℱ h_adapt hC0 hC in
/-- Fourth moment of a partial sum against a per-tile coefficient bound: the elapsed
variance budget `∑_{j<k} c_j² (τ_{j+1} − τ_j)` replaces `C²τ_k`. -/
theorem solution {c : Fin G.N → ℝ}
    (hc : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ c i) :
    ∀ (k : ℕ) (_hk : k ≤ G.N),
      ∫ ω, (G.partialSum W k ω) ^ 4 ∂P
        ≤ 6 * (G.varClock c G.N * G.varClock c k)
          + LevyStochCalc.Brownian.Ito.gaussianFourthMoment * G.varClock c k ^ 2 := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : ∀ ω, G.partialSum W 0 ω = 0 := G.partialSum_zero W
    simp_rw [h0]
    simp [G.varClock_zero]
  | succ n ih =>
    intro hk
    have hn : n < G.N := hk
    have hΔ0 : (0 : ℝ) ≤ G.partition (⟨n, hn⟩ : Fin G.N).succ
        - G.partition (⟨n, hn⟩ : Fin G.N).castSucc :=
      sub_nonneg.mpr (G.partition_strictMono Fin.castSucc_lt_succ).le
    have hcn2 : (0 : ℝ) ≤ c ⟨n, hn⟩ ^ 2 := sq_nonneg _
    have hxi2 : ∀ ω, (G.ξ ⟨n, hn⟩ ω) ^ 2 ≤ c ⟨n, hn⟩ ^ 2 := fun ω => by
      have h := pow_le_pow_left₀ (abs_nonneg (G.ξ ⟨n, hn⟩ ω)) (hc ⟨n, hn⟩ ω) 2
      rwa [← abs_pow, abs_of_nonneg (sq_nonneg (G.ξ ⟨n, hn⟩ ω))] at h
    have hSint : Integrable (fun ω => (G.partialSum W n ω) ^ 2) P :=
      integrable_pow_of_memLp (m := 2) (by norm_num) (by simp)
        (G.memLp_partialSum W hC 2 (by simp) n)
    have hmix : Integrable
        (fun ω => (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2) P := by
      refine (hSint.const_mul (c ⟨n, hn⟩ ^ 2)).mono
        (((G.measurable_partialSum W n).pow_const 2).mul
          ((G.ξ_measurable _).pow_const 2)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow,
        abs_of_nonneg hcn2]
      have h4 : |G.ξ ⟨n, hn⟩ ω| ^ 2 ≤ c ⟨n, hn⟩ ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (hc ⟨n, hn⟩ ω) 2
      nlinarith [pow_nonneg (abs_nonneg (G.partialSum W n ω)) 2]
    have hmix_le : ∫ ω, (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2 ∂P
        ≤ c ⟨n, hn⟩ ^ 2 * ∫ ω, (G.partialSum W n ω) ^ 2 ∂P := by
      have hstep : ∫ ω, (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2 ∂P
          ≤ ∫ ω, c ⟨n, hn⟩ ^ 2 * (G.partialSum W n ω) ^ 2 ∂P :=
        integral_mono hmix (hSint.const_mul _) fun ω => by
          nlinarith [sq_nonneg (G.partialSum W n ω), hxi2 ω]
      rwa [integral_const_mul] at hstep
    have hS2 := G.integral_partialSum_sq_le_varClock_408915f W ℱ hℱ h_adapt hC0 hC hc n hn.le
    have hVN : G.varClock c n ≤ G.varClock c G.N := G.varClock_mono_408915f c hn.le
    have hV0 : (0 : ℝ) ≤ G.varClock c n := G.varClock_nonneg c n
    have hcg : (0 : ℝ) ≤ LevyStochCalc.Brownian.Ito.gaussianFourthMoment := LevyStochCalc.Brownian.Ito.gaussianFourthMoment_nonneg
    have hA : (∫ ω, (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2 ∂P)
        ≤ c ⟨n, hn⟩ ^ 2 * G.varClock c G.N :=
      hmix_le.trans (mul_le_mul_of_nonneg_left (hS2.trans hVN) hcn2)
    have hB : (∫ ω, (G.ξ ⟨n, hn⟩ ω) ^ 4 ∂P) ≤ c ⟨n, hn⟩ ^ 4 := by
      simpa using G.integral_xi_even_le (P := P) ⟨n, hn⟩ (hc ⟨n, hn⟩) 2
    rw [G.integral_partialSum_pow_four_succ_408915f W ℱ hℱ h_adapt hC0 hC hn, G.varClock_succ c hn]
    have h1 := ih hn.le
    nlinarith [mul_le_mul_of_nonneg_right hA hΔ0,
      mul_le_mul_of_nonneg_right hB
        (mul_nonneg (mul_nonneg hΔ0 hΔ0) hcg),
      mul_nonneg (mul_nonneg (mul_nonneg hcg hV0) hcn2) hΔ0]
