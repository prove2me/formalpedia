-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_sq_frozen_sub_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:29:56.108991+00:00
-- url     : https://prove2.me/submissions/adb8475b-524b-463c-860e-cc0e2e2baa64

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_VectorItoProcessVersion
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
import Mathlib.Analysis.Calculus.MeanValue
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
import Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_lintegral_window_sq_norm_sub_le_408915f
import Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_unifGrid_cell_408915f

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraSimpleIntegrand.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
/-- A simple integrand is jointly measurable in the form the integral consumes. -/
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.measurable_uncurry_eval {T : ℝ} (G : SimplePredictable Ω T) :
    Measurable (Function.uncurry fun ω s => G.eval s ω) := G.eval_jointly_measurable
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoIncrementMomentRestrict.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
/-- At most one cell of a strictly monotone partition contains a given time. -/
theorem LevyStochCalc.Brownian.Ito.partition_cell_unique {M : ℕ} {π : Fin (M + 1) → ℝ} (hπ : StrictMono π)
    {s : ℝ} {i j : Fin M} (hi : π i.castSucc < s ∧ s ≤ π i.succ)
    (hj : π j.castSucc < s ∧ s ≤ π j.succ) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : (i.succ : Fin (M + 1)) ≤ j.castSucc := by
      rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hlt
    exact absurd (hi.2.trans (hπ.monotone hle)) (not_le.mpr hj.1)
  · have hle : (j.succ : Fin (M + 1)) ≤ i.castSucc := by
      rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hgt
    exact absurd (hj.2.trans (hπ.monotone hle)) (not_le.mpr hi.1)
/-- A simple integrand evaluates to a tile's coefficient at every time in that tile. -/
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.eval_of_mem_Ioc {T : ℝ} (H : SimplePredictable Ω T) (j : Fin H.N)
    {s : ℝ} (hs : H.partition j.castSucc < s ∧ s ≤ H.partition j.succ) (ω : Ω) :
    H.eval s ω = H.ξ j ω := by
  classical
  unfold SimplePredictable.eval
  rw [Finset.sum_eq_single j
    (fun i _ hij => if_neg fun hc => hij (partition_cell_unique H.partition_strictMono hc hs))
    (fun hnm => absurd (Finset.mem_univ _) hnm)]
  exact if_pos hs
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFormulaGrid.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
theorem LevyStochCalc.Brownian.Ito.unifGrid_nonneg {T : ℝ} (hT : 0 ≤ T) (m i : ℕ) : 0 ≤ unifGrid T m i := by
  rw [unifGrid]
  positivity
theorem LevyStochCalc.Brownian.Ito.unifGrid_le {T : ℝ} (hT : 0 ≤ T) {m i : ℕ} (hi : i ≤ m) (hm : m ≠ 0) :
    unifGrid T m i ≤ T := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  rw [unifGrid, div_le_iff₀ hm']
  have : (i : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hi
  nlinarith
/-- The grid integrand evaluates to the cell coefficient on each cell. -/
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid_eval {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i)) (i : Fin m) {s : ℝ}
    (hs : unifGrid T m (i : ℕ) < s ∧ s ≤ unifGrid T m ((i : ℕ) + 1)) (ω : Ω) :
    (SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).eval s ω = ξ i ω :=
  (SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).eval_of_mem_Ioc i hs ω
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoGridPartition.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
/-- The cells of the uniform grid cover `(0, T]`. -/
theorem LevyStochCalc.Brownian.Ito.unifGrid_iUnion_Ioc {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    (⋃ i ∈ Finset.range m, Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)))
      = Set.Ioc (0 : ℝ) T := by
  ext s
  simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_Ioc, exists_prop]
  constructor
  · rintro ⟨i, hi, hlo, hhi⟩
    refine ⟨lt_of_le_of_lt (by simpa using unifGrid_nonneg hT.le m i) hlo, ?_⟩
    exact hhi.trans (unifGrid_le hT.le (by omega) hm0)
  · rintro ⟨hs0, hsT⟩
    obtain ⟨i, hi, hlo, hhi⟩ := exists_unifGrid_cell_408915f hT hm0 hs0 hsT
    exact ⟨i, hi, hlo, hhi⟩
/-- The cells of the uniform grid are pairwise disjoint. -/
theorem LevyStochCalc.Brownian.Ito.unifGrid_pairwiseDisjoint {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    (Finset.range m : Set ℕ).PairwiseDisjoint
      fun i => Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)) := by
  have hmono : StrictMono (unifGrid T m) :=
    strictMono_nat_of_lt_succ fun i => unifGrid_lt_succ hT hm0 i
  intro i _ j _ hij
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · refine Set.disjoint_left.mpr fun s hs hs' => ?_
    exact absurd (hs.2.trans_lt (lt_of_le_of_lt (hmono.monotone hlt) hs'.1)) (lt_irrefl _)
  · refine Set.disjoint_left.mpr fun s hs hs' => ?_
    exact absurd (hs'.2.trans_lt (lt_of_le_of_lt (hmono.monotone hlt) hs.1)) (lt_irrefl _)
/-- A lower integral over `[0, T]` is the sum of the lower integrals over the grid cells. -/
theorem LevyStochCalc.Brownian.Ito.lintegral_Icc_eq_sum_unifGrid {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0)
    (f : ℝ → ℝ≥0∞) :
    ∫⁻ s in Set.Icc (0 : ℝ) T, f s ∂volume
      = ∑ i ∈ Finset.range m,
          ∫⁻ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), f s ∂volume := by
  rw [← MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc,
    ← unifGrid_iUnion_Ioc hT hm0,
    MeasureTheory.lintegral_biUnion_finset (unifGrid_pairwiseDisjoint hT hm0)
      (fun i _ => measurableSet_Ioc) f]
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoMartingaleRiemann.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
/-- The square of a real number's extended norm is the extended value of its square. -/
theorem LevyStochCalc.Brownian.Ito.sq_enn_nnnorm_eq_ofReal_sq (x : ℝ) :
    ((‖x‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (x ^ 2) := by
  have h1 : (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal |x| := by
    rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg _)]
    exact congrArg _ (NNReal.eq (by simp [Real.norm_eq_abs]))
  rw [h1, ← ENNReal.ofReal_pow (abs_nonneg _), ← abs_pow,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 2)]
end
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoMartingaleRiemann.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
section VectorFrozen
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
/-- **The frozen step weight is `L²`-close to the weight itself.** For an `L`-Lipschitz `φ` on the
state space, the step process taking the value `φ(X_{tᵢ})` on cell `i` differs from `φ(X_s)` by
`L²·T·n(2B²(T/m)² + 2d²C²(T/m))` in `L²(P ⊗ ds)`. -/
theorem solution
    (h : LevyStochCalc.Brownian.Ito.IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
    {φ : (Fin n → ℝ) → ℝ} {L : ℝ} (hL0 : 0 ≤ L)
    (hφlip : ∀ x y : Fin n → ℝ, |φ x - φ y| ≤ L * ‖x - y‖)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i))
    (hξ : ∀ (i : Fin m) (ω : Ω), ξ i ω = φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)) ω)) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
          - φ (X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal (L ^ 2)
        * ENNReal.ofReal (T * ((n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
          + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ))))))) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hTm0 : (0 : ℝ) ≤ T / (m : ℝ) := (div_pos hT hm').le
  have hφc : Continuous φ := by
    have hlip : LipschitzWith (Real.toNNReal L) φ := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal L hL0]
      exact hφlip x y
    exact hlip.continuous
  have hsub : Measurable (Function.uncurry fun ω s =>
      (LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω - φ (X s ω)) :=
    (LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).measurable_uncurry_eval.sub
      (h.measurable_uncurry_comp hφc.measurable)
  have hjoint : Measurable (Function.uncurry fun ω s =>
      (‖(LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
        - φ (X s ω)‖₊ : ℝ≥0∞) ^ 2) :=
    (hsub.nnnorm.coe_nnreal_ennreal).pow_const 2
  have hmeasCell : ∀ i : ℕ, Measurable fun ω : Ω =>
      ∫⁻ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
        (‖(LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
          - φ (X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume := fun i =>
    hjoint.lintegral_prod_right'
  rw [lintegral_congr fun ω => LevyStochCalc.Brownian.Ito.lintegral_Icc_eq_sum_unifGrid hT hm0
    (fun s => (‖(LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
      - φ (X s ω)‖₊ : ℝ≥0∞) ^ 2)]
  rw [MeasureTheory.lintegral_finsetSum _ fun i _ => hmeasCell i]
  have hcell : ∀ i ∈ Finset.range m,
      ∫⁻ ω, ∫⁻ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
          (‖(LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
            - φ (X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal (L ^ 2)
        * ENNReal.ofReal ((T / (m : ℝ)) * ((n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
          + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ))))))) := by
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    have hfrozen : ∀ (ω : Ω), ∀ s ∈ Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
        (‖(LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
          - φ (X s ω)‖₊ : ℝ≥0∞) ^ 2
        ≤ ENNReal.ofReal (L ^ 2)
          * ENNReal.ofReal (‖X s ω - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 2) := by
      intro ω s hs
      have heval : (LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
          = φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) := by
        have := LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid_eval hT hm0 ξ hbdd hmeas ⟨i, him⟩ ⟨hs.1, hs.2⟩ ω
        rw [this, hξ ⟨i, him⟩ ω]
      rw [heval, LevyStochCalc.Brownian.Ito.sq_enn_nnnorm_eq_ofReal_sq, ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hlip := hφlip (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) (X s ω)
      have hnrm : ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖ = ‖X s ω - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ :=
        norm_sub_rev _ _
      rw [hnrm] at hlip
      calc (φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) - φ (X s ω)) ^ 2
          = |φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) - φ (X s ω)| ^ 2 := (sq_abs _).symm
        _ ≤ (L * ‖X s ω - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hlip 2
        _ = L ^ 2 * ‖X s ω - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 2 := by rw [mul_pow]
    calc ∫⁻ ω, ∫⁻ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
          (‖(LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω
            - φ (X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        ≤ ∫⁻ ω, ∫⁻ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
            ENNReal.ofReal (L ^ 2)
              * ENNReal.ofReal (‖X s ω - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 2) ∂volume ∂P :=
          lintegral_mono fun ω =>
            MeasureTheory.setLIntegral_mono' measurableSet_Ioc (hfrozen ω)
      _ = ENNReal.ofReal (L ^ 2) * ∫⁻ ω,
            ∫⁻ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
              ENNReal.ofReal (‖X s ω - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 2) ∂volume ∂P := by
          have hne : ENNReal.ofReal (L ^ 2) ≠ ⊤ := by simp
          rw [← MeasureTheory.lintegral_const_mul' _ _ hne]
          exact lintegral_congr fun ω => MeasureTheory.lintegral_const_mul' _ _ hne
      _ ≤ ENNReal.ofReal (L ^ 2)
            * ENNReal.ofReal ((T / (m : ℝ)) * ((n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
              + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ))))))) := by
          gcongr
          have := h.lintegral_window_sq_norm_sub_le_408915f hC0 hCH hbm hB0 hB
            (LevyStochCalc.Brownian.Ito.unifGrid_nonneg hT.le m i) (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 i).le
          rwa [LevyStochCalc.Brownian.Ito.unifGrid_succ_sub hm0 i] at this
  refine (Finset.sum_le_sum hcell).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, mul_comm ((m : ℝ≥0∞))]
  rw [mul_assoc]
  gcongr _ * ?_
  have hWnn : (0 : ℝ) ≤ (n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
      + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ))))) := by positivity
  rw [show ((m : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((m : ℝ)) from (ENNReal.ofReal_natCast m).symm,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
  refine le_of_eq (congrArg ENNReal.ofReal ?_)
  field_simp
