-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.SimplePredictable.sum_xi_mul_simpleIntegral_sub_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:02:19.074386+00:00
-- url     : https://prove2.me/submissions/49ce5095-1386-44b4-8940-e23024e54121

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoAlgebraProduct
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityDyadicAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPointwise
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPredictableL2
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityShiftedAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityUnbounded
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

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraProduct.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
private lemma LevyStochCalc.Brownian.Ito.min_min_of_le {a b t : ℝ} (h : a ≤ b) : min a (min b t) = min a t := by
  rw [← min_assoc, min_eq_left h]
private lemma LevyStochCalc.Brownian.Ito.min_min_of_le' {a b t : ℝ} (h : a ≤ b) : min b (min a t) = min a t := by
  rw [← min_assoc, min_eq_right h]
namespace LevyStochCalc.Brownian.Ito.SimplePredictable
end LevyStochCalc.Brownian.Ito.SimplePredictable
open LevyStochCalc.Brownian.Ito.SimplePredictable in
/-- **The elementary integral against an elementary integral.** Summing the increments of
`simpleIntegral W K` against the coefficients of `G` gives the elementary integral of the
product `G · K` on the common refinement. -/
theorem solution
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (G K : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T)
    (h_eq : G.partition (Fin.last G.N) = K.partition (Fin.last K.N))
    (t : ℝ) (ω : Ω) :
    (∑ i : Fin G.N, G.ξ i ω *
        (LevyStochCalc.Brownian.Ito.simpleIntegral W K (min (G.partition i.succ) t) ω
          - LevyStochCalc.Brownian.Ito.simpleIntegral W K (min (G.partition i.castSucc) t) ω))
      = LevyStochCalc.Brownian.Ito.simpleIntegral W (G.mul_on_common K h_eq) t ω := by
  classical
  set π : Fin (G.mergedM K + 1) → ℝ := G.mergedπ K with hπ
  set L : Fin (G.mergedM K) → Fin G.N := G.mergedIdxMap_left K h_eq with hL
  set R : Fin (G.mergedM K) → Fin K.N := G.mergedIdxMap_right K h_eq with hR
  have hmono : StrictMono π := G.mergedπ_strictMono K
  have hLle : ∀ j, G.partition (L j).castSucc ≤ π j.castSucc :=
    G.mergedIdxMap_left_idx_le K h_eq
  have hLge : ∀ j, π j.succ ≤ G.partition (L j).succ := G.mergedIdxMap_left_idx_ge K h_eq
  -- `K`'s elementary integral, read on the merged partition
  have hK : ∀ u : ℝ, LevyStochCalc.Brownian.Ito.simpleIntegral W K u ω
      = ∑ j : Fin (G.mergedM K), K.ξ (R j) ω
        * (W.W (min (π j.succ) u) ω - W.W (min (π j.castSucc) u) ω) := by
    intro u
    rw [← K.simpleIntegral_refine_intermediate W (G.mergedM K) π (G.mergedπ_zero K)
      (h_eq ▸ G.mergedπ_last K h_eq) hmono R (G.mergedIdxMap_right_idx_le K h_eq)
      (G.mergedIdxMap_right_idx_ge K h_eq) (G.mergedπ_refines_right K) u ω]
    rfl
  set ΔW : Fin (G.mergedM K) → ℝ := fun j =>
    W.W (min (π j.succ) t) ω - W.W (min (π j.castSucc) t) ω with hΔW
  set D : Fin G.N → Fin (G.mergedM K) → ℝ := fun i j =>
    (W.W (min (π j.succ) (min (G.partition i.succ) t)) ω
        - W.W (min (π j.castSucc) (min (G.partition i.succ) t)) ω)
      - (W.W (min (π j.succ) (min (G.partition i.castSucc) t)) ω
        - W.W (min (π j.castSucc) (min (G.partition i.castSucc) t)) ω) with hD
  have hDself : ∀ j, D (L j) j = ΔW j := by
    intro j
    have h1 : π j.castSucc ≤ π j.succ := (hmono Fin.castSucc_lt_succ).le
    have h2 : G.partition (L j).castSucc ≤ π j.castSucc := hLle j
    rw [hD, hΔW]
    simp only
    rw [min_min_of_le (hLge j), min_min_of_le (h1.trans (hLge j)),
      min_min_of_le' (h2.trans h1), min_min_of_le' h2]
    ring
  have hDzero : ∀ (j : Fin (G.mergedM K)) (i : Fin G.N), i ≠ L j → D i j = 0 := by
    intro j i hne
    have h1 : π j.castSucc ≤ π j.succ := (hmono Fin.castSucc_lt_succ).le
    have hGi : G.partition i.castSucc ≤ G.partition i.succ :=
      G.partition_strictMono.monotone Fin.castSucc_lt_succ.le
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle : (i.succ : Fin (G.N + 1)) ≤ (L j).castSucc := by
        rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hlt
      have hstep : G.partition i.succ ≤ π j.castSucc :=
        (G.partition_strictMono.monotone hle).trans (hLle j)
      rw [hD]
      simp only
      rw [min_min_of_le' hstep, min_min_of_le' (hstep.trans h1),
        min_min_of_le' (hGi.trans hstep), min_min_of_le' ((hGi.trans hstep).trans h1)]
      ring
    · have hle : ((L j).succ : Fin (G.N + 1)) ≤ i.castSucc := by
        rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hgt
      have hstep : π j.succ ≤ G.partition i.castSucc :=
        (hLge j).trans (G.partition_strictMono.monotone hle)
      rw [hD]
      simp only
      rw [min_min_of_le (hstep.trans hGi), min_min_of_le (h1.trans (hstep.trans hGi)),
        min_min_of_le hstep, min_min_of_le (h1.trans hstep)]
      ring
  calc (∑ i : Fin G.N, G.ξ i ω *
          (LevyStochCalc.Brownian.Ito.simpleIntegral W K (min (G.partition i.succ) t) ω
            - LevyStochCalc.Brownian.Ito.simpleIntegral W K (min (G.partition i.castSucc) t) ω))
      = ∑ i : Fin G.N, ∑ j : Fin (G.mergedM K), G.ξ i ω * (K.ξ (R j) ω * D i j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hK, hK, ← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hD]; ring
    _ = ∑ j : Fin (G.mergedM K), ∑ i : Fin G.N, G.ξ i ω * (K.ξ (R j) ω * D i j) :=
        Finset.sum_comm
    _ = ∑ j : Fin (G.mergedM K), G.ξ (L j) ω * K.ξ (R j) ω * ΔW j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_eq_single (L j)
          (fun i _ hne => by rw [hDzero j i hne, mul_zero, mul_zero])
          (fun hnm => absurd (Finset.mem_univ _) hnm), hDself j]
        ring
    _ = LevyStochCalc.Brownian.Ito.simpleIntegral W (G.mul_on_common K h_eq) t ω := by
        unfold LevyStochCalc.Brownian.Ito.simpleIntegral
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hΔW]
        rfl
