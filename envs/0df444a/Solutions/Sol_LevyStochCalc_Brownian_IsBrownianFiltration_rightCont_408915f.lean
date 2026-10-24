-- Prove2me | solution 1 for LevyStochCalc.Brownian.IsBrownianFiltration.rightCont_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:00:18.005117+00:00
-- url     : https://prove2.me/submissions/3c28425c-6188-453b-afac-ef59cf7cc9bb

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Martingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MartingaleCondExp
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.MeanInequalities
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
import Theorems.Thm_LevyStochCalc_Probability_indep_comap_of_tendsto_ae_408915f
import Theorems.Thm_LevyStochCalc_Probability_indep_iSup_of_finset_408915f

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/ComapTuple.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc LevyStochCalc.Probability
variable {Ω : Type*}
/-- The σ-algebra generated by a tuple is the supremum of those generated by its components. -/
theorem LevyStochCalc.Probability.comap_pi_eq_iSup {ι : Type*} {𝓨 : ι → Type*} [∀ i, MeasurableSpace (𝓨 i)]
    (f : ∀ i, Ω → 𝓨 i) :
    MeasurableSpace.comap (fun ω i => f i ω) MeasurableSpace.pi
      = ⨆ i, MeasurableSpace.comap (f i) inferInstance := by
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  exact iSup_congr fun i => MeasurableSpace.comap_comp
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/Filtered.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory Filter Topology
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Brownian
end LevyStochCalc.Brownian
open LevyStochCalc LevyStochCalc.Brownian
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
namespace LevyStochCalc.Brownian.IsBrownianFiltration
end LevyStochCalc.Brownian.IsBrownianFiltration
open LevyStochCalc.Brownian.IsBrownianFiltration in
/-- A Brownian motion for `ℱ` is one for the right-continuous filtration `ℱ₊`. -/
theorem solution {W : LevyStochCalc.Brownian.BrownianMotion P} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (h : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ) : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ.rightCont where
  measurable t := (h.measurable t).mono (ℱ.le_rightCont t) le_rfl
  indep_future := by
    classical
    intro s hs
    obtain ⟨r, hr_anti, hr_gt, hr_tend⟩ := exists_seq_strictAnti_tendsto s
    have hle : ∀ k, ℱ.rightCont s ≤ ℱ (r k) := fun k => by
      rw [Filtration.rightCont_eq_of_neBot_nhdsGT ℱ s]
      exact iInf₂_le (r k) (hr_gt k)
    have hfin : ∀ (n : ℕ) (u : Fin n → ℝ), (∀ i, s < u i) →
        Indep (ℱ.rightCont s)
          (⨆ i, MeasurableSpace.comap (fun ω => W.W (u i) ω - W.W s ω) inferInstance) P := by
      intro n u hu
      obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
        (Filter.eventually_all.2 fun i => hr_tend.eventually (eventually_lt_nhds (hu i)))
      have hq_lt : ∀ (k : ℕ) (i : Fin n), r (k + K) < u i := fun k i =>
        hK (k + K) (Nat.le_add_left K k) i
      have hq_tend : Tendsto (fun k => r (k + K)) atTop (𝓝 s) :=
        hr_tend.comp (tendsto_add_atTop_nat K)
      have hYcomap :
          MeasurableSpace.comap (fun ω (i : Fin n) => W.W (u i) ω - W.W s ω) inferInstance
            = ⨆ i, MeasurableSpace.comap (fun ω => W.W (u i) ω - W.W s ω) inferInstance :=
        LevyStochCalc.Probability.comap_pi_eq_iSup fun i ω => W.W (u i) ω - W.W s ω
      rw [← hYcomap]
      refine LevyStochCalc.Probability.indep_comap_of_tendsto_ae_408915f (ℱ.rightCont.le s)
        (X := fun k ω (i : Fin n) => W.W (u i) ω - W.W (r (k + K)) ω)
        (fun k => measurable_pi_lambda _ fun i =>
          (W.measurable_eval (u i)).sub (W.measurable_eval (r (k + K))))
        (measurable_pi_lambda _ fun i => (W.measurable_eval (u i)).sub (W.measurable_eval s))
        (fun k => ?_) ?_
      · have hkcomap : MeasurableSpace.comap
              (fun ω (i : Fin n) => W.W (u i) ω - W.W (r (k + K)) ω) inferInstance
            = ⨆ i, MeasurableSpace.comap
              (fun ω => W.W (u i) ω - W.W (r (k + K)) ω) inferInstance :=
          LevyStochCalc.Probability.comap_pi_eq_iSup fun i ω => W.W (u i) ω - W.W (r (k + K)) ω
        rw [hkcomap]
        refine indep_of_indep_of_le_left (indep_of_indep_of_le_right
          (h.indep_future (hs.trans (hr_gt (k + K)).le)) ?_) (hle (k + K))
        exact iSup_le fun i => le_iSup₂_of_le (u i) (Set.mem_Ioi.mpr (hq_lt k i)) le_rfl
      · filter_upwards [W.continuous_paths] with ω hω
        exact tendsto_pi_nhds.2 fun i => tendsto_const_nhds.sub ((hω.tendsto s).comp hq_tend)
    have hsup : (⨆ t ∈ Set.Ioi s,
          MeasurableSpace.comap (fun ω => W.W t ω - W.W s ω) inferInstance)
        = ⨆ t : Set.Ioi s,
            MeasurableSpace.comap (fun ω => W.W (t : ℝ) ω - W.W s ω) inferInstance :=
      le_antisymm
        (iSup₂_le fun t ht => le_iSup (fun t : Set.Ioi s =>
          MeasurableSpace.comap (fun ω => W.W (t : ℝ) ω - W.W s ω) inferInstance) ⟨t, ht⟩)
        (iSup_le fun t => le_iSup₂_of_le (t : ℝ) t.2 le_rfl)
    rw [hsup]
    refine (LevyStochCalc.Probability.indep_iSup_of_finset_408915f
      (m := fun t : Set.Ioi s =>
        MeasurableSpace.comap (fun ω => W.W (t : ℝ) ω - W.W s ω) inferInstance)
      (fun t => ((W.measurable_eval (t : ℝ)).sub (W.measurable_eval s)).comap_le)
      (ℱ.rightCont.le s) fun S => ?_).symm
    exact indep_of_indep_of_le_left
      (hfin S.card (fun i => ((S.equivFin.symm i).1 : ℝ))
        (fun i => (S.equivFin.symm i).1.2)).symm
      (iSup₂_le fun t ht => le_iSup_of_le (S.equivFin ⟨t, ht⟩) (by simp))
