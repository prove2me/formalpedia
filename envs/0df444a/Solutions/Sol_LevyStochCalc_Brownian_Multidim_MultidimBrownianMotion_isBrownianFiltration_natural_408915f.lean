-- Prove2me | solution 1 for LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.isBrownianFiltration_natural_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:05:20.948845+00:00
-- url     : https://prove2.me/submissions/d9994335-33fd-464d-9c50-8d68e33a70c6

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
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Multidim
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MultidimFiltered
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
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
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_indep_naturalFiltration_future_408915f
import Theorems.Thm_LevyStochCalc_Probability_indep_sup_left_of_indep_408915f

section
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
/-- A Brownian motion is a Brownian motion for its natural filtration. -/
theorem LevyStochCalc.Brownian.isBrownianFiltration_natural (W : BrownianMotion P) :
    IsBrownianFiltration W (Martingale.naturalFiltration W) where
  measurable t := by
    refine Measurable.of_comap_le ?_
    change MeasurableSpace.comap (W.W t) inferInstance
      ≤ ⨆ j ≤ t, MeasurableSpace.comap (W.W j) inferInstance
    exact le_iSup₂_of_le t le_rfl le_rfl
  indep_future _ hs := W.indep_naturalFiltration_future_408915f hs
section
namespace LevyStochCalc.Brownian.IsBrownianFiltration
end LevyStochCalc.Brownian.IsBrownianFiltration
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.IsBrownianFiltration
variable {W : BrownianMotion P} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
/-- If `W` is a Brownian motion for `ℱ`, it is one for every filtration `𝒢` to which it is adapted
and with `𝒢 s ≤ ℱ s ⊔ m s` for σ-algebras `m s` independent of the join of `ℱ s` with the
σ-algebra generated by the increments of `W` after `s`. -/
theorem LevyStochCalc.Brownian.IsBrownianFiltration.of_le_sup (h : IsBrownianFiltration W ℱ) {𝒢 : Filtration ℝ ‹MeasurableSpace Ω›}
    (hadapted : ∀ t, Measurable[𝒢 t] (W.W t)) {m : ℝ → MeasurableSpace Ω}
    (hm : ∀ s, m s ≤ ‹MeasurableSpace Ω›) (hle : ∀ s, 𝒢 s ≤ ℱ s ⊔ m s)
    (hind : ∀ ⦃s : ℝ⦄, 0 ≤ s → Indep (m s) (ℱ s ⊔ ⨆ t ∈ Set.Ioi s,
      MeasurableSpace.comap (fun ω => W.W t ω - W.W s ω) inferInstance) P) :
    IsBrownianFiltration W 𝒢 where
  measurable := hadapted
  indep_future s hs := indep_of_indep_of_le_left
    (Probability.indep_sup_left_of_indep_408915f (ℱ.le s) (hm s)
      (iSup₂_le fun t _ => ((W.measurable_eval t).sub (W.measurable_eval s)).comap_le)
      (h.indep_future hs) (hind hs))
    (hle s)
end
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/MultidimFiltered.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
lemma MeasureTheory.Filtration.iSup_apply' {Ω ι : Type*} {m : MeasurableSpace Ω}
    (f : ι → Filtration ℝ m) (s : ℝ) : (⨆ i, f i) s = ⨆ i, f i s := by
  change sSup (Set.range f) s = _
  rw [Filtration.sSup_def, sSup_image, iSup_range]
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Brownian
end LevyStochCalc.Brownian
open LevyStochCalc LevyStochCalc.Brownian
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
lemma LevyStochCalc.Brownian.sigmaBrownian_le (W : BrownianMotion P) : sigmaBrownian W ≤ ‹MeasurableSpace Ω› :=
  iSup_le fun t => (W.measurable_eval t).comap_le
lemma LevyStochCalc.Brownian.naturalFiltration_le_sigmaBrownian (W : BrownianMotion P) (s : ℝ) :
    Martingale.naturalFiltration W s ≤ sigmaBrownian W :=
  iSup₂_le fun t _ => le_iSup (fun t => MeasurableSpace.comap (W.W t) inferInstance) t
lemma LevyStochCalc.Brownian.comap_increment_le_sigmaBrownian (W : BrownianMotion P) (s t : ℝ) :
    MeasurableSpace.comap (fun ω => W.W t ω - W.W s ω) inferInstance ≤ sigmaBrownian W := by
  have ht : Measurable[sigmaBrownian W] (W.W t) :=
    Measurable.of_comap_le (le_iSup (fun t => MeasurableSpace.comap (W.W t) inferInstance) t)
  have hs : Measurable[sigmaBrownian W] (W.W s) :=
    Measurable.of_comap_le (le_iSup (fun t => MeasurableSpace.comap (W.W t) inferInstance) s)
  exact (ht.sub hs).comap_le
/-- `σ(W)` is the σ-algebra generated by the path `ω ↦ (t ↦ W t ω)`. -/
lemma LevyStochCalc.Brownian.sigmaBrownian_eq_comap_path (W : BrownianMotion P) :
    sigmaBrownian W = MeasurableSpace.comap (fun ω t => W.W t ω) MeasurableSpace.pi := by
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  unfold sigmaBrownian
  congr
  funext t
  rw [MeasurableSpace.comap_comp]
  rfl
/-- The coordinates of a multidimensional Brownian motion generate independent σ-algebras. -/
lemma LevyStochCalc.Brownian.iIndep_sigmaBrownian (W : Multidim.MultidimBrownianMotion P d) :
    iIndep (fun i => sigmaBrownian (W.W i)) P := by
  have h := W.components_independent
  rw [iIndepFun_iff_iIndep] at h
  convert h using 1
  funext i
  exact sigmaBrownian_eq_comap_path (W.W i)
/-- The σ-algebra of the other coordinates is independent of `σ(Wʲ)`. -/
lemma LevyStochCalc.Brownian.indep_iSup_sigmaBrownian_ne (W : Multidim.MultidimBrownianMotion P d) (j : Fin d) :
    Indep (⨆ i ∈ {i : Fin d | i ≠ j}, sigmaBrownian (W.W i)) (sigmaBrownian (W.W j)) P := by
  have h := indep_iSup_of_disjoint (fun i => sigmaBrownian_le (W.W i)) (iIndep_sigmaBrownian W)
    (S := {i : Fin d | i ≠ j}) (T := {j}) (by simp [Set.disjoint_left])
  simpa using h
section
namespace LevyStochCalc.Brownian.Multidim
end LevyStochCalc.Brownian.Multidim
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
section
namespace LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
end LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.naturalFiltration_apply (W : MultidimBrownianMotion P d) (s : ℝ) :
    W.naturalFiltration s = ⨆ i, Martingale.naturalFiltration (W.W i) s :=
  Filtration.iSup_apply' _ s
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.naturalFiltration_coord_le (W : MultidimBrownianMotion P d) (j : Fin d) (s : ℝ) :
    Martingale.naturalFiltration (W.W j) s ≤ W.naturalFiltration s := by
  rw [naturalFiltration_apply]
  exact le_iSup (fun i => Martingale.naturalFiltration (W.W i) s) j
namespace LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
end LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
open LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion in
/-- Every coordinate of `W` is a Brownian motion for the joint natural filtration. -/
theorem solution (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d) (j : Fin d) :
    LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) W.naturalFiltration := by
  refine (LevyStochCalc.Brownian.isBrownianFiltration_natural (W.W j)).of_le_sup
    (fun t => ((LevyStochCalc.Brownian.isBrownianFiltration_natural (W.W j)).measurable t).mono
      (W.naturalFiltration_coord_le j t) le_rfl)
    (m := fun s => ⨆ i ∈ {i : Fin d | i ≠ j}, LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W i) s)
    (fun s => iSup₂_le fun i _ => (LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W i)).le s) ?_ ?_
  · intro s
    rw [LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.naturalFiltration_apply]
    refine iSup_le fun i => ?_
    by_cases hij : i = j
    · subst hij
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂ (f := fun i (_ : i ∈ {i : Fin d | i ≠ j}) =>
        LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W i) s) i hij)
  · intro s _
    refine indep_of_indep_of_le_right
      (indep_of_indep_of_le_left (LevyStochCalc.Brownian.indep_iSup_sigmaBrownian_ne W j) ?_) ?_
    · exact iSup₂_le fun i hi => le_iSup₂_of_le i hi (LevyStochCalc.Brownian.naturalFiltration_le_sigmaBrownian _ s)
    · exact sup_le (LevyStochCalc.Brownian.naturalFiltration_le_sigmaBrownian _ s)
        (iSup₂_le fun t _ => LevyStochCalc.Brownian.comap_increment_le_sigmaBrownian (W.W j) s t)
