-- Prove2me | solution 1 for OAI.Problem356.SmoothBranchMarginal.exists_smooth_branch_marginal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:49:57.239841+00:00
-- url     : https://prove2.me/submissions/978bbfc5-bf9b-4b83-a7da-bf864d5426aa

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/SmoothBranchMarginal.lean:L163-L199
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.SmoothBranchMarginal.exists_smooth_branch_marginal. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryMap
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalBranchMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothPushforward
import Definitions.Def_OAI_Analysis_CoulombTransport_GluedCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_GoodTypePermutation
import Definitions.Def_OAI_Analysis_CoulombTransport_IsometryTransport
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothBranchMarginal
import Theorems.Thm_OAI_Problem356_SmoothBranchMarginal_transported_square_amplitude
import Theorems.Thm_OAI_Problem356_densityMeasure_sum_weighted_squares
import Theorems.Thm_OAI_Problem356_exists_normalized_smooth_square_in_ball
import Theorems.Thm_OAI_Problem356_isSmoothCompactProbabilityDensity_sum_normalized_disjoint_squares

-- ---- from OAI.Analysis.CoulombTransport.SmoothBranchMarginal ----
namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.SmoothBranchMarginal

theorem squareDensity_probability {g : E3 → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hmass : (∫ x : E3, g x ^ 2) = 1) :
    IsProbabilityMeasure (densityMeasure (fun x => g x ^ 2)) := by
  have hcompact : HasCompactSupport (fun x => g x ^ 2) := by
    simpa only [Function.comp_def] using
      hgc.comp_left (g := fun y : ℝ => y ^ 2) (by simp)
  have hint : Integrable (fun x => g x ^ 2) (volume : Measure E3) :=
    (hg.pow 2).integrable_of_hasCompactSupport hcompact
  refine ⟨?_⟩
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun x => sq_nonneg (g x))),
    hmass, ENNReal.ofReal_one]

theorem marginalDensity_smooth {B : Set E3}
    {e : Fin 4 → OpenPartialHomeomorph E3 E3}
    {g : E3 → ℝ} {q : Fin 4 → E3 → ℝ}
    (hg : NormalizedAmplitude g) (hq : ∀ i, NormalizedAmplitude (q i))
    (hgs : tsupport g ⊆ B) (hqs : ∀ i, tsupport (q i) ⊆ e i '' B)
    (hdisj : Pairwise (fun i j => Disjoint (componentRegion B e i) (componentRegion B e j))) :
    IsSmoothCompactProbabilityDensity (marginalDensity g q) := by
  apply isSmoothCompactProbabilityDensity_sum_normalized_disjoint_squares
    Finset.univ componentWeight (componentAmplitude g q)
  · intro i _
    cases i <;> norm_num [componentWeight]
  · intro i _
    cases i with
    | none => exact hg.1
    | some i => exact (hq i).1
  · intro i _
    cases i with
    | none => exact hg.2.1
    | some i => exact (hq i).2.1
  · intro i _
    cases i with
    | none => exact hg.2.2.1
    | some i => exact (hq i).2.2.1
  · have hsub : ∀ i, Function.support (componentAmplitude g q i) ⊆ componentRegion B e i := by
      intro i
      cases i with
      | none => exact (subset_tsupport g).trans hgs
      | some i => exact (subset_tsupport (q i)).trans (hqs i)
    intro i _ j _ hij
    exact (hdisj hij).mono (hsub i) (hsub j)
  · intro i _
    cases i with
    | none => exact hg.2.2.2
    | some i => exact (hq i).2.2.2
  · norm_num [componentWeight, Fintype.sum_option]

theorem marginalDensity_measure {g : E3 → ℝ} {q : Fin 4 → E3 → ℝ}
    (hg : Measurable g) (hq : ∀ i, Measurable (q i)) :
    densityMeasure (marginalDensity g q) =
      (1 / 3 : ℝ≥0∞) • densityMeasure (fun x => g x ^ 2) +
      ∑ i : Fin 4, (1 / 6 : ℝ≥0∞) • densityMeasure (fun x => q i x ^ 2) := by
  unfold marginalDensity
  rw [densityMeasure_sum_weighted_squares]
  · simp [Fintype.sum_option, componentWeight, componentAmplitude]
  · intro i _
    cases i <;> norm_num [componentWeight]
  · intro i _
    cases i with
    | none => exact hg
    | some i => exact hq i

/-- Construct the actual smooth five-component marginal from local branch
charts on a common ball. All square amplitudes and their exact pushforward
laws are supplied in the conclusion. -/
theorem exists_smooth_branch_marginal
    (c : E3) {r : ℝ} (hr : 0 < r)
    (e : Fin 4 → OpenPartialHomeomorph E3 E3)
    (hsource : ∀ i, Metric.ball c r ⊆ (e i).source)
    (hdisj : Pairwise (fun i j => Disjoint
      (componentRegion (Metric.ball c r) e i) (componentRegion (Metric.ball c r) e j)))
    (he : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i).symm (e i).target)
    (D : Fin 4 → E3 → E3 →L[ℝ] E3)
    (hD : ∀ i y, y ∈ (e i).target → HasFDerivAt (e i).symm (D i y) y)
    (hJ : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat)
      (fun y => Real.sqrt |(D i y).det|) (e i).target) :
    ∃ (g : E3 → ℝ) (q : Fin 4 → E3 → ℝ),
      NormalizedAmplitude g ∧ tsupport g ⊆ Metric.ball c r ∧
      (∀ i, NormalizedAmplitude (q i) ∧ tsupport (q i) ⊆ e i '' Metric.ball c r) ∧
      IsProbabilityMeasure (densityMeasure (fun x => g x ^ 2)) ∧
      IsSmoothCompactProbabilityDensity (marginalDensity g q) ∧
      densityMeasure (marginalDensity g q) =
        (1 / 3 : ℝ≥0∞) • densityMeasure (fun x => g x ^ 2) +
        ∑ i : Fin 4, (1 / 6 : ℝ≥0∞) •
          Measure.map (LocalBranchMeasure.extendedBranch (e i) 0)
            (densityMeasure (fun x => g x ^ 2)) := by
  obtain ⟨g, hg0, hg, hgc, hgs, hgm⟩ := exists_normalized_smooth_square_in_ball c hr
  have hqexists := fun i => transported_square_amplitude (e i) hg0 hg hgc
    (hgs.trans (hsource i)) hgm (he i) (D i) (hD i) (hJ i)
  choose q hq0 hq hqc hqs hqm hqmap using hqexists
  have hgn : NormalizedAmplitude g := ⟨hg0, hg, hgc, hgm⟩
  have hqn : ∀ i, NormalizedAmplitude (q i) := fun i => ⟨hq0 i, hq i, hqc i, hqm i⟩
  have hqsub : ∀ i, tsupport (q i) ⊆ e i '' Metric.ball c r := fun i =>
    (hqs i).trans (Set.image_mono hgs)
  refine ⟨g, q, hgn, hgs, fun i => ⟨hqn i, hqsub i⟩,
    squareDensity_probability hg.continuous hgc hgm,
    marginalDensity_smooth hgn hqn hgs hqsub hdisj, ?_⟩
  rw [marginalDensity_measure hg.continuous.measurable (fun i => (hq i).continuous.measurable)]
  simp_rw [hqmap]

end Problem356.SmoothBranchMarginal

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.SmoothBranchMarginal
open MeasureTheory Set
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.Problem356.SmoothBranchMarginal.exists_smooth_branch_marginal := @_root_.OAI.Problem356.SmoothBranchMarginal.exists_smooth_branch_marginal
