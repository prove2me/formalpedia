-- Prove2me | solution 2 for OAI.Problem356.SmoothBranchMarginal.transported_square_amplitude
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:48:07.627732+00:00
-- url     : https://prove2.me/submissions/1dda4a38-3ffa-4a2b-987f-f14d589e398d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/SmoothBranchMarginal.lean:L49-L87
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.SmoothBranchMarginal.transported_square_amplitude. The node keeps its source
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
import Theorems.Thm_OAI_Problem356_map_squareDensity_localHomeomorph

-- ---- from OAI.Analysis.CoulombTransport.LocalBranchMeasure ----
namespace OAI

universe uAlpha uBeta

noncomputable section

open MeasureTheory Set

namespace Problem356
namespace LocalBranchMeasure

variable {α : Type uAlpha} {β : Type uBeta} [TopologicalSpace α] [TopologicalSpace β]
  [MeasurableSpace α] [MeasurableSpace β] [BorelSpace α] [BorelSpace β]

/-- The extension is Borel measurable even if the local map is arbitrary outside its source. -/
theorem measurable_extendedBranch (e : OpenPartialHomeomorph α β) (z : β) :
    Measurable (extendedBranch e z) := by
  classical
  exact e.continuousOn.measurable_piecewise continuous_const.continuousOn
    e.open_source.measurableSet

omit [BorelSpace α] [BorelSpace β] in
/-- Extending outside the source does not change pushforwards of measures concentrated there. -/
theorem map_extendedBranch (e : OpenPartialHomeomorph α β) (z : β)
    (ν : Measure α) (hν : ∀ᵐ x ∂ν, x ∈ e.source) :
    Measure.map (extendedBranch e z) ν = Measure.map e ν := by
  apply Measure.map_congr
  filter_upwards [hν] with x hx
  exact extendedBranch_apply_of_mem e z hx

end LocalBranchMeasure
end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.SmoothPushforward ----
namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Problem356

/-- A smooth function on an open set extends smoothly by zero whenever its
closed support stays in that open set.  The function is already defined
on the ambient space; the support hypothesis expresses the extension. -/
theorem contDiff_of_contDiffOn_of_tsupport_subset
    {f : E3 → ℝ} {s : Set E3} {n : WithTop ENat}
    (hs : IsOpen s) (hf : ContDiffOn ℝ n f s) (hfs : tsupport f ⊆ s) :
    ContDiff ℝ n f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ s
  · exact hf.contDiffAt (hs.mem_nhds hx)
  · have hxt : x ∉ tsupport f := fun ht => hx (hfs ht)
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hxt] with y hy
    exact image_eq_zero_of_notMem_tsupport hy

theorem localTransportAmplitude_nonneg
    (e : OpenPartialHomeomorph E3 E3) {g J : E3 → ℝ}
    (hg : ∀ x, 0 ≤ g x) (hJ : ∀ y ∈ e.target, 0 ≤ J y) :
    ∀ y, 0 ≤ localTransportAmplitude e g J y := by
  intro y
  by_cases hy : y ∈ e.target
  · simp only [localTransportAmplitude, indicator_of_mem hy]
    exact mul_nonneg (hg _) (hJ _ hy)
  · simp [localTransportAmplitude, hy]

theorem support_localTransportAmplitude_subset
    (e : OpenPartialHomeomorph E3 E3) (g J : E3 → ℝ) :
    Function.support (localTransportAmplitude e g J) ⊆ e '' tsupport g := by
  intro y hy
  have hyt : y ∈ e.target := by
    by_contra hn
    exact hy (by simp [localTransportAmplitude, hn])
  refine ⟨e.symm y, ?_, e.right_inv hyt⟩
  apply subset_tsupport g
  intro hz
  apply hy
  simp [localTransportAmplitude, hyt, hz]

theorem tsupport_localTransportAmplitude_subset
    (e : OpenPartialHomeomorph E3 E3) {g : E3 → ℝ} (J : E3 → ℝ)
    (hg : HasCompactSupport g) (hgs : tsupport g ⊆ e.source) :
    tsupport (localTransportAmplitude e g J) ⊆ e '' tsupport g := by
  apply closure_minimal (support_localTransportAmplitude_subset e g J)
  exact (hg.image_of_continuousOn (e.continuousOn.mono hgs)).isClosed

theorem hasCompactSupport_localTransportAmplitude
    (e : OpenPartialHomeomorph E3 E3) {g : E3 → ℝ} (J : E3 → ℝ)
    (hg : HasCompactSupport g) (hgs : tsupport g ⊆ e.source) :
    HasCompactSupport (localTransportAmplitude e g J) := by
  exact (hg.image_of_continuousOn (e.continuousOn.mono hgs)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_localTransportAmplitude_subset e J hg hgs)

theorem tsupport_localTransportAmplitude_subset_target
    (e : OpenPartialHomeomorph E3 E3) {g : E3 → ℝ} (J : E3 → ℝ)
    (hg : HasCompactSupport g) (hgs : tsupport g ⊆ e.source) :
    tsupport (localTransportAmplitude e g J) ⊆ e.target := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := tsupport_localTransportAmplitude_subset e J hg hgs hy
  exact e.map_source (hgs hx)

theorem contDiff_localTransportAmplitude
    (e : OpenPartialHomeomorph E3 E3) {g J : E3 → ℝ} {n : WithTop ENat}
    (hg : ContDiff ℝ n g) (hgc : HasCompactSupport g)
    (hgs : tsupport g ⊆ e.source)
    (he : ContDiffOn ℝ n e.symm e.target)
    (hJ : ContDiffOn ℝ n J e.target) :
    ContDiff ℝ n (localTransportAmplitude e g J) := by
  apply contDiff_of_contDiffOn_of_tsupport_subset e.open_target
    _ (tsupport_localTransportAmplitude_subset_target e J hgc hgs)
  have hcomp : ContDiffOn ℝ n (fun y => g (e.symm y) * J y) e.target :=
    (hg.comp_contDiffOn he).mul hJ
  refine hcomp.congr ?_
  intro y hy
  simp [localTransportAmplitude, hy]

end Problem356

end

end OAI

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

theorem squareDensity_ae_tsupport {g : E3 → ℝ} (hg : Measurable g) :
    ∀ᵐ x ∂densityMeasure (fun x => g x ^ 2), x ∈ tsupport g := by
  rw [densityMeasure, ae_withDensity_iff ((hg.pow_const 2).ennreal_ofReal)]
  apply ae_of_all
  intro x hx
  apply subset_tsupport g
  intro hgx
  exact hx (by simp [hgx])

theorem square_integral_eq_one {g : E3 → ℝ} (hg : Continuous g)
    [IsProbabilityMeasure (densityMeasure (fun x => g x ^ 2))] :
    (∫ x : E3, g x ^ 2) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (fun x => sq_nonneg (g x))) (hg.pow 2).aestronglyMeasurable]
  have hm := measure_univ (μ := densityMeasure (fun x => g x ^ 2))
  simpa only [densityMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, hm, ENNReal.toReal_one] using congrArg ENNReal.toReal hm

/-- A normalized smooth amplitude transports to another normalized smooth
amplitude. The derivative and its smooth square-root determinant are explicit
inputs, so the result is compatible with independently constructed local charts. -/
theorem transported_square_amplitude
    (e : OpenPartialHomeomorph E3 E3) {g : E3 → ℝ}
    (hg0 : ∀ x, 0 ≤ g x)
    (hg : ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) g)
    (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ e.source)
    (hmass : (∫ x : E3, g x ^ 2) = 1)
    (he : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) e.symm e.target)
    (D : E3 → E3 →L[ℝ] E3)
    (hD : ∀ y ∈ e.target, HasFDerivAt e.symm (D y) y)
    (hJ : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat)
      (fun y => Real.sqrt |(D y).det|) e.target) :
    ∃ q : E3 → ℝ,
      (∀ y, 0 ≤ q y) ∧
      ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) q ∧
      HasCompactSupport q ∧
      tsupport q ⊆ e '' tsupport g ∧
      (∫ y : E3, q y ^ 2) = 1 ∧
      Measure.map (LocalBranchMeasure.extendedBranch e 0)
        (densityMeasure (fun x => g x ^ 2)) = densityMeasure (fun y => q y ^ 2) := by
  let q := localTransportAmplitude e g (fun y => Real.sqrt |(D y).det|)
  have hq : ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) q :=
    contDiff_localTransportAmplitude e hg hgc hgs he hJ
  have hm : Measure.map (LocalBranchMeasure.extendedBranch e 0)
      (densityMeasure (fun x => g x ^ 2)) = densityMeasure (fun y => q y ^ 2) := by
    rw [LocalBranchMeasure.map_extendedBranch e 0 _
      ((squareDensity_ae_tsupport hg.continuous.measurable).mono (fun x hx => hgs hx))]
    exact map_squareDensity_localHomeomorph e g hgs D hD
  have := squareDensity_probability hg.continuous hgc hmass
  have : IsProbabilityMeasure (densityMeasure (fun y => q y ^ 2)) := by
    rw [← hm]
    exact Measure.isProbabilityMeasure_map
      (LocalBranchMeasure.measurable_extendedBranch e 0).aemeasurable
  refine ⟨q, localTransportAmplitude_nonneg e hg0 (fun y _ => Real.sqrt_nonneg _), hq,
    hasCompactSupport_localTransportAmplitude e _ hgc hgs,
    tsupport_localTransportAmplitude_subset e _ hgc hgs, ?_, hm⟩
  exact square_integral_eq_one hq.continuous

end Problem356.SmoothBranchMarginal

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.SmoothBranchMarginal
open MeasureTheory Set
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.Problem356.SmoothBranchMarginal.transported_square_amplitude := @_root_.OAI.Problem356.SmoothBranchMarginal.transported_square_amplitude
