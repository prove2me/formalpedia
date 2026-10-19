-- Prove2me | solution 2 for OAI.Problem356.map_withDensity_localHomeomorph
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:29:25.72881+00:00
-- url     : https://prove2.me/submissions/fc7f17a1-563a-4e08-8c98-91a1798f8dd8

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/SmoothPushforward.lean:L94-L128
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.map_withDensity_localHomeomorph. The node keeps its source
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

-- ---- from OAI.Analysis.CoulombTransport.SmoothPushforward ----
namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Problem356

/-- The inverse-Jacobian change-of-variables formula for a local
homeomorphism.  No global behavior outside its source is required. -/
theorem map_withDensity_localHomeomorph
    (e : OpenPartialHomeomorph E3 E3) (w : E3 → ℝ≥0∞)
    (D : E3 → E3 →L[ℝ] E3)
    (hD : ∀ y ∈ e.target, HasFDerivAt e.symm (D y) y) :
    Measure.map e (((volume : Measure E3).restrict e.source).withDensity w) =
      ((volume : Measure E3).restrict e.target).withDensity
        (fun y => ENNReal.ofReal |(D y).det| * w (e.symm y)) := by
  have he : AEMeasurable e ((volume : Measure E3).restrict e.source) :=
    e.continuousOn.aemeasurable e.open_source.measurableSet
  have hew : AEMeasurable e
      (((volume : Measure E3).restrict e.source).withDensity w) :=
    he.mono_ac (withDensity_absolutelyContinuous _ _)
  apply Measure.ext
  intro s hs
  have hpre : NullMeasurableSet (e ⁻¹' s)
      ((volume : Measure E3).restrict e.source) :=
    he.nullMeasurableSet_preimage hs
  rw [Measure.map_apply_of_aemeasurable hew hs,
    withDensity_apply₀ _ hpre, withDensity_apply _ hs,
    Measure.restrict_restrict₀ hpre, Measure.restrict_restrict hs]
  have hset : e.symm '' (s ∩ e.target) = e ⁻¹' s ∩ e.source := by
    ext x
    constructor
    · rintro ⟨y, ⟨hys, hyt⟩, rfl⟩
      exact ⟨by simpa only [mem_preimage, e.right_inv hyt] using hys,
        e.symm.map_source hyt⟩
    · rintro ⟨hxs, hxe⟩
      exact ⟨e x, ⟨hxs, e.map_source hxe⟩, e.left_inv hxe⟩
  rw [← hset]
  exact lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (hs.inter e.open_target.measurableSet)
    (fun y hy => (hD y hy.2).hasFDerivWithinAt)
    (e.symm.injOn.mono inter_subset_right) w

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open MeasureTheory Set Filter
open scoped Topology ENNReal


theorem solution : type_of% @_root_.OAI.Problem356.map_withDensity_localHomeomorph := @_root_.OAI.Problem356.map_withDensity_localHomeomorph
