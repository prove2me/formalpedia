-- Prove2me | solution 2 for OAI.Problem356.Splitting.map_image_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:20:02.000504+00:00
-- url     : https://prove2.me/submissions/e7412401-1b32-4735-af1b-cdfa399db6b4

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/SplitMeasure.lean:L39-L56
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.Splitting.map_image_eq. The node keeps its source
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

-- ---- from OAI.Analysis.CoulombTransport.SplitMeasure ----
namespace OAI

universe uAlpha uIndex

/-! Measure identities for the five-component splitting construction. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356
namespace Splitting

variable {α : Type uAlpha} {ι : Type uIndex} [MeasurableSpace α]

/-- An injective branch has the original mass on the image of each central subset. -/
theorem map_image_eq
    (ν : Measure α) {B S : Set α} {H : α → α}
    (hν : ∀ᵐ x ∂ν, x ∈ B) (hH : Measurable H)
    (hInj : Set.InjOn H B) (hSB : S ⊆ B)
    (hImage : MeasurableSet (H '' S)) :
    (Measure.map H ν) (H '' S) = ν S := by
  rw [Measure.map_apply hH hImage]
  apply measure_congr
  filter_upwards [hν] with x hx
  apply propext
  change H x ∈ H '' S ↔ x ∈ S
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hyx : y = x := hInj (hSB hy) hx hxy
    simpa only [hyx] using hy
  · intro hxS
    exact ⟨x, hxS, rfl⟩

variable [Fintype ι]

end Splitting
end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.Splitting
open MeasureTheory Set
open scoped ENNReal


theorem solution.{uAlpha} : type_of% @_root_.OAI.Problem356.Splitting.map_image_eq.{uAlpha} := @_root_.OAI.Problem356.Splitting.map_image_eq.{uAlpha}
