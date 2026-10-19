-- Prove2me | solution 2 for OAI.Problem356.ae_branchMarginal_mem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:24:28.286342+00:00
-- url     : https://prove2.me/submissions/e6113844-e034-4fdb-beae-4a7e137340eb

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/CounterexampleAssembly.lean:L23-L40
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.ae_branchMarginal_mem. The node keeps its source
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

-- ---- from OAI.Analysis.CoulombTransport.CounterexampleAssembly ----
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- Support of the central measure and its four images gives support of the
five-component marginal. -/
lemma ae_branchMarginal_mem (nu : Measure E3) {H : Fin 4 → E3 → E3}
    (hH : ∀ i, Measurable (H i)) {B U : Set E3}
    (hU : MeasurableSet U) (hfull : ∀ᵐ x ∂nu, x ∈ B)
    (hBU : B ⊆ U) (hHU : ∀ i, H i '' B ⊆ U) :
    ∀ᵐ x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3), x ∈ U := by
  have hcentral : ∀ᵐ x ∂nu, x ∈ U := hfull.mono fun _ hx => hBU hx
  have houter : ∀ i, ∀ᵐ x ∂Measure.map (H i) nu, x ∈ U := by
    intro i
    apply (ae_map_iff (hH i).aemeasurable hU).mpr
    exact hfull.mono fun x hx => hHU i ⟨x, hx, rfl⟩
  unfold branchMarginal
  apply ae_add_measure_iff.mpr
  refine ⟨Measure.ae_smul_measure hcentral _, Measure.ae_smul_measure ?_ _⟩
  exact ae_add_measure_iff.mpr
    ⟨ae_add_measure_iff.mpr ⟨ae_add_measure_iff.mpr ⟨houter 0, houter 1⟩, houter 2⟩,
      houter 3⟩

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open MeasureTheory
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.Problem356.ae_branchMarginal_mem := @_root_.OAI.Problem356.ae_branchMarginal_mem
