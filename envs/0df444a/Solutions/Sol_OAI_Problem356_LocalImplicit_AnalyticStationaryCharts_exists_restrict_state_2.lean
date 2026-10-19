-- Prove2me | solution 2 for OAI.Problem356.LocalImplicit.AnalyticStationaryCharts.exists_restrict_state
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:00:15.244779+00:00
-- url     : https://prove2.me/submissions/86d17fc2-3ad1-457c-818a-ebbd5fbfea88

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/LocalImplicit.lean:L247-L273
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.LocalImplicit.AnalyticStationaryCharts.exists_restrict_state. The node keeps its source
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

-- ---- from OAI.Analysis.CoulombTransport.LocalImplicit ----
namespace OAI

universe uP uS

noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace Problem356.LocalImplicit

variable {P : Type uP} {S : Type uS}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]

namespace AnalyticStationaryCharts

variable {G : P × (S × S) → S × S} {p : P} {s : S × S}

omit [CompleteSpace P] [CompleteSpace S]

/-- Any smaller open state neighborhood can be used after shrinking the common
parameter domain. All chart functions and all uniqueness conclusions are preserved. -/
theorem exists_restrict_state
    (c : AnalyticStationaryCharts G p s) (W : Set (S × S))
    (hW : IsOpen W) (hsW : s ∈ W) (hWV : W ⊆ c.stateDomain) :
    ∃ d : AnalyticStationaryCharts G p s,
      d.stateDomain = W ∧ d.central.source ⊆ c.central.source ∧
      (d.central : P → S) = c.central ∧ (d.opposite : P → S) = c.opposite := by
  have hp₂ : p ∈ c.opposite.source := c.source_eq ▸ c.point_mem
  have hc₁ : ContinuousAt c.central p :=
    c.central.continuousOn.continuousAt (c.central.open_source.mem_nhds c.point_mem)
  have hc₂ : ContinuousAt c.opposite p :=
    c.opposite.continuousOn.continuousAt (c.opposite.open_source.mem_nhds hp₂)
  have hval : (c.central p, c.opposite p) = s :=
    Prod.ext c.central_value c.opposite_value
  have hpre : (fun y => (c.central y, c.opposite y)) ⁻¹' W ∈ 𝓝 p :=
    (hc₁.prodMk hc₂).preimage_mem_nhds (by rw [hval]; exact hW.mem_nhds hsW)
  obtain ⟨U, hUsub, hUopen, hpU⟩ := mem_nhds_iff.mp hpre
  let c₀ := c.restrictSource U hUopen hpU
  let d : AnalyticStationaryCharts G p s := {
    c₀ with
      stateDomain := W
      stateDomain_open := hW
      state_mem := hsW
      mapsTo_state := fun _ hy => hUsub hy.2
      unique_zero := fun y hy z hz => c.unique_zero y hy.1 z (hWV hz) }
  exact ⟨d, rfl, (fun _ hy => hy.1), rfl, rfl⟩

end AnalyticStationaryCharts

end Problem356.LocalImplicit

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.LocalImplicit OAI.Problem356.LocalImplicit.AnalyticStationaryCharts
open Filter Set
open scoped Topology ContDiff


theorem solution.{uP,uS} : type_of% @_root_.OAI.Problem356.LocalImplicit.AnalyticStationaryCharts.exists_restrict_state.{uP,uS} := @_root_.OAI.Problem356.LocalImplicit.AnalyticStationaryCharts.exists_restrict_state.{uP,uS}
