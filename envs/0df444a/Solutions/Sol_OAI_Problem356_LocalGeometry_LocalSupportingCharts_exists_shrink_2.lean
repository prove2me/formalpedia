-- Prove2me | solution 2 for OAI.Problem356.LocalGeometry.LocalSupportingCharts.exists_shrink
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:24:02.484704+00:00
-- url     : https://prove2.me/submissions/5635ea45-050a-4a48-a22b-0b4897f08f84

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/LocalCertificate.lean:L145-L201
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.LocalGeometry.LocalSupportingCharts.exists_shrink. The node keeps its source
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
import Theorems.Thm_OAI_Problem356_LocalImplicit_AnalyticStationaryCharts_exists_restrict_state

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

/-- The common source can be chosen to be a genuine positive-radius ball,
inside any prescribed parameter neighborhood, without changing either chart function. -/
theorem exists_restrict_ball
    (c : AnalyticStationaryCharts G p s) (U : Set P) (hU : U ∈ 𝓝 p) :
    ∃ r : ℝ, 0 < r ∧ ∃ d : AnalyticStationaryCharts G p s,
      d.central.source = Metric.ball p r ∧ d.central.source ⊆ U ∧
      d.stateDomain = c.stateDomain ∧
      (d.central : P → S) = c.central ∧ (d.opposite : P → S) = c.opposite := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (c.central.open_source.mem_nhds c.point_mem) hU)
  let d := c.restrictSource (Metric.ball p r) Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hsource : d.central.source = Metric.ball p r :=
    inter_eq_right.mpr (fun _ hx => (hball hx).1)
  refine ⟨r, hr, d, hsource, ?_, rfl, rfl, rfl⟩
  rw [hsource]
  exact fun _ hx => (hball hx).2

end AnalyticStationaryCharts

end Problem356.LocalImplicit

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.LocalCertificate ----
namespace OAI

universe uE

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Problem356.LocalGeometry

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A local certificate survives arbitrary further neighborhood restrictions.
First shrink the state ball, and only then shrink the parameter ball so that
both branches still land in the new state ball. The functions and value are
unchanged, so previously established center values are preserved. -/
theorem LocalSupportingCharts.exists_shrink [CompleteSpace E]
    {F : E × (E × E) → ℝ} {G : E × (E × E) → E × E} {p : E} {s : E × E}
    (C : LocalSupportingCharts F G p s) (rp rs : ℝ) (hp : 0 < rp) (hs : 0 < rs) :
    ∃ D : LocalSupportingCharts F G p s,
      D.charts.central.source ⊆ C.charts.central.source ∩ Metric.ball p rp ∧
      D.charts.stateDomain ⊆ C.charts.stateDomain ∩ Metric.ball s rs ∧
      (D.charts.central : E → E) = C.charts.central ∧
      (D.charts.opposite : E → E) = C.charts.opposite ∧ D.value = C.value := by
  let r := min C.stateRadius rs
  have hr : 0 < r := lt_min C.stateRadius_pos hs
  have hball : Metric.ball s r ⊆ C.charts.stateDomain := by
    rw [C.state_ball]
    exact Metric.ball_subset_ball (min_le_left _ _)
  obtain ⟨d, hdstate, hdsource, hdX, hdZ⟩ := C.charts.exists_restrict_state
    (Metric.ball s r) Metric.isOpen_ball (Metric.mem_ball_self hr) hball
  have hU : d.central.source ∩ Metric.ball p rp ∈ 𝓝 p :=
    inter_mem (d.central.open_source.mem_nhds d.point_mem) (Metric.ball_mem_nhds p hp)
  obtain ⟨t, ht, e, hesource, heU, hestate, heX, heZ⟩ :=
    d.exists_restrict_ball (d.central.source ∩ Metric.ball p rp) hU
  have hsource : e.central.source ⊆ C.charts.central.source :=
    fun _ hy => hdsource (heU hy).1
  have hstate : e.stateDomain ⊆ C.charts.stateDomain := by
    rw [hestate, hdstate]
    exact hball
  have hsameX : (e.central : E → E) = C.charts.central := heX.trans hdX
  have hsameZ : (e.opposite : E → E) = C.charts.opposite := heZ.trans hdZ
  let D : LocalSupportingCharts F G p s := {
    charts := e
    parameterRadius := t
    parameterRadius_pos := ht
    source_ball := hesource
    stateRadius := r
    stateRadius_pos := hr
    state_ball := hestate.trans hdstate
    value := C.value
    value_analytic := C.value_analytic.mono hsource
    value_eq := by
      intro y
      rw [hsameX, hsameZ]
      exact C.value_eq y
    value_base := C.value_base
    supporting := fun y hy z hz => C.supporting y (hsource hy) z (hstate hz)
    contact := by
      intro y hy z hz
      rw [hsameX, hsameZ]
      exact C.contact y (hsource hy) z (hstate hz) }
  refine ⟨D, ?_, ?_, hsameX, hsameZ, rfl⟩
  · exact fun _ hy => ⟨hsource hy, (heU hy).2⟩
  · intro z hz
    refine ⟨hstate hz, ?_⟩
    change z ∈ e.stateDomain at hz
    rw [hestate, hdstate] at hz
    exact Metric.ball_subset_ball (min_le_right _ _) hz

end Problem356.LocalGeometry

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.LocalGeometry
open Set Filter
open scoped Topology ContDiff


theorem solution.{uE} : type_of% @_root_.OAI.Problem356.LocalGeometry.LocalSupportingCharts.exists_shrink.{uE} := @_root_.OAI.Problem356.LocalGeometry.LocalSupportingCharts.exists_shrink.{uE}
