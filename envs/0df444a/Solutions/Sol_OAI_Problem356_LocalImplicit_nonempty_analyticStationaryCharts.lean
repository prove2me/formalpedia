-- Prove2me | solution 1 for OAI.Problem356.LocalImplicit.nonempty_analyticStationaryCharts
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:58:23.600237+00:00
-- url     : https://prove2.me/submissions/2075d4fa-8391-4a88-b70e-997fac9443b9

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/LocalImplicit.lean:L160-L205
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.LocalImplicit.nonempty_analyticStationaryCharts. The node keeps its source
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
import Theorems.Thm_OAI_Problem356_LocalImplicit_exists_analytic_implicit_branch
import Theorems.Thm_OAI_Problem356_LocalImplicit_exists_two_analytic_local_charts

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

/-- Local stationarity plus the three invertibility checks produces two genuine
analytic charts on a common open source. -/
theorem nonempty_analyticStationaryCharts
    (G : P × (S × S) → S × S) (p : P) (s : S × S)
    (hG : ContDiffAt ℝ ω G (p, s)) (hzero : G (p, s) = 0)
    (hinv : (fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inr ℝ P (S × S)).IsInvertible)
    (hcentral : (ContinuousLinearMap.fst ℝ S S ∘L implicitDerivative G p s).IsInvertible)
    (hopposite : (ContinuousLinearMap.snd ℝ S S ∘L implicitDerivative G p s).IsInvertible) :
    Nonempty (AnalyticStationaryCharts G p s) := by
  obtain ⟨ψ, U, V, hUopen, hpU, hVopen, hsV, hψU, hψV, hψp, heqn, huniq, hd⟩ :=
    exists_analytic_implicit_branch G p s hG hzero hinv
  have hψ : ContDiffAt ℝ ω ψ p := hUopen.contDiffOn_iff.mp hψU hpU
  have hd₁ : HasFDerivAt (fun y => (ψ y).1)
      (ContinuousLinearMap.fst ℝ S S ∘L implicitDerivative G p s) p :=
    hd.hasFDerivAt.fst
  have hd₂ : HasFDerivAt (fun y => (ψ y).2)
      (ContinuousLinearMap.snd ℝ S S ∘L implicitDerivative G p s) p :=
    hd.hasFDerivAt.snd
  obtain ⟨e₁, e₂, he₁, he₂, hp, hsource, hsub, hc₁, hi₁, hc₂, hi₂⟩ :=
    exists_two_analytic_local_charts ψ p U (hUopen.mem_nhds hpU) hψ
      (by rw [hd₁.fderiv]; exact hcentral) (by rw [hd₂.fderiv]; exact hopposite)
  refine ⟨{
    central := e₁
    opposite := e₂
    source_eq := hsource
    point_mem := hp
    central_value := ?_
    opposite_value := ?_
    stateDomain := V
    stateDomain_open := hVopen
    state_mem := hsV
    mapsTo_state := ?_
    stationary := ?_
    unique_zero := ?_
    central_analytic := hc₁
    central_inverse_analytic := hi₁
    opposite_analytic := hc₂
    opposite_inverse_analytic := hi₂ }⟩
  · simp only [he₁, hψp]
  · simp only [he₂, hψp]
  · intro y hy
    simpa only [he₁, he₂, Prod.eta] using hψV (hsub hy)
  · intro y hy
    simpa only [he₁, he₂, Prod.eta] using heqn y (hsub hy)
  · intro y hy z hz
    simpa only [he₁, he₂, Prod.eta] using huniq y (hsub hy) z hz

namespace AnalyticStationaryCharts

variable {G : P × (S × S) → S × S} {p : P} {s : S × S}

omit [CompleteSpace P] [CompleteSpace S]

end AnalyticStationaryCharts

end Problem356.LocalImplicit

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.LocalImplicit
open Filter Set
open scoped Topology ContDiff


theorem solution.{uP,uS} : type_of% @_root_.OAI.Problem356.LocalImplicit.nonempty_analyticStationaryCharts.{uP,uS} := @_root_.OAI.Problem356.LocalImplicit.nonempty_analyticStationaryCharts.{uP,uS}
