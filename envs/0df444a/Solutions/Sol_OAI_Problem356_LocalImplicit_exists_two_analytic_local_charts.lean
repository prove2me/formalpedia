-- Prove2me | solution 1 for OAI.Problem356.LocalImplicit.exists_two_analytic_local_charts
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:56:59.559925+00:00
-- url     : https://prove2.me/submissions/969535c7-ee4a-46b6-a406-7536caf89136

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/LocalImplicit.lean:L98-L132
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.LocalImplicit.exists_two_analytic_local_charts. The node keeps its source
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
import Theorems.Thm_OAI_Problem356_LocalImplicit_exists_analytic_local_diffeomorph

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

omit [CompleteSpace S] in
/-- The two projections of a local branch can be made analytic diffeomorphisms
on one common source neighborhood, contained in any prescribed neighborhood. -/
theorem exists_two_analytic_local_charts
    (ψ : P → S × S) (p : P) (U : Set P) (hU : U ∈ 𝓝 p)
    (hψ : ContDiffAt ℝ ω ψ p)
    (hinv₁ : (fderiv ℝ (fun y => (ψ y).1) p).IsInvertible)
    (hinv₂ : (fderiv ℝ (fun y => (ψ y).2) p).IsInvertible) :
    ∃ e₁ e₂ : OpenPartialHomeomorph P S,
      (e₁ : P → S) = (fun y => (ψ y).1) ∧
      (e₂ : P → S) = (fun y => (ψ y).2) ∧
      p ∈ e₁.source ∧ e₁.source = e₂.source ∧ e₁.source ⊆ U ∧
      ContDiffOn ℝ ω e₁ e₁.source ∧ ContDiffOn ℝ ω e₁.symm e₁.target ∧
      ContDiffOn ℝ ω e₂ e₂.source ∧ ContDiffOn ℝ ω e₂.symm e₂.target := by
  obtain ⟨e₁, he₁, hp₁, hc₁, hi₁⟩ :=
    exists_analytic_local_diffeomorph (fun y => (ψ y).1) p hψ.fst hinv₁
  obtain ⟨e₂, he₂, hp₂, hc₂, hi₂⟩ :=
    exists_analytic_local_diffeomorph (fun y => (ψ y).2) p hψ.snd hinv₂
  obtain ⟨O, hOU, hOopen, hpO⟩ := mem_nhds_iff.mp hU
  let W := e₁.source ∩ (e₂.source ∩ O)
  have hWopen : IsOpen W := e₁.open_source.inter (e₂.open_source.inter hOopen)
  have hW₁ : W ⊆ e₁.source := fun _ h => h.1
  have hW₂ : W ⊆ e₂.source := fun _ h => h.2.1
  have hs₁ : (e₁.restrOpen W hWopen).source = W := inter_eq_right.mpr hW₁
  have hs₂ : (e₂.restrOpen W hWopen).source = W := inter_eq_right.mpr hW₂
  refine ⟨e₁.restrOpen W hWopen, e₂.restrOpen W hWopen, he₁, he₂, ?_,
    hs₁.trans hs₂.symm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs₁]
    exact ⟨hp₁, hp₂, hpO⟩
  · rw [hs₁]
    exact fun _ h => hOU h.2.2
  · exact hc₁.mono (fun _ h => h.1)
  · exact hi₁.mono (fun _ h => h.1)
  · exact hc₂.mono (fun _ h => h.1)
  · exact hi₂.mono (fun _ h => h.1)

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


theorem solution.{uP,uS} : type_of% @_root_.OAI.Problem356.LocalImplicit.exists_two_analytic_local_charts.{uP,uS} := @_root_.OAI.Problem356.LocalImplicit.exists_two_analytic_local_charts.{uP,uS}
