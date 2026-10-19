-- Prove2me | solution 1 for OAI.Problem356.LocalImplicit.exists_analytic_implicit_branch
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:53:59.711491+00:00
-- url     : https://prove2.me/submissions/94c80ccf-4584-464f-9962-2eb9bec5144e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/LocalImplicit.lean:L18-L54
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.LocalImplicit.exists_analytic_implicit_branch. The node keeps its source
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

/-- Analytic implicit-function theorem, packaged on open product neighborhoods.
The equation is normalized to zero, as for a stationary-point equation. -/
theorem exists_analytic_implicit_branch
    (G : P × S → S) (p : P) (s : S)
    (hG : ContDiffAt ℝ ω G (p, s))
    (hzero : G (p, s) = 0)
    (hinv : (fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inr ℝ P S).IsInvertible) :
    ∃ (ψ : P → S) (U : Set P) (V : Set S),
      IsOpen U ∧ p ∈ U ∧ IsOpen V ∧ s ∈ V ∧
      ContDiffOn ℝ ω ψ U ∧ MapsTo ψ U V ∧ ψ p = s ∧
      (∀ y ∈ U, G (y, ψ y) = 0) ∧
      (∀ y ∈ U, ∀ z ∈ V, G (y, z) = 0 ↔ ψ y = z) ∧
      HasStrictFDerivAt ψ
        (-(fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inr ℝ P S).inverse ∘L
          (fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inl ℝ P S)) p := by
  let ψ : P → S := hG.implicitFunction (by simp) hinv
  have hψ : ContDiffAt ℝ ω ψ p := hG.contDiffAt_implicitFunction (by simp) hinv
  have hψp : ψ p = s := hG.implicitFunction_apply_self (by simp) hinv
  have heq : ∀ᶠ q in 𝓝 (p, s), G q = 0 ↔ ψ q.1 = q.2 := by
    simpa only [hzero] using hG.eventually_apply_eq_iff_implicitFunction (by simp) hinv
  obtain ⟨U₀, hU₀, V₀, hV₀, hprod⟩ := mem_nhds_prod_iff.mp heq
  obtain ⟨V, hVV₀, hVopen, hsV⟩ := mem_nhds_iff.mp hV₀
  have hmaps : ψ ⁻¹' V ∈ 𝓝 p := hψ.continuousAt.preimage_mem_nhds (by
    rw [hψp]
    exact hVopen.mem_nhds hsV)
  have hcont : ∀ᶠ y in 𝓝 p, ContDiffAt ℝ ω ψ y := hψ.eventually (by simp)
  have heqn : ∀ᶠ y in 𝓝 p, G (y, ψ y) = 0 := by
    simpa only [hzero] using hG.eventually_apply_implicitFunction (by simp) hinv
  obtain ⟨U, hUsub, hUopen, hpU⟩ :=
    mem_nhds_iff.mp (inter_mem hU₀ (inter_mem hmaps (hcont.and heqn)))
  refine ⟨ψ, U, V, hUopen, hpU, hVopen, hsV, ?_, ?_, hψp, ?_, ?_, ?_⟩
  · exact hUopen.contDiffOn_iff.mpr (fun _ hy => (hUsub hy).2.2.1)
  · exact fun y hy => (hUsub hy).2.1
  · exact fun y hy => (hUsub hy).2.2.2
  · intro y hy z hz
    exact hprod ⟨(hUsub hy).1, hVV₀ hz⟩
  · exact hG.hasStrictFDerivAt_implicitFunction (by simp) hinv

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


theorem solution.{uP,uS} : type_of% @_root_.OAI.Problem356.LocalImplicit.exists_analytic_implicit_branch.{uP,uS} := @_root_.OAI.Problem356.LocalImplicit.exists_analytic_implicit_branch.{uP,uS}
