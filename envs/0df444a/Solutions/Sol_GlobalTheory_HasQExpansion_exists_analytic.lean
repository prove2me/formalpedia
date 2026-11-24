-- Prove2me | solution 1 for GlobalTheory.HasQExpansion.exists_analytic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:32:02.252862+00:00
-- url     : https://prove2.me/submissions/ba31f093-39e3-4746-9259-0b5e39d667ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Theorems.Thm_GlobalTheory_HasQExpansion_one_le_radius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm Complex Function Filter PowerSeries
open scoped Topology MatrixGroups Manifold Real
noncomputable section
open GlobalTheory
local notation "𝕢" => Function.Periodic.qParam
open GlobalTheory.HasQExpansion
variable {h : ℝ} {f g : ℍ → ℂ} {φ ψ : PowerSeries ℂ}
namespace GlobalTheory.HasQExpansion
theorem _root_.solution (hh : 0 < h) (hf : HasQExpansion h f φ) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (Metric.ball 0 1) ∧ F 0 = coeff 0 φ ∧
      ∀ τ : ℍ, f τ = F (𝕢 h τ) := by
  set p := FormalMultilinearSeries.ofScalars ℂ (fun m ↦ coeff m φ) with hp
  have h1 : 1 ≤ p.radius := hf.one_le_radius hh
  have h2 : HasFPowerSeriesOnBall p.sum p 0 1 :=
    (p.hasFPowerSeriesOnBall (zero_lt_one.trans_le h1)).mono zero_lt_one h1
  refine ⟨p.sum, ?_, ?_, fun τ ↦ ?_⟩
  · have := h2.analyticOnNhd
    rwa [← ENNReal.coe_one, Metric.eball_coe] at this
  · rw [← h2.coeff_zero (fun _ ↦ 0)]
    simp [hp, FormalMultilinearSeries.ofScalars_apply_eq']
  · rw [FormalMultilinearSeries.sum, ← (hf τ).tsum_eq]
    simp [hp, FormalMultilinearSeries.ofScalars_apply_eq', mul_comm]
end GlobalTheory.HasQExpansion
