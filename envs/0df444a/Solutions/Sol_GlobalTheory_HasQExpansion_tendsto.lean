-- Prove2me | solution 1 for GlobalTheory.HasQExpansion.tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:49:43.620303+00:00
-- url     : https://prove2.me/submissions/77658d76-37ef-463d-9d31-42c8c0f69cb7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Theorems.Thm_GlobalTheory_HasQExpansion_exists_analytic

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
    Tendsto f atImInfty (𝓝 (coeff 0 φ)) := by
  obtain ⟨F, hF, h0, hfF⟩ := hf.exists_analytic hh
  rw [show f = F ∘ fun τ : ℍ ↦ 𝕢 h τ from funext hfF, ← h0]
  exact (hF 0 (by simp)).continuousAt.tendsto.comp (qParam_tendsto_atImInfty hh)
end GlobalTheory.HasQExpansion
