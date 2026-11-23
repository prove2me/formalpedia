-- Prove2me | solution 1 for GlobalTheory.HasQExpansion.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:28.581679+00:00
-- url     : https://prove2.me/submissions/46789b73-7f46-410f-afe3-b5f0f7d1331f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm

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
theorem _root_.solution (hf : HasQExpansion h f φ) (hg : HasQExpansion h g ψ) :
    HasQExpansion h (fun τ ↦ f τ + g τ) (φ + ψ) := fun τ ↦ by
  simpa [add_mul] using (hf τ).add (hg τ)
end GlobalTheory.HasQExpansion
