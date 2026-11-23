-- Prove2me | solution 1 for GlobalTheory.HasQExpansion.sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:41.334806+00:00
-- url     : https://prove2.me/submissions/79a0d6ee-7db6-49b2-865e-d2ed34a78152

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
    HasQExpansion h (fun τ ↦ f τ - g τ) (φ - ψ) := fun τ ↦ by
  simpa [sub_mul] using (hf τ).sub (hg τ)
end GlobalTheory.HasQExpansion
