-- Prove2me | solution 1 for GlobalTheory.HasQExpansion.const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:05.660292+00:00
-- url     : https://prove2.me/submissions/52c48db8-fe92-426f-9242-97e9c91391bd

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
theorem _root_.solution (h : ℝ) (c : ℂ) : HasQExpansion h (fun _ ↦ c) (C c) := fun τ ↦ by
  have := hasSum_single (f := fun m ↦ coeff m (C c) * 𝕢 h τ ^ m) 0
    (fun m hm ↦ by simp [coeff_C, hm])
  simpa using this
end GlobalTheory.HasQExpansion
