-- Prove2me | solution 1 for GlobalTheory.HasQExpansion.of_qParam_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:05.90216+00:00
-- url     : https://prove2.me/submissions/0be31323-6392-4ead-8cbe-956f9d15f000

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
theorem _root_.solution (hf : HasQExpansion h (fun τ ↦ 𝕢 h τ * f τ) (X * φ)) :
    HasQExpansion h f φ := fun τ ↦ by
  have h1 := (hasSum_nat_add_iff' 1).mpr (hf τ)
  have hq : 𝕢 h τ ≠ 0 := Periodic.qParam_ne_zero _
  have h2 := h1.mul_left (𝕢 h τ)⁻¹
  simp only [coeff_succ_X_mul, Finset.range_one, Finset.sum_singleton, coeff_zero_X_mul,
    zero_mul, sub_zero, inv_mul_cancel_left₀ hq] at h2
  convert! h2 using 2 with m
  field_simp
  ring
end GlobalTheory.HasQExpansion
