-- Prove2me | solution 1 for GlobalTheory.HasQExpansion.pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:54.945984+00:00
-- url     : https://prove2.me/submissions/29b0b7c7-d0e6-4ce6-846c-62d303ab7a3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Theorems.Thm_GlobalTheory_HasQExpansion_mul
import Theorems.Thm_GlobalTheory_HasQExpansion_const

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
theorem _root_.solution (hf : HasQExpansion h f φ) (n : ℕ) : HasQExpansion h (fun τ ↦ f τ ^ n) (φ ^ n) := by
  induction n with
  | zero => simpa using const h 1
  | succ n ih => simpa [pow_succ] using ih.mul hf
end GlobalTheory.HasQExpansion
