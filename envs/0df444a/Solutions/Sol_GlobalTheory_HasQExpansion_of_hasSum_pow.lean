-- Prove2me | solution 1 for GlobalTheory.HasQExpansion.of_hasSum_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:57.165492+00:00
-- url     : https://prove2.me/submissions/e4f573c8-ff12-4fd5-b646-f4562645dd17

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
theorem _root_.solution {c : ℕ → ℂ} {e : ℕ} (he : e ≠ 0)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m * (𝕢 h τ ^ e) ^ m) (f τ)) :
    HasQExpansion h f (PowerSeries.mk fun k ↦ if e ∣ k then c (k / e) else 0) := fun τ ↦ by
  have hinj : Injective (fun m : ℕ ↦ e * m) := mul_right_injective₀ he
  rw [← hinj.hasSum_iff]
  · convert hf τ using 2 with m
    simp [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero he), pow_mul]
  · intro k hk
    have : ¬ e ∣ k := fun ⟨m, hm⟩ ↦ hk ⟨m, hm.symm⟩
    simp [this]
end GlobalTheory.HasQExpansion
