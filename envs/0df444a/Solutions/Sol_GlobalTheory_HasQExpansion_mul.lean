-- Prove2me | solution 1 for GlobalTheory.HasQExpansion.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:05.83905+00:00
-- url     : https://prove2.me/submissions/061b0244-2f85-4be1-a0a2-567cb9ab1ab9

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
    HasQExpansion h (fun τ ↦ f τ * g τ) (φ * ψ) := fun τ ↦ by
  have h1 := (hf τ).summable.norm
  have h2 := (hg τ).summable.norm
  have h3 := (summable_norm_sum_mul_antidiagonal_of_summable_norm h1 h2).of_norm.hasSum
  rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm h1 h2, (hf τ).tsum_eq,
    (hg τ).tsum_eq] at h3
  convert! h3 using 2 with m
  rw [coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hx]
  ring
end GlobalTheory.HasQExpansion
