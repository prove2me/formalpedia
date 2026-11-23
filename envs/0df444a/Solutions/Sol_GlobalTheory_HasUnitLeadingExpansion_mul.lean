-- Prove2me | solution 1 for GlobalTheory.HasUnitLeadingExpansion.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:22:03.639041+00:00
-- url     : https://prove2.me/submissions/4b50e003-c1b2-4476-831b-8c643ac81fd9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral
import Theorems.Thm_GlobalTheory_HasQExpansion_congr
import Theorems.Thm_GlobalTheory_HasQExpansion_mul


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
namespace GlobalTheory
namespace HasUnitLeadingExpansion
theorem _root_.solution {n : ℝ} {f g : ℍ → ℂ} (hf : HasUnitLeadingExpansion n f)
    (hg : HasUnitLeadingExpansion n g) : HasUnitLeadingExpansion n (f * g) := by
  obtain ⟨e, φ, h1, h2, h3, h4⟩ := hf
  obtain ⟨e', ψ, h1', h2', h3', h4'⟩ := hg
  refine ⟨e + e', φ * ψ, mul_mem h1 h1', by simp [h2, h2'], ?_,
    (h4.mul h4').congr fun τ ↦ by simp only [Pi.mul_apply]; ring⟩
  rw [map_mul, mul_inv]
  exact h3.mul h3'
end HasUnitLeadingExpansion
end GlobalTheory
