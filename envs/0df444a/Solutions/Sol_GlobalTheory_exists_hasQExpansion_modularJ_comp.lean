-- Prove2me | solution 1 for GlobalTheory.exists_hasQExpansion_modularJ_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:16:20.395833+00:00
-- url     : https://prove2.me/submissions/7a454447-51ac-488e-a7c0-3ee6af99d0ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral
import Theorems.Thm_GlobalTheory_HasUnitLeadingExpansion_mul
import Theorems.Thm_GlobalTheory_HasQExpansion_mul
import Theorems.Thm_GlobalTheory_HasQExpansion_of_hasSum_pow
import Theorems.Thm_GlobalTheory_HasQExpansion_pow
import Theorems.Thm_GlobalTheory_exists_hasQExpansion_modularJ


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
theorem _root_.solution {n : ℝ} {w : ℍ → ℍ} {ζ : ℂ} (hζ : IsIntegral ℤ ζ) {e : ℕ}
    (he : e ≠ 0) (hw : ∀ τ, 𝕢 1 (w τ) = ζ * 𝕢 n τ ^ e) :
    ∃ ψ ∈ integralSeries, constantCoeff ψ = 1 ∧
      HasQExpansion n (fun τ ↦ ζ * 𝕢 n τ ^ e * modularJ (w τ)) ψ := by
  obtain ⟨J, hJ0, hJ⟩ := exists_hasQExpansion_modularJ
  refine ⟨_, fun k ↦ ?_, ?_, HasQExpansion.of_hasSum_pow (c := fun m ↦ (coeff m J : ℤ) * ζ ^ m) he
    fun τ ↦ ?_⟩
  · rw [coeff_mk]
    split_ifs
    exacts [(isIntegral_algebraMap (R := ℤ)).mul (hζ.pow _), isIntegral_zero]
  · simp [← coeff_zero_eq_constantCoeff_apply, hJ0]
  · have := hJ (w τ)
    simp only [hw, coeff_map, eq_intCast] at this
    convert! this using 2 with m
    ring
end GlobalTheory
