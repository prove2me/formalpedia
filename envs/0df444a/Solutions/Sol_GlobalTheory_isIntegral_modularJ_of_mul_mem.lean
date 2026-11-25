-- Prove2me | solution 1 for GlobalTheory.isIntegral_modularJ_of_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:14:09.357122+00:00
-- url     : https://prove2.me/submissions/b177d0d3-612e-40f1-9941-cb27f2ef3034

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral
import Theorems.Thm_GlobalTheory_isIntegral_modularJ_of_quadratic

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
theorem _root_.solution {τ : ℍ} {α : ℂ} (hα : ∀ m : ℤ, α ≠ m)
    (h : ∀ x ∈ Submodule.span ℤ {(τ : ℂ), 1}, α * x ∈ Submodule.span ℤ {(τ : ℂ), 1}) :
    IsIntegral ℤ (modularJ τ) := by
  obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp (h τ (Submodule.subset_span (by simp)))
  obtain ⟨r, s, hrs⟩ := Submodule.mem_span_pair.mp (h 1 (Submodule.subset_span (by simp)))
  simp only [zsmul_eq_mul, mul_one] at hpq hrs
  refine isIntegral_modularJ_of_quadratic (a := r) (b := s - p) (c := -q) ?_ ?_
  · rintro rfl
    exact hα s (by simpa using hrs.symm)
  · push_cast
    linear_combination (τ : ℂ) * hrs - hpq
end GlobalTheory
