-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CommNil.finrank_range_pow_convex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:24:21.326671+00:00
-- url     : https://prove2.me/submissions/fc224750-c15f-4205-98a0-345c199fe7a9

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankRangePowConvex
import Theorems.Thm_GlobalTheory_CompanionTheory_CommNil_range_pow_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_CommNil_range_pow_succ_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory.CompanionTheory.CommNil
open Module
variable {V : Type} [AddCommGroup V] [Module ℂ V]
private theorem finrank_map_add_finrank_inf_ker' {E F : Type} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] [AddCommGroup F] [Module ℂ F] (f : E →ₗ[ℂ] F) (A : Submodule ℂ E) :
    finrank ℂ (A.map f) + finrank ℂ (A ⊓ LinearMap.ker f : Submodule ℂ E) = finrank ℂ A := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict A)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  rw [← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]
  exact h
end GlobalTheory.CompanionTheory.CommNil
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CommNil
open Module
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.CommNil
theorem _root_.solution [FiniteDimensional ℂ V] (a : Module.End ℂ V) (i : ℕ) :
    2 * finrank ℂ (LinearMap.range (a ^ (i + 1))) ≤
      finrank ℂ (LinearMap.range (a ^ i)) + finrank ℂ (LinearMap.range (a ^ (i + 2))) := by
  have h0 : finrank ℂ (LinearMap.range (a ^ (i + 1))) +
      finrank ℂ (LinearMap.range (a ^ i) ⊓ LinearMap.ker a : Submodule ℂ V) = finrank ℂ (LinearMap.range (a ^ i)) := by
    have h := finrank_map_add_finrank_inf_ker' a (LinearMap.range (a ^ i))
    rw [← range_pow_succ] at h
    exact h
  have h1 : finrank ℂ (LinearMap.range (a ^ (i + 2))) +
      finrank ℂ (LinearMap.range (a ^ (i + 1)) ⊓ LinearMap.ker a : Submodule ℂ V) =
        finrank ℂ (LinearMap.range (a ^ (i + 1))) := by
    have h := finrank_map_add_finrank_inf_ker' a (LinearMap.range (a ^ (i + 1)))
    rw [← range_pow_succ] at h
    exact h
  have hmono : finrank ℂ (LinearMap.range (a ^ (i + 1)) ⊓ LinearMap.ker a : Submodule ℂ V) ≤
      finrank ℂ (LinearMap.range (a ^ i) ⊓ LinearMap.ker a : Submodule ℂ V) :=
    Submodule.finrank_mono (inf_le_inf_right _ (range_pow_succ_le a i))
  omega
end GlobalTheory.CompanionTheory.CommNil
