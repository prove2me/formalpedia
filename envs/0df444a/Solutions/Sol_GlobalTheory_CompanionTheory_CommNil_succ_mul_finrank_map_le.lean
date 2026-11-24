-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CommNil.succ_mul_finrank_map_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:55:22.306605+00:00
-- url     : https://prove2.me/submissions/1e80f1b2-bd1d-47e2-a88a-67e34581a17b

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankRangePowConvex
import Theorems.Thm_GlobalTheory_CompanionTheory_CommNil_exists_rel_compl
import Theorems.Thm_GlobalTheory_CompanionTheory_CommNil_range_pow_succ_le
import Theorems.Thm_GlobalTheory_CompanionTheory_CommNil_succ_mul_drop_le
import Theorems.Thm_GlobalTheory_CompanionTheory_CommNil_range_le_ker_of_commute
import Theorems.Thm_GlobalTheory_CompanionTheory_CommNil_finrank_map_le_of_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CommNil
open Module
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.CommNil
theorem _root_.solution :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : Module.End ℂ V),
      IsNilpotent a → ∀ (x : ℕ) (A : Submodule ℂ (Module.End ℂ V)), (∀ b ∈ A, Commute b a) →
        (x + 1) * Module.finrank ℂ (A.map (LinearMap.mulRight ℂ (a ^ x))) ≤
          Module.finrank ℂ V ^ 2 := by
  intro V _ _ _ a ha x A hA
  obtain ⟨Y, hY, hdim⟩ := exists_rel_compl (LinearMap.range (a ^ (x + 1))) (LinearMap.range (a ^ x))
    (range_pow_succ_le a x)
  let T : Module.End ℂ V →ₗ[ℂ] (Y →ₗ[ℂ] V) := LinearMap.lcomp ℂ V Y.subtype
  have hker : ∀ b ∈ A, T b = 0 → LinearMap.mulRight ℂ (a ^ x) b = 0 := by
    intro b hbA hTb
    have hYk : Y ≤ LinearMap.ker b := by
      intro y hy
      have hy0 := LinearMap.congr_fun hTb ⟨y, hy⟩
      rw [LinearMap.lcomp_apply, LinearMap.zero_apply] at hy0
      exact LinearMap.mem_ker.2 hy0
    have hR := range_le_ker_of_commute a b (hA b hbA) ha x Y hY hYk
    rw [LinearMap.mulRight_apply]
    ext v
    rw [Module.End.mul_apply, LinearMap.zero_apply]
    exact LinearMap.mem_ker.1 (hR (LinearMap.mem_range_self _ v))
  have h7 := finrank_map_le_of_ker (LinearMap.mulRight ℂ (a ^ x)) T A hker
  have h8 : Module.finrank ℂ (A.map T) ≤ Module.finrank ℂ Y * Module.finrank ℂ V :=
    (Submodule.finrank_le _).trans (le_of_eq (Module.finrank_linearMap ℂ ℂ Y V))
  have h5 := succ_mul_drop_le a x
  have hr0 : Module.finrank ℂ (LinearMap.range (a ^ 0)) ≤ Module.finrank ℂ V := Submodule.finrank_le _
  rw [← hdim] at h5
  have hY1 : (x + 1) * Module.finrank ℂ Y ≤ Module.finrank ℂ V := by nlinarith [h5, hr0]
  calc (x + 1) * Module.finrank ℂ (A.map (LinearMap.mulRight ℂ (a ^ x)))
      ≤ (x + 1) * (Module.finrank ℂ Y * Module.finrank ℂ V) := Nat.mul_le_mul_left _ (h7.trans h8)
    _ = ((x + 1) * Module.finrank ℂ Y) * Module.finrank ℂ V := by ring
    _ ≤ Module.finrank ℂ V * Module.finrank ℂ V := Nat.mul_le_mul_right _ hY1
    _ = Module.finrank ℂ V ^ 2 := by ring
end GlobalTheory.CompanionTheory.CommNil
