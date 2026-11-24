-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CommStep.adjoin_le_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:39:22.419323+00:00
-- url     : https://prove2.me/submissions/c51dfe95-9299-40b8-8b8b-b3fd1f6fe74a

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CommuteOfMemAdjoin
import Theorems.Thm_GlobalTheory_CompanionTheory_CommStep_commute_of_mem_adjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CommStep
open Module
namespace GlobalTheory.CompanionTheory.CommStep
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] {l : ℕ}
    (a : Fin (l + 1) → Module.End ℂ V) (hc : ∀ i j, Commute (a i) (a j)) :
    Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a)) ≤
      Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ)) ⊔
        (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
          (LinearMap.mulRight ℂ (a 0)) := by
  have hBC : Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ) ≤
      Algebra.adjoin ℂ (Set.range a) :=
    Algebra.adjoin_mono (Set.range_subset_iff.2 fun k => ⟨k.succ, rfl⟩)
  have ha0 : a 0 ∈ Algebra.adjoin ℂ (Set.range a) := Algebra.subset_adjoin ⟨0, rfl⟩
  intro y hy
  rw [Subalgebra.mem_toSubmodule] at hy
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    induction j using Fin.cases with
    | zero =>
      refine Submodule.mem_sup_right (Submodule.mem_map.2 ⟨1, ?_, ?_⟩)
      · exact (Subalgebra.mem_toSubmodule _).2 (one_mem _)
      · rw [LinearMap.mulRight_apply, one_mul]
    | succ k => exact Submodule.mem_sup_left (Algebra.subset_adjoin ⟨k, rfl⟩)
  | algebraMap r => exact Submodule.mem_sup_left (Subalgebra.algebraMap_mem _ r)
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    obtain ⟨p₁, hp₁, z₁, hz₁, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨p₂, hp₂, z₂, hz₂, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨q₁, hq₁, rfl⟩ := Submodule.mem_map.1 hz₁
    obtain ⟨q₂, hq₂, rfl⟩ := Submodule.mem_map.1 hz₂
    rw [Subalgebra.mem_toSubmodule] at hp₁ hp₂ hq₁ hq₂
    rw [LinearMap.mulRight_apply, LinearMap.mulRight_apply]
    have hp₂c : Commute p₂ (a 0) := GlobalTheory.CompanionTheory.CommStep.commute_of_mem_adjoin a hc 0 (hBC hp₂)
    have hq₂c : Commute q₂ (a 0) := GlobalTheory.CompanionTheory.CommStep.commute_of_mem_adjoin a hc 0 hq₂
    have e₁ : q₁ * a 0 * p₂ = q₁ * p₂ * a 0 := by
      rw [mul_assoc, ← hp₂c.eq, ← mul_assoc]
    have e₂ : q₁ * a 0 * (q₂ * a 0) = q₁ * q₂ * a 0 * a 0 := by
      rw [← mul_assoc, mul_assoc q₁, ← hq₂c.eq, ← mul_assoc]
    have key : (p₁ + q₁ * a 0) * (p₂ + q₂ * a 0) =
        p₁ * p₂ + (p₁ * q₂ + q₁ * p₂ + q₁ * q₂ * a 0) * a 0 := by
      rw [add_mul, mul_add, mul_add, e₁, e₂]
      simp only [add_mul, mul_assoc, add_assoc]
    rw [key]
    refine Submodule.add_mem_sup ((Subalgebra.mem_toSubmodule _).2 (mul_mem hp₁ hp₂))
      (Submodule.mem_map.2 ⟨p₁ * q₂ + q₁ * p₂ + q₁ * q₂ * a 0, ?_, LinearMap.mulRight_apply _ _ _⟩)
    rw [Subalgebra.mem_toSubmodule]
    exact add_mem (add_mem (mul_mem (hBC hp₁) hq₂) (mul_mem hq₁ (hBC hp₂)))
      (mul_mem (mul_mem hq₁ hq₂) ha0)
end GlobalTheory.CompanionTheory.CommStep
