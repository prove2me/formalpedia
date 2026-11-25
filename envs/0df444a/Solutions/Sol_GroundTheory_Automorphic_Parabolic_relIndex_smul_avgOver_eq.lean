-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.relIndex_smul_avgOver_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:28.147708+00:00
-- url     : https://prove2.me/submissions/c89a7661-289c-4d5c-b382-2b1672fe0bcd

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCount
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_of_forall_mul_eq
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_relIndex_inf_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_smul_avgOver_inf
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_mul_left_eq
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_comp_linearMap
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_le_rightStab_avgOver


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Set
variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
variable {A : Subgroup G}
variable (θ : A → W →ₗ[ℂ] W)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {E : Type*} [AddCommGroup E] [Module ℂ E] (π : W →ₗ[ℂ] E)
    (hπ : ∀ a : A, π ∘ₗ θ a = π) {K K' : Subgroup G} {h : G → W}
    (hh : ∀ a : A, ∀ y, h ((a : G) * y) = θ a (h y)) (hKK' : K ≤ K') (hf : AvgFinite K h)
    (hK : K.relIndex K' ≠ 0) (hsupp : ∀ y ∈ K', h y ≠ 0 → ∃ a ∈ A, ∃ k ∈ K, y = a * k) :
    (K.relIndex K' : ℂ) • π (avgOver K' h 1) =
      ((K ⊓ A).relIndex (K' ⊓ A) : ℂ) • π (avgOver K h 1) := by
  rw [avgOver_eq_smul_avgOver_inf hKK' hf hK hsupp, map_smul, smul_smul, ← mul_assoc,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 hK), one_mul]
  congr 1
  have hgf : AvgFinite (K' ⊓ A) (avgOver K h) := by
    have h1 : ((rightStab (avgOver K h)).subgroupOf (K' ⊓ A)) ≥
        (K ⊓ A).subgroupOf (K' ⊓ A) := fun k hk =>
      le_rightStab_avgOver hf (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hk)).1
    have hT := relIndex_inf_ne_zero (A := A) hK
    intro h0
    apply hT
    have := Subgroup.index_dvd_of_le h1
    exact Nat.eq_zero_of_zero_dvd (h0 ▸ this)
  rw [← avgOver_comp_linearMap hgf π]
  apply avgOver_eq_of_forall_mul_eq
  · have h1 : (rightStab (avgOver K h)) ≤ rightStab (fun y => π (avgOver K h y)) := fun k hk y => by
      show π (avgOver K h (y * k)) = π (avgOver K h y)
      rw [hk y]
    intro h0
    apply hgf
    have := Subgroup.relIndex_dvd_of_le_left (K' ⊓ A) h1
    exact Nat.eq_zero_of_zero_dvd (h0 ▸ this)
  · intro k hk
    rw [one_mul]
    have := avgOver_mul_left_eq θ hh hf ⟨k, (Subgroup.mem_inf.1 hk).2⟩ 1
    rw [mul_one] at this
    rw [this, ← LinearMap.comp_apply, hπ]
end GroundTheory.Automorphic.Parabolic
