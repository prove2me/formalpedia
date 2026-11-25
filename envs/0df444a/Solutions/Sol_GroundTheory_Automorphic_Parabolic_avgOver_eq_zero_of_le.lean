-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgOver_eq_zero_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:26.585693+00:00
-- url     : https://prove2.me/submissions/54d586ef-7350-463d-8417-24032f0de75d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCount
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_zero_of_forall
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_smul_avgOver_inf
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_mul_left_eq

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
theorem _root_.solution {K K' : Subgroup G} {h : G → W}
    (hh : ∀ a : A, ∀ y, h ((a : G) * y) = θ a (h y)) (hKK' : K ≤ K') (hf : AvgFinite K h)
    (hK : K.relIndex K' ≠ 0) (hsupp : ∀ y ∈ K', h y ≠ 0 → ∃ a ∈ A, ∃ k ∈ K, y = a * k)
    (h0 : avgOver K h 1 = 0) : avgOver K' h 1 = 0 := by
  rw [avgOver_eq_smul_avgOver_inf hKK' hf hK hsupp]
  rw [avgOver_eq_zero_of_forall, smul_zero]
  intro k hk
  rw [one_mul]
  have := avgOver_mul_left_eq θ hh hf ⟨k, (Subgroup.mem_inf.1 hk).2⟩ 1
  rw [mul_one] at this
  rw [this, h0, map_zero]
end GroundTheory.Automorphic.Parabolic
