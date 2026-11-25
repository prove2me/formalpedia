-- Prove2me | solution 1 for GroundTheory.LocalField.mem_spanA_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:58:07.963084+00:00
-- url     : https://prove2.me/submissions/a4d68760-69e4-4a59-8971-d38dd5e46322

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Theorems.Thm_GroundTheory_LocalField_classCount_mem_spanA
import Theorems.Thm_GroundTheory_LocalField_card_smul_eq_sum_classCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
open scoped Classical
universe u
variable {G : Type u} [Group G] [Fintype G]
variable {E : Subgroup G → Prop} (hE : ∀ K L : Subgroup G, E K → L ≤ K → E L)
  (hmono : ∀ K : Subgroup G, E K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
  (hcyc : ∀ s : G, E (Subgroup.zpowers s))
  {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))
include hE hmono hcyc hζ
namespace GroundTheory.LocalField
theorem _root_.solution {F : G → ℂ} (hF : IsClassFun F)
    (hdiv : ∀ g, ∃ k : ℤ, F g = (Nat.card G : ℂ) * k) : F ∈ spanA E ζ := by
  choose k hk using hdiv
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hF' : F = ∑ s : G, k s • classCount s := by
    have h := card_smul_eq_sum_classCount hF
    funext g
    have hg := congrFun h g
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hg
    simp only [Finset.sum_apply]
    simp only [Pi.smul_apply, zsmul_eq_mul]
    apply mul_left_cancel₀ hG
    rw [hg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [hk s]
    ring
  rw [hF']
  exact Submodule.sum_mem _ fun s _ ↦ Submodule.smul_mem _ _ (classCount_mem_spanA hE hmono hcyc hζ s)
end GroundTheory.LocalField
