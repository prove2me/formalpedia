-- Prove2me | solution 1 for GroundTheory.LocalField.classCount_mem_spanA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:04:26.978047+00:00
-- url     : https://prove2.me/submissions/00fab71b-17c3-4a08-88f7-2a9ad2014ec2

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Theorems.Thm_GroundTheory_LocalField_indFun_zpowers_delta
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_apply_mem_adjoin
import Theorems.Thm_GroundTheory_LocalField_IsIrrCharacter_isCharacter
import Theorems.Thm_GroundTheory_LocalField_eq_sum_irrChars_of_isClassFun
import Theorems.Thm_GroundTheory_LocalField_indFun_mem_spanZ
import Theorems.Thm_GroundTheory_LocalField_mem_irrChars
import Theorems.Thm_GroundTheory_LocalField_smul_mem_spanA


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
theorem _root_.solution (s : G) : classCount s ∈ spanA E ζ := by
  set C := Subgroup.zpowers s
  set s' : C := ⟨s, Subgroup.mem_zpowers s⟩
  set δ : C → ℂ := fun c ↦ if c = s' then (Nat.card C : ℂ) else 0
  have hcomm : ∀ a b : C, a * b = b * a := fun a b ↦
    (Subgroup.zpowers_isMulCommutative s).is_comm.comm a b
  have hδ : IsClassFun δ := by
    intro g h
    simp only [δ]
    rw [hcomm h g, mul_inv_cancel_right]
  have hN : (Nat.card C : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcoef : ∀ ψ : C → ℂ, charInner C δ ψ = ψ s'⁻¹ := by
    intro ψ
    rw [charInner_apply]
    simp only [δ, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), ← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  rw [← indFun_zpowers_delta]
  change indFun C.subtype δ ∈ spanA E ζ
  rw [eq_sum_irrChars_of_isClassFun hδ, map_sum]
  refine Submodule.sum_mem _ fun ψ hψ ↦ ?_
  rw [map_smul, hcoef]
  refine smul_mem_spanA ?_ (indFun_mem_spanZ hE hmono (hcyc s) (mem_irrChars.mp hψ).isCharacter)
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  refine (mem_irrChars.mp hψ).isCharacter.apply_mem_adjoin _ hζ ?_
  rw [← Subgroup.orderOf_coe]
  exact orderOf_dvd_natCard _
end GroundTheory.LocalField
