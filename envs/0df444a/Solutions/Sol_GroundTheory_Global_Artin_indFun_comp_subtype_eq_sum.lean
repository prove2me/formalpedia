-- Prove2me | solution 1 for GroundTheory.Global.Artin.indFun_comp_subtype_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:35.324897+00:00
-- url     : https://prove2.me/submissions/84feb893-cc30-489c-a5d7-c02c68984e5c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_TateCohomology_DoubleCosetSum
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
import Theorems.Thm_GroundTheory_Global_Artin_extendByZero_coe
import Theorems.Thm_GroundTheory_Global_Artin_extendByZero_conj
import Theorems.Thm_GroundTheory_Global_Artin_indFun_subtype_apply
import Theorems.Thm_GroundTheory_Global_Artin_sum_mul_mul_eq
import Theorems.Thm_GroundTheory_Global_Artin_extendByZero_conjFun
import Theorems.Thm_GroundTheory_GroupCoh_doubleCosetMap_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.doubleCosetMap_mk


attribute [local simp] GroundTheory.Global.Artin.extendByZero_coe

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
open GroundTheory.LocalField
variable {G : Type*} [Group G]
variable [Fintype G]
open Classical
namespace GroundTheory.Global.Artin
theorem _root_.solution (H D : Subgroup G) [Fintype H] [Fintype D] {f : H → ℂ}
    (hf : IsClassFun f) (x : DoubleCoset.Quotient (H : Set G) D → G)
    (hx : ∀ q, DoubleCoset.mk H D (x q) = q) :
    indFun H.subtype f ∘ D.subtype =
      ∑ q, indFun ((MulAut.conj (x q)⁻¹ • H : Subgroup G).subgroupOf D).subtype
        (conjFun H D (x q) f) := by
  classical
  funext d
  rw [Function.comp_apply, Finset.sum_apply, indFun_subtype_apply]
  simp_rw [indFun_subtype_apply, extendByZero_conjFun]
  have h1 : ∑ t : G, extendByZero H f (t⁻¹ * D.subtype d * t) =
      ∑ u : G, extendByZero H f (u * d * u⁻¹) :=
    Fintype.sum_equiv (Equiv.inv G) _ _ (fun t ↦ by simp)
  rw [h1, ← Finset.sum_fiberwise Finset.univ (DoubleCoset.mk H D), Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have key := sum_mul_mul_eq H D (x q) (fun u ↦ extendByZero H f (u * d * u⁻¹))
  rw [hx q] at key
  set E : Subgroup D := (MulAut.conj (x q)⁻¹ • H : Subgroup G).subgroupOf D
  have hE0 : (Nat.card E : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hH0 : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h2 : ∀ (h : H) (e : D), extendByZero H f ((h * x q * e) * d * (h * x q * e)⁻¹) =
      extendByZero H f (x q * ((e * d * e⁻¹ : D) : G) * (x q)⁻¹) := by
    intro h e
    rw [← extendByZero_conj hf h.2 (x q * ((e * d * e⁻¹ : D) : G) * (x q)⁻¹)]
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have h3 : ∑ h : H, ∑ e : D, extendByZero H f ((h * x q * e) * d * (h * x q * e)⁻¹) =
      Nat.card H * ∑ t : D, extendByZero H f (x q * ((t⁻¹ * d * t : D) : G) * (x q)⁻¹) := by
    simp_rw [h2]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
    congr 1
    exact Fintype.sum_equiv (Equiv.inv D) _ _ (fun e ↦ by simp)
  rw [h3] at key
  have hS : ∑ u ∈ Finset.univ.filter (fun u ↦ DoubleCoset.mk H D u = q),
      extendByZero H f (u * d * u⁻¹) = (Nat.card E : ℂ)⁻¹ *
        (Nat.card H * ∑ t : D, extendByZero H f (x q * ((t⁻¹ * d * t : D) : G) * (x q)⁻¹)) := by
    rw [key, inv_mul_cancel_left₀ hE0]
  rw [hS, mul_left_comm, inv_mul_cancel_left₀ hH0]
end GroundTheory.Global.Artin
