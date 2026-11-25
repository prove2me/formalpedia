-- Prove2me | solution 1 for GroundTheory.Global.Artin.card_mul_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:55:31.849001+00:00
-- url     : https://prove2.me/submissions/dd2b44da-f1f3-4008-a8ea-d5814b08fff4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
import Definitions.Def_GroundTheory_GlobalFields_Artin_MackeyFrobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
open GroundTheory.LocalField
variable {G : Type*} [Group G]
variable {H D I : Subgroup G}
namespace GroundTheory.Global.Artin
theorem _root_.solution [Finite G] (hID : I ≤ D) [hN : (I.subgroupOf D).Normal] (x : G) :
    Nat.card D * Nat.card ((MulAut.conj x • I : Subgroup G).subgroupOf H) =
      frobIndex H D I x * Nat.card I *
        Nat.card ((MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D) := by
  set I' := I.subgroupOf D with hI'
  set E := (MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D with hE
  have hK : (I ⊔ ((MulAut.conj x⁻¹ • H : Subgroup G) ⊓ D)).subgroupOf D = I' ⊔ E := by
    rw [Subgroup.subgroupOf_sup hID inf_le_right, Subgroup.inf_subgroupOf_right]
  have hr : frobIndex H D I x = (I' ⊔ E).index := by
    rw [frobIndex, Subgroup.relIndex, hK]
  have h1 : Nat.card D = Nat.card (I' ⊔ E : Subgroup D) * (I' ⊔ E).index :=
    (Subgroup.card_mul_index _).symm
  have h2 : Nat.card (I' ⊔ E : Subgroup D) = Nat.card I' * I'.relIndex E := by
    rw [← Subgroup.relIndex_sup_left, ← Subgroup.card_mul_index (I'.subgroupOf (I' ⊔ E)),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : I' ≤ I' ⊔ E)).toEquiv]
    rfl
  have h3 : Nat.card E = Nat.card (I'.subgroupOf E) * I'.relIndex E :=
    (Subgroup.card_mul_index _).symm
  have h4 : Nat.card I' = Nat.card I := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hID).toEquiv
  have hw : ∀ w : (MulAut.conj x • I : Subgroup G).subgroupOf H, x⁻¹ * ((w : H) : G) * x ∈ I :=
    fun w ↦ (mem_conj_smul_iff I x _).1 (Subgroup.mem_subgroupOf.1 w.2)
  have h5 : Nat.card ((MulAut.conj x • I : Subgroup G).subgroupOf H) =
      Nat.card (I'.subgroupOf E) := by
    refine Nat.card_congr
      { toFun := fun w ↦ ⟨⟨⟨x⁻¹ * ((w : H) : G) * x, hID (hw w)⟩, ?_⟩, ?_⟩
        invFun := fun z ↦ ⟨⟨x * (((z : E) : D) : G) * x⁻¹, ?_⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · rename_i w
      rw [hE, Subgroup.mem_subgroupOf, mem_conj_inv_smul_iff]
      change x * (x⁻¹ * ((w : H) : G) * x) * x⁻¹ ∈ H
      rw [show x * (x⁻¹ * ((w : H) : G) * x) * x⁻¹ = (w : H) by group]
      exact (w : H).2
    · rename_i w
      rw [Subgroup.mem_subgroupOf, hI', Subgroup.mem_subgroupOf]
      exact hw w
    · rename_i z
      exact (mem_conj_inv_smul_iff H x _).1 (Subgroup.mem_subgroupOf.1 (z : E).2)
    · rename_i z
      rw [Subgroup.mem_subgroupOf, mem_conj_smul_iff]
      change x⁻¹ * (x * (((z : E) : D) : G) * x⁻¹) * x ∈ I
      rw [show x⁻¹ * (x * (((z : E) : D) : G) * x⁻¹) * x = ((z : E) : D) by group]
      exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 z.2)
    · intro w
      apply Subtype.ext
      apply Subtype.ext
      change x * (x⁻¹ * ((w : H) : G) * x) * x⁻¹ = (w : H)
      group
    · intro z
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      change x⁻¹ * (x * (((z : E) : D) : G) * x⁻¹) * x = ((z : E) : D)
      group
  rw [h1, h2, h3, h4, h5, hr]
  ring
end GroundTheory.Global.Artin
