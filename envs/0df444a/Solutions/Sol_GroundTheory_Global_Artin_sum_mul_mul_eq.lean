-- Prove2me | solution 1 for GroundTheory.Global.Artin.sum_mul_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:28.89236+00:00
-- url     : https://prove2.me/submissions/2efe8ca1-9825-4eec-b72f-96f4514c9ac0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_TateCohomology_DoubleCosetSum
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
import Theorems.Thm_GroundTheory_Global_Artin_extendByZero_coe
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
theorem _root_.solution (H D : Subgroup G) [Fintype H] [Fintype D] (x : G) (F : G → ℂ) :
    ∑ h : H, ∑ e : D, F (h * x * e) =
      (Nat.card ((MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D) : ℂ) *
        ∑ u ∈ Finset.univ.filter (fun u ↦ DoubleCoset.mk H D u = DoubleCoset.mk H D x), F u := by
  classical
  set E : Subgroup D := (MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D with hEdef
  have hE : ∀ c : D, c ∈ E ↔ x * c * x⁻¹ ∈ H := fun c ↦ by
    rw [hEdef, Subgroup.mem_subgroupOf, mem_conj_inv_smul_iff]
  have hfib : ∀ u : G, (Finset.univ.filter (fun p : H × D ↦ (p.1 : G) * x * p.2 = u)).card =
      if DoubleCoset.mk H D u = DoubleCoset.mk H D x then Nat.card E else 0 := by
    intro u
    split_ifs with hu
    · obtain ⟨h0, hh0, e0, he0, rfl⟩ := (DoubleCoset.eq H D x u).1 hu.symm
      rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
      refine Finset.card_bij' (fun p _ ↦ ⟨⟨e0 * (p.2 : G)⁻¹, D.mul_mem he0 (D.inv_mem p.2.2)⟩, ?_⟩)
        (fun c _ ↦ (⟨h0 * (x * ((c : D) : G) * x⁻¹), H.mul_mem hh0 ((hE c).1 c.2)⟩,
          ⟨((c : D) : G)⁻¹ * e0, D.mul_mem (D.inv_mem (c : D).2) he0⟩)) ?_ ?_ ?_ ?_
      · rename_i p hp
        rw [Finset.mem_filter] at hp
        rw [hE]
        have hp1 : (p.1 : G) = h0 * x * e0 * (p.2 : G)⁻¹ * x⁻¹ := by
          rw [← hp.2]
          group
        have : x * (e0 * (p.2 : G)⁻¹) * x⁻¹ = h0⁻¹ * p.1 := by
          rw [hp1]
          group
        rw [show ((⟨e0 * (p.2 : G)⁻¹, D.mul_mem he0 (D.inv_mem p.2.2)⟩ : D) : G) =
          e0 * (p.2 : G)⁻¹ from rfl, this]
        exact H.mul_mem (H.inv_mem hh0) p.1.2
      · intro p _
        exact Finset.mem_univ _
      · intro c _
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        group
      · intro p hp
        rw [Finset.mem_filter] at hp
        ext
        · change h0 * (x * (e0 * (p.2 : G)⁻¹) * x⁻¹) = p.1
          have hp1 : (p.1 : G) = h0 * x * e0 * (p.2 : G)⁻¹ * x⁻¹ := by
            rw [← hp.2]
            group
          rw [hp1]
          group
        · change (e0 * (p.2 : G)⁻¹)⁻¹ * e0 = p.2
          group
      · intro c _
        ext
        change e0 * (((c : D) : G)⁻¹ * e0)⁻¹ = ((c : D) : G)
        group
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p _ hp
      apply hu
      exact ((DoubleCoset.eq H D x u).2 ⟨p.1, p.1.2, p.2, p.2.2, hp.symm⟩).symm
  calc ∑ h : H, ∑ e : D, F (h * x * e)
      = ∑ p : H × D, F ((p.1 : G) * x * p.2) := (Fintype.sum_prod_type' _).symm
    _ = ∑ u : G, ∑ p ∈ Finset.univ.filter (fun p : H × D ↦ (p.1 : G) * x * p.2 = u),
          F ((p.1 : G) * x * p.2) :=
        (Finset.sum_fiberwise Finset.univ (fun p : H × D ↦ (p.1 : G) * x * p.2) _).symm
    _ = ∑ u : G, (if DoubleCoset.mk H D u = DoubleCoset.mk H D x then (Nat.card E : ℂ) else 0) *
          F u := by
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        rw [Finset.sum_congr rfl fun p hp ↦ by rw [(Finset.mem_filter.1 hp).2], Finset.sum_const,
          nsmul_eq_mul, hfib u]
        split_ifs <;> simp
    _ = (Nat.card E : ℂ) *
          ∑ u ∈ Finset.univ.filter (fun u ↦ DoubleCoset.mk H D u = DoubleCoset.mk H D x), F u := by
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        split_ifs <;> simp
end GroundTheory.Global.Artin
