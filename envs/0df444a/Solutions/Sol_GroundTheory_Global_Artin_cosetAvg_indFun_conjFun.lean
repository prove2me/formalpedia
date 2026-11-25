-- Prove2me | solution 1 for GroundTheory.Global.Artin.cosetAvg_indFun_conjFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:59.218825+00:00
-- url     : https://prove2.me/submissions/d9066cdc-c817-4ec3-9bbd-c2644d83a358

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
import Definitions.Def_GroundTheory_GlobalFields_Artin_MackeyFrobenius
import Theorems.Thm_GroundTheory_Global_Artin_zpow_inv_mul_zpow_mem
import Theorems.Thm_GroundTheory_Global_Artin_zpow_mem_iff_relIndex_dvd
import Theorems.Thm_GroundTheory_Global_Artin_sum_conj_eq_sum_subgroupOf
import Theorems.Thm_GroundTheory_Global_Artin_sum_conj_coset
import Theorems.Thm_GroundTheory_Global_Artin_card_mul_card_eq
import Theorems.Thm_GroundTheory_Global_Artin_extendByZero_coe
import Theorems.Thm_GroundTheory_Global_Artin_extendByZero_conjFun
import Theorems.Thm_GroundTheory_Global_Artin_extendByZero_of_notMem
import Theorems.Thm_GroundTheory_Global_Artin_indFun_subtype_apply
import Theorems.Thm_GroundTheory_GroupCoh_doubleCosetMap_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Artin.extendByZero_coe
attribute [local simp] GroundTheory.GroupCoh.doubleCosetMap_mk



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
open GroundTheory.LocalField
variable {G : Type*} [Group G] [Fintype G] {H D I : Subgroup G}
open Classical
namespace GroundTheory.Global.Artin
theorem _root_.solution [Fintype H] [Fintype D] [Fintype I] (hID : I ≤ D)
    [(I.subgroupOf D).Normal] {φ : G} (hφ : φ ∈ D)
    (hgen : Subgroup.zpowers ((⟨φ, hφ⟩ : D) : D ⧸ I.subgroupOf D) = ⊤) (f : H → ℂ) (x : G)
    (φx : H) (hφx : ∃ i ∈ (MulAut.conj x • I : Subgroup G),
      (φx : G) = x * φ ^ (frobIndex H D I x : ℤ) * x⁻¹ * i) (m : ℤ) :
    (Nat.card I : ℂ)⁻¹ * ∑ i : I,
        indFun ((MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D).subtype (conjFun H D x f)
          ⟨φ ^ m * i, D.mul_mem (D.zpow_mem hφ m) (hID i.2)⟩ =
      if (frobIndex H D I x : ℤ) ∣ m then
        (frobIndex H D I x : ℂ) *
          cosetAvg ((MulAut.conj x • I : Subgroup G).subgroupOf H) φx f (m / frobIndex H D I x)
      else 0 := by
  classical
  set K : Subgroup G := I ⊔ ((MulAut.conj x⁻¹ • H : Subgroup G) ⊓ D) with hK
  have hIK : I ≤ K := le_sup_left
  have hKr : ∀ n : ℤ, φ ^ n ∈ K ↔ (frobIndex H D I x : ℤ) ∣ n :=
    zpow_mem_iff_relIndex_dvd hφ hgen hIK
  simp_rw [indFun_subtype_apply, extendByZero_conjFun]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hA : ∀ t : D, ∑ i : I, extendByZero H f (x * ((t : G)⁻¹ * (φ ^ m * i) * t) * x⁻¹) =
      ∑ i : I, extendByZero H f (x * (φ ^ m * i) * x⁻¹) := fun t ↦
    sum_conj_coset hID hφ hgen t.2 (fun g ↦ extendByZero H f (x * g * x⁻¹)) m
  simp_rw [hA]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  have hcount := card_mul_card_eq (H := H) hID x
  have hI0 : (Nat.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hE0 : (Nat.card ((MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hIx0 : (Nat.card ((MulAut.conj x • I : Subgroup G).subgroupOf H) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 Nat.card_pos.ne'
  split_ifs with hdiv
  · obtain ⟨k, hk⟩ := hdiv
    have hr0 : (frobIndex H D I x : ℤ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hk
      have h1 : (frobIndex H D I x : ℤ) ∣ 0 := dvd_zero _
      rw [← hKr, zpow_zero] at h1
      rw [Nat.cast_eq_zero] at h0
      have := (Subgroup.card_mul_index ((I ⊔ ((MulAut.conj x⁻¹ • H : Subgroup G) ⊓ D)).subgroupOf
        D))
      rw [← Subgroup.relIndex, ← frobIndex, h0, mul_zero] at this
      exact Nat.card_pos.ne' this.symm
    rw [hk, Int.mul_ediv_cancel_left _ hr0]
    obtain ⟨i0, hi0, hφxeq⟩ := hφx
    obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = x⁻¹ * (φx : G) * x := ⟨_, rfl⟩
    have hj0 : (φ ^ (frobIndex H D I x : ℤ))⁻¹ * ψ ∈ I := by
      rw [show (φ ^ (frobIndex H D I x : ℤ))⁻¹ * ψ = x⁻¹ * i0 * x by rw [hψ, hφxeq]; group]
      exact (mem_conj_smul_iff I x i0).1 hi0
    have hψD : ψ ∈ D := by
      have := D.mul_mem (D.zpow_mem hφ (frobIndex H D I x : ℤ)) (hID hj0)
      simpa using this
    have hi1 : (ψ ^ k)⁻¹ * φ ^ ((frobIndex H D I x : ℤ) * k) ∈ I := by
      have h1 : ψ⁻¹ * φ ^ (frobIndex H D I x : ℤ) ∈ I := by simpa using I.inv_mem hj0
      have := zpow_inv_mul_zpow_mem hψD (D.zpow_mem hφ (frobIndex H D I x : ℤ)) h1 k
      rwa [← zpow_mul] at this
    have hψk : ψ ^ k = x⁻¹ * (φx : G) ^ k * x := by
      have := conj_zpow (i := k) (a := x⁻¹) (b := (φx : G))
      rw [inv_inv] at this
      rw [hψ, this]
    have hS : ∑ i : I, extendByZero H f (x * (φ ^ ((frobIndex H D I x : ℤ) * k) * i) * x⁻¹) =
        ∑ i : I, extendByZero H f (x * (ψ ^ k * i) * x⁻¹) :=
      Fintype.sum_equiv (Equiv.mulLeft (⟨_, hi1⟩ : I)) _ _ fun i ↦ by
        congr 1
        simp only [Equiv.coe_mulLeft, Subgroup.coe_mul]
        group
    have hS2 : ∑ i : I, extendByZero H f (x * (ψ ^ k * i) * x⁻¹) =
        ∑ i : I, (fun g ↦ extendByZero H f ((φx : G) ^ k * g)) (x * i * x⁻¹) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only
      rw [hψk]
      congr 1
      group
    have hF : ∀ g ∉ H, (fun g ↦ extendByZero H f ((φx : G) ^ k * g)) g = 0 := fun g hg ↦
      extendByZero_of_notMem H f fun hm ↦ hg (by
        have := H.mul_mem (H.inv_mem (H.zpow_mem φx.2 k)) hm
        simpa using this)
    have hS3 : ∑ j : (MulAut.conj x • I : Subgroup G).subgroupOf H,
        (fun g ↦ extendByZero H f ((φx : G) ^ k * g)) ((j : H) : G) =
        ∑ j : (MulAut.conj x • I : Subgroup G).subgroupOf H, f (φx ^ k * j) :=
      Finset.sum_congr rfl fun j _ ↦ by
        simp only
        rw [show (φx : G) ^ k * ((j : H) : G) = ((φx ^ k * (j : H) : H) : G) by simp,
          extendByZero_coe]
    rw [hS, hS2, sum_conj_eq_sum_subgroupOf H I x _ hF, hS3, cosetAvg]
    have hc : (Nat.card D : ℂ) * Nat.card ((MulAut.conj x • I : Subgroup G).subgroupOf H) =
        frobIndex H D I x * Nat.card I *
          Nat.card ((MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D) := by
      exact_mod_cast hcount
    field_simp
    linear_combination (∑ j : (MulAut.conj x • I : Subgroup G).subgroupOf H, f (φx ^ k * j)) * hc
  · have h0 : ∀ i : I, extendByZero H f (x * (φ ^ m * i) * x⁻¹) = 0 := fun i ↦
      extendByZero_of_notMem H f fun hm ↦ hdiv ((hKr m).1 (by
        have h1 : φ ^ m * i ∈ K := Subgroup.mem_sup_right (Subgroup.mem_inf.2
          ⟨(mem_conj_inv_smul_iff H x _).2 hm, D.mul_mem (D.zpow_mem hφ m) (hID i.2)⟩)
        have := K.mul_mem h1 (hIK (I.inv_mem i.2))
        simpa using this))
    simp [h0]
end GroundTheory.Global.Artin
