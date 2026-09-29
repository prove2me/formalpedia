-- Prove2me | solution 1 for HeckeIntegralSeam.exists_isHeckeCosetSystem_and_isHeckeCosetSystem_mul_inv_of_conj_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4000b4c3-04b4-5851-aa98-446e5d3c0d12

import Mathlib
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeIntegralSeam_exists_isHeckeCosetSystem_and_isHeckeCosetSystem_mul_inv_of_conj_eq

set_option autoImplicit false

namespace R1LtCommonTransversal

open HeckeIntegralSeam

variable {G : Type*} [Group G] {U : Subgroup G} {g w z : G}

theorem mul_inv_mem_doubleCoset (hw : w ∈ U) (hz : z ∈ Subgroup.center G)
    (hconj : w * g * w⁻¹ = z * g⁻¹) {x : G} (hx : x ∈ HeckePair.doubleCoset U g) :
    z * x⁻¹ ∈ HeckePair.doubleCoset U g := by
  have hzc : ∀ y : G, y * z = z * y := fun y => Subgroup.mem_center_iff.mp hz y
  obtain ⟨a, ha, b, hb, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  refine HeckePair.mem_doubleCoset_iff.mpr ⟨b⁻¹ * w, U.mul_mem (U.inv_mem hb) hw,
    w⁻¹ * a⁻¹, U.mul_mem (U.inv_mem hw) (U.inv_mem ha), ?_⟩
  calc b⁻¹ * w * g * (w⁻¹ * a⁻¹) = b⁻¹ * (w * g * w⁻¹) * a⁻¹ := by simp only [mul_assoc]
    _ = b⁻¹ * (z * g⁻¹) * a⁻¹ := by rw [hconj]
    _ = (b⁻¹ * z) * g⁻¹ * a⁻¹ := by simp only [mul_assoc]
    _ = (z * b⁻¹) * g⁻¹ * a⁻¹ := by rw [hzc]
    _ = z * (a * g * b)⁻¹ := by simp only [mul_inv_rev, mul_assoc]

theorem exists_eq_mul_mul_of_mem_doubleCoset {r t : G}
    (hr : r ∈ HeckePair.doubleCoset U g) (ht : t ∈ HeckePair.doubleCoset U g) :
    ∃ u₁ ∈ U, ∃ u₂ ∈ U, u₁ * t * u₂ = r := by
  obtain ⟨a, ha, b, hb, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hr
  obtain ⟨c, hc, d, hd, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp ht
  refine ⟨a * c⁻¹, U.mul_mem ha (U.inv_mem hc), d⁻¹ * b, U.mul_mem (U.inv_mem hd) hb, ?_⟩
  calc a * c⁻¹ * (c * g * d) * (d⁻¹ * b) = a * (c⁻¹ * c) * g * (d * d⁻¹) * b := by
        simp only [mul_assoc]
    _ = a * g * b := by rw [inv_mul_cancel, mul_inv_cancel, mul_one, mul_one]

variable {ι : Type*} {reps : ι → G}

theorem exists_isHeckeCosetSystem_and_isHeckeCosetSystem_mul_inv
    (hsys : IsHeckeCosetSystem U g reps) (hw : w ∈ U) (hz : z ∈ Subgroup.center G)
    (hconj : w * g * w⁻¹ = z * g⁻¹) :
    ∃ ε : ι → G, IsHeckeCosetSystem U g ε ∧
      (∀ i, (QuotientGroup.mk (ε i) : G ⧸ U) = QuotientGroup.mk (reps i)) ∧
      IsHeckeCosetSystem U g (fun i => z * (ε i)⁻¹) := by
  have hzc : ∀ y : G, y * z = z * y := fun y => Subgroup.mem_center_iff.mp hz y
  have hzc' : ∀ y : G, y * z⁻¹ = z⁻¹ * y := fun y =>
    Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hz) y

  obtain ⟨t, ht⟩ : ∃ t : ι → G, ∀ i, t i = z * (reps i)⁻¹ := ⟨_, fun _ => rfl⟩
  have ht_mem : ∀ i, t i ∈ HeckePair.doubleCoset U g := fun i => by
    rw [ht]; exact mul_inv_mem_doubleCoset hw hz hconj (hsys.mem_doubleCoset i)

  have ht_inj : ∀ i j, t i * (t j)⁻¹ ∈ U → i = j := by
    intro i j hij
    apply hsys.mk_injective
    rw [QuotientGroup.eq]
    have : t i * (t j)⁻¹ = (reps i)⁻¹ * reps j := by
      rw [ht, ht]
      calc z * (reps i)⁻¹ * (z * (reps j)⁻¹)⁻¹ = z * (reps i)⁻¹ * (reps j * z⁻¹) := by
            rw [mul_inv_rev, inv_inv]
        _ = z * (reps i)⁻¹ * (z⁻¹ * reps j) := by rw [hzc']
        _ = z * ((reps i)⁻¹ * z⁻¹) * reps j := by simp only [mul_assoc]
        _ = (z * z⁻¹) * ((reps i)⁻¹ * reps j) := by rw [hzc']; simp only [mul_assoc]
        _ = (reps i)⁻¹ * reps j := by rw [mul_inv_cancel, one_mul]
    rwa [this] at hij

  have ht_cov : ∀ x ∈ HeckePair.doubleCoset U g, ∃ i, x * (t i)⁻¹ ∈ U := by
    intro x hx
    obtain ⟨i, hi⟩ := hsys.covers _ (mul_inv_mem_doubleCoset hw hz hconj hx)
    refine ⟨i, ?_⟩
    rw [QuotientGroup.eq] at hi

    have : x * (t i)⁻¹ = (z * x⁻¹)⁻¹ * reps i := by
      rw [ht, mul_inv_rev, inv_inv, mul_inv_rev, inv_inv, hzc', mul_assoc]
    rw [this]; exact hi

  have hcommon : ∀ i, ∃ e : G, (∃ u ∈ U, e = reps i * u) ∧ (∃ u ∈ U, e = u * t i) := by
    intro i
    obtain ⟨u₁, hu₁, u₂, hu₂, h⟩ :=
      exists_eq_mul_mul_of_mem_doubleCoset (hsys.mem_doubleCoset i) (ht_mem i)
    refine ⟨u₁ * t i, ⟨u₂⁻¹, U.inv_mem hu₂, ?_⟩, ⟨u₁, hu₁, rfl⟩⟩
    rw [← h, mul_assoc (u₁ * t i), mul_inv_cancel, mul_one]
  choose ε hεl hεr using hcommon
  have hε_left : ∀ i, (QuotientGroup.mk (ε i) : G ⧸ U) = QuotientGroup.mk (reps i) := by
    intro i
    obtain ⟨u, hu, hue⟩ := hεl i
    rw [QuotientGroup.eq, hue, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    exact U.inv_mem hu
  have hε_right : ∀ i, ε i * (t i)⁻¹ ∈ U := by
    intro i
    obtain ⟨u, hu, hue⟩ := hεr i
    rw [hue, mul_assoc, mul_inv_cancel, mul_one]; exact hu
  have hε_mem : ∀ i, ε i ∈ HeckePair.doubleCoset U g := by
    intro i
    obtain ⟨u, hu, hue⟩ := hεl i
    rw [hue]; exact HeckePair.doubleCoset_mul_mem (hsys.mem_doubleCoset i) hu
  refine ⟨ε, ⟨hε_mem, fun x hx => ?_, fun i j hij => ?_⟩, hε_left, ⟨fun i => ?_, fun x hx => ?_,
    fun i j hij => ?_⟩⟩
  · obtain ⟨i, hi⟩ := hsys.covers x hx
    exact ⟨i, hi.trans (hε_left i).symm⟩
  · exact hsys.mk_injective ((hε_left i).symm.trans ((show _ = _ from hij).trans (hε_left j)))
  · exact mul_inv_mem_doubleCoset hw hz hconj (hε_mem i)
  ·
    obtain ⟨i, hi⟩ := ht_cov _ (mul_inv_mem_doubleCoset hw hz hconj hx)
    refine ⟨i, ?_⟩
    rw [QuotientGroup.eq]
    have h1 : z * x⁻¹ * (t i)⁻¹ * (ε i * (t i)⁻¹)⁻¹ ∈ U := U.mul_mem hi (U.inv_mem (hε_right i))
    have h2 : z * x⁻¹ * (t i)⁻¹ * (ε i * (t i)⁻¹)⁻¹ = x⁻¹ * (z * (ε i)⁻¹) := by
      calc z * x⁻¹ * (t i)⁻¹ * (ε i * (t i)⁻¹)⁻¹ = z * x⁻¹ * ((t i)⁻¹ * (t i)) * (ε i)⁻¹ := by
            simp only [mul_inv_rev, inv_inv, mul_assoc]
        _ = z * x⁻¹ * (ε i)⁻¹ := by rw [inv_mul_cancel, mul_one]
        _ = x⁻¹ * z * (ε i)⁻¹ := by rw [← hzc x⁻¹]
        _ = x⁻¹ * (z * (ε i)⁻¹) := mul_assoc _ _ _
    rw [h2] at h1; exact h1
  ·
    have hij' : (z * (ε i)⁻¹)⁻¹ * (z * (ε j)⁻¹) ∈ U := QuotientGroup.eq.mp hij
    have h2 : ε i * (ε j)⁻¹ ∈ U := by
      have : (z * (ε i)⁻¹)⁻¹ * (z * (ε j)⁻¹) = ε i * (ε j)⁻¹ := by
        simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
      rwa [this] at hij'
    apply ht_inj
    have h3 := U.mul_mem (U.mul_mem (U.inv_mem (hε_right i)) h2) (hε_right j)
    have h4 : (ε i * (t i)⁻¹)⁻¹ * (ε i * (ε j)⁻¹) * (ε j * (t j)⁻¹) = t i * (t j)⁻¹ := by
      simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
    rwa [h4] at h3

end R1LtCommonTransversal

open R1LtCommonTransversal HeckeIntegralSeam in
theorem solution
    {G : Type*} [Group G] {U : Subgroup G} {g w z : G} {ι : Type*} {reps : ι → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g reps) (hw : w ∈ U)
    (hz : z ∈ Subgroup.center G) (hconj : w * g * w⁻¹ = z * g⁻¹) :
    ∃ ε : ι → G, HeckeIntegralSeam.IsHeckeCosetSystem U g ε ∧
      (∀ i, (QuotientGroup.mk (ε i) : G ⧸ U) = QuotientGroup.mk (reps i)) ∧
      HeckeIntegralSeam.IsHeckeCosetSystem U g (fun i => z * (ε i)⁻¹) :=
  exists_isHeckeCosetSystem_and_isHeckeCosetSystem_mul_inv hsys hw hz hconj

end S_HeckeIntegralSeam_exists_isHeckeCosetSystem_and_isHeckeCosetSystem_mul_inv_of_conj_eq
end P2MW
export P2MW.S_HeckeIntegralSeam_exists_isHeckeCosetSystem_and_isHeckeCosetSystem_mul_inv_of_conj_eq (solution)
