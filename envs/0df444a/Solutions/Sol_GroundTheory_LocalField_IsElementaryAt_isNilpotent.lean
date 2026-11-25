-- Prove2me | solution 1 for GroundTheory.LocalField.IsElementaryAt.isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:12:53.756392+00:00
-- url     : https://prove2.me/submissions/fc592e3a-a27e-448f-b59f-a5593fe6cb40

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary

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
variable {G : Type*} [Group G]
variable [Finite G] {p : ℕ}
namespace GroundTheory.LocalField
namespace IsElementaryAt
theorem _root_.solution (hp : p.Prime) {H : Subgroup G} (hH : IsElementaryAt p H) :
    Group.IsNilpotent H := by
  obtain ⟨C, P, hCH, hPH, hC, hCp, hP, hcomm, hdec⟩ := hH
  have : Fact p.Prime := ⟨hp⟩
  let C' : Subgroup H := C.subgroupOf H
  have hCcomm : ∀ c ∈ C, ∀ c' ∈ C, c * c' = c' * c := by
    intro c hc c' hc'
    have := hC.commGroup.mul_comm ⟨c, hc⟩ ⟨c', hc'⟩
    exact congrArg Subtype.val this
  have hcent : C' ≤ Subgroup.center H := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro h
    obtain ⟨c0, hc0, y0, hy0, hh⟩ := hdec h h.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hh]
    have hc' : (c : G) ∈ C := hc
    have key : (c : G) * (c0 * y0) = (c0 * y0) * c := by
      rw [← mul_assoc, hCcomm c hc' c0 hc0, mul_assoc, hcomm c hc' y0 hy0, mul_assoc]
    first
    | exact key
    | exact key.symm
  have hnorm : C'.Normal := ⟨fun n hn g ↦ by
    have := Subgroup.mem_center_iff.mp (hcent hn) g
    rw [this, mul_inv_cancel_right]
    exact hn⟩
  have hQ : IsPGroup p (H ⧸ C') := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨c0, hc0, y0, hy0, hh⟩ := hdec h h.2
    obtain ⟨j, hj⟩ := hP ⟨y0, hy0⟩
    refine ⟨j, ?_⟩
    have hyj : y0 ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hmk : (QuotientGroup.mk h : H ⧸ C') = QuotientGroup.mk ⟨y0, hPH hy0⟩ := by
      rw [QuotientGroup.eq]
      change ((h⁻¹ * ⟨y0, hPH hy0⟩ : H) : G) ∈ C
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hh, mul_inv_rev, mul_assoc, hcomm _ (C.inv_mem hc0) y0 hy0, inv_mul_cancel_left]
      exact C.inv_mem hc0
    rw [hmk, ← QuotientGroup.mk_pow]
    have : (⟨y0, hPH hy0⟩ : H) ^ p ^ j = 1 := Subtype.ext (by simpa using hyj)
    rw [this, QuotientGroup.mk_one]
  have hnil : Group.IsNilpotent (H ⧸ C') := hQ.isNilpotent
  exact Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' C')
    (by rw [QuotientGroup.ker_mk']; exact hcent)
end IsElementaryAt
end GroundTheory.LocalField
