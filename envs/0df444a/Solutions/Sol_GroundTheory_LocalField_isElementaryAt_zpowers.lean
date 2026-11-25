-- Prove2me | solution 1 for GroundTheory.LocalField.isElementaryAt_zpowers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:13:32.954689+00:00
-- url     : https://prove2.me/submissions/9a4b5a0b-703d-4ed6-bf3e-ed438daf7154

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary
import Theorems.Thm_GroundTheory_LocalField_exists_zpow_mul_zpow_eq

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
theorem _root_.solution (hp : p.Prime) (s : G) : IsElementaryAt p (Subgroup.zpowers s) := by
  obtain ⟨a, b, hab, ha, hb⟩ := exists_zpow_mul_zpow_eq hp s
  refine ⟨Subgroup.zpowers (s ^ a), Subgroup.zpowers (s ^ b), ?_, ?_, inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.zpowers_le]
    exact Subgroup.zpow_mem_zpowers s a
  · rw [Subgroup.zpowers_le]
    exact Subgroup.zpow_mem_zpowers s b
  · rwa [Nat.card_zpowers]
  · intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨(orderOf s).factorization p, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]
  · intro c hc y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_mul, ← zpow_mul, ← zpow_add, ← zpow_add, add_comm]
  · intro h hh
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    refine ⟨(s ^ a) ^ m, Subgroup.zpow_mem_zpowers _ m, (s ^ b) ^ m, Subgroup.zpow_mem_zpowers _ m, ?_⟩
    have hab' : s ^ (a + b) = s := by rw [zpow_add, hab]
    rw [← zpow_mul, ← zpow_mul, ← zpow_add, ← add_mul, zpow_mul, hab']
end GroundTheory.LocalField
