-- Prove2me | solution 1 for GroundTheory.LocalField.not_dvd_brauerFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:27:28.143826+00:00
-- url     : https://prove2.me/submissions/ed2328b8-be77-41dd-991e-230d5a8dbe0a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime
import Theorems.Thm_GroundTheory_LocalField_brauerFun_mem_spanA
import Theorems.Thm_GroundTheory_LocalField_exists_int_brauerFun
import Theorems.Thm_GroundTheory_LocalField_brauerFun_of_coprime
import Theorems.Thm_GroundTheory_LocalField_exists_zpow_mul_zpow_eq
import Theorems.Thm_GroundTheory_LocalField_int_modEq_of_mem_spanA


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
variable {G : Type u} [Group G]
variable [Fintype G] (p : ℕ) [hp : Fact p.Prime] (x : G)
variable {p x}
variable {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))
  (hmono : ∀ K : Subgroup G, IsElementaryAt p K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
include hζ hmono
namespace GroundTheory.LocalField
theorem _root_.solution (s : G) : ∃ k : ℤ, brauerFun p s = k ∧ ¬ (p : ℤ) ∣ k := by
  obtain ⟨a, b, hab, ha, hb⟩ := exists_zpow_mul_zpow_eq hp.out s
  obtain ⟨k, hk⟩ := exists_int_brauerFun hζ hmono s
  obtain ⟨m, hm, hpm⟩ := brauerFun_of_coprime ha
  refine ⟨k, hk, fun hdiv ↦ hpm ?_⟩
  have hcong := int_modEq_of_mem_spanA hζ hp.out hab hb (brauerFun_mem_spanA hζ hmono) hk
    (v := (m : ℤ)) (by rw [hm]; push_cast; rfl)
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd k p).mpr hdiv] at hcong
  have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (m : ℤ) p).mp hcong.symm
  exact Int.natCast_dvd_natCast.mp h0
end GroundTheory.LocalField
