-- Prove2me | solution 1 for GroundTheory.ProfCoh.mul_inv_mem_of_iterate_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:24:49.911831+00:00
-- url     : https://prove2.me/submissions/807d0539-823c-4a39-8346-72884510d56a

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsPower
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_VanishingUnits
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.LocalField ValuativeRel IsLocalRing
variable {G : Type*} [CommGroup G]
namespace GroundTheory.ProfCoh
theorem _root_.solution {l m : ℕ} (P O : Subgroup G) (s : G →* G)
    (hPl : ∀ y : G, y ^ l ∈ P) (hO : ∀ x : G, s x * x⁻¹ ∈ O)
    (hOP : ∀ e ∈ O, s e * e⁻¹ ∈ P) (hm : m.Coprime l) (hsm : ∀ x : G, s^[m] x = x) (x : G) :
    s x * x⁻¹ ∈ P := by
  have hPn : P.Normal := Subgroup.normal_of_isMulCommutative P
  have hq : ∀ a b : G, a * b⁻¹ ∈ P → (a : G ⧸ P) = b := fun a b h => by
    rw [QuotientGroup.eq]
    have := P.inv_mem h
    rwa [mul_inv_rev, inv_inv, mul_comm] at this
  set c := s x * x⁻¹ with hc
  have hOs : ∀ e ∈ O, s e ∈ O := fun e he => by
    have := O.mul_mem (hO e) he
    rwa [inv_mul_cancel_right] at this
  have hcO : ∀ j : ℕ, s^[j] c ∈ O := fun j => by
    induction j with
    | zero => exact hO x
    | succ j ih => rw [Function.iterate_succ_apply']; exact hOs _ ih
  have hcj : ∀ j : ℕ, ((s^[j] c : G) : G ⧸ P) = c := fun j => by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', hq _ _ (hOP _ (hcO j)), ih]
  have hsx : s x = x * c := by rw [hc, mul_comm (s x), mul_inv_cancel_left]
  have hxj : ∀ j : ℕ, ((s^[j] x : G) : G ⧸ P) = (x : G ⧸ P) * (c : G ⧸ P) ^ j := fun j => by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply, hsx, iterate_map_mul, QuotientGroup.mk_mul, ih,
        hcj, pow_succ, mul_assoc]
  have h1 : (c : G ⧸ P) ^ m = 1 := by
    have h := hxj m
    rw [hsm] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)
  have h2 : (c : G ⧸ P) ^ l = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hPl c
  have h3 : (c : G ⧸ P) = 1 := by
    have h := (pow_gcd_eq_one (a := (c : G ⧸ P))).2 ⟨h1, h2⟩
    rwa [Nat.Coprime.gcd_eq_one hm, pow_one] at h
  exact (QuotientGroup.eq_one_iff c).1 h3
end GroundTheory.ProfCoh
