-- Prove2me | solution 1 for GroundTheory.LocalField.brauerFun_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:04:23.772404+00:00
-- url     : https://prove2.me/submissions/8fd36b15-5feb-4c45-9fa6-19fc214889ba

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime
import Theorems.Thm_GroundTheory_LocalField_exists_card_centralizer_eq
import Theorems.Thm_GroundTheory_LocalField_card_mul_indFun_theta_of_coprime
import Theorems.Thm_GroundTheory_LocalField_sum_conj_eq_card_centralizer
import Theorems.Thm_GroundTheory_LocalField_sum_conj_eq_zero
import Theorems.Thm_GroundTheory_LocalField_mk_classRep

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
omit hζ hmono
namespace GroundTheory.LocalField
theorem _root_.solution {y : G} (hy : (orderOf y).Coprime p) :
    ∃ m : ℕ, brauerFun p y = m ∧ ¬ p ∣ m := by
  set c0 := ConjClasses.mk y
  set x := classRep c0
  have hxy : IsConj x y := ConjClasses.mk_eq_mk_iff_isConj.mp (mk_classRep c0)
  have hx : (orderOf x).Coprime p := by
    obtain ⟨u, hu⟩ := isConj_iff.mp hxy
    rw [show x = (MulAut.conj u⁻¹) y by rw [MulAut.conj_apply, ← hu]; group, MulEquiv.orderOf_eq]
    exact hy
  obtain ⟨m, hm, hpm⟩ := exists_card_centralizer_eq p x
  refine ⟨m, ?_, hpm⟩
  rw [brauerFun, Finset.sum_apply, Finset.sum_eq_single c0]
  · rw [if_pos hx]
    have h := card_mul_indFun_theta_of_coprime hx hy
    rw [sum_conj_eq_card_centralizer hxy, hm] at h
    have hP : (Nat.card (sylowCent p x) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    push_cast at h
    exact mul_left_cancel₀ hP h
  · intro c _ hc
    split_ifs with hxc
    · have h := card_mul_indFun_theta_of_coprime hxc hy
      have hnc : ¬ IsConj (classRep c) y := by
        intro hcj
        apply hc
        rw [← mk_classRep c]
        exact ConjClasses.mk_eq_mk_iff_isConj.mpr hcj
      rw [sum_conj_eq_zero hnc] at h
      have hP : (Nat.card (sylowCent p (classRep c)) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
      exact (mul_eq_zero.mp h).resolve_left hP
    · simp
  · intro h
    exact absurd (Finset.mem_univ _) h
end GroundTheory.LocalField
