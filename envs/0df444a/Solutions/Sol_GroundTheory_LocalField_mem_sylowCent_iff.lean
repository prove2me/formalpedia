-- Prove2me | solution 1 for GroundTheory.LocalField.mem_sylowCent_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:22.022474+00:00
-- url     : https://prove2.me/submissions/84813de8-6f64-415e-87ec-e41d009904ce

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime
import Theorems.Thm_GroundTheory_LocalField_isPGroup_sylowCent

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
omit [Fintype G]
namespace GroundTheory.LocalField
theorem _root_.solution (hx : (orderOf x).Coprime p) {z : G} (hz : (orderOf z).Coprime p) :
    x⁻¹ * z ∈ sylowCent p x ↔ z = x := by
  constructor
  · intro hw
    have hxw : x * (x⁻¹ * z) = (x⁻¹ * z) * x := (commute_of_mem_sylowCent hw).symm
    have hxz : Commute x z := by
      have h1 : Commute x (x⁻¹ * z) := hxw
      have := (Commute.refl x).mul_right h1
      rwa [mul_inv_cancel_left] at this
    have hcomm : Commute x⁻¹ z := hxz.inv_left
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp (isPGroup_sylowCent p x)) ⟨_, hw⟩
    rw [Subgroup.orderOf_mk] at hj
    have hdvd := hcomm.orderOf_mul_dvd_lcm
    rw [orderOf_inv, hj] at hdvd
    have hcop : (Nat.lcm (orderOf x) (orderOf z)).Coprime p :=
      Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd_mul _ _) (Nat.Coprime.mul_left hx hz)
    have hj0 : j = 0 := by
      by_contra hj0
      have : p ∣ Nat.lcm (orderOf x) (orderOf z) :=
        (dvd_pow_self p hj0).trans hdvd
      exact hp.out.one_lt.ne' ((Nat.coprime_comm.mp hcop).eq_one_of_dvd this)
    rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
    calc z = x * (x⁻¹ * z) := by group
      _ = x := by rw [hj, mul_one]
  · intro h
    rw [h, inv_mul_cancel]
    exact (sylowCent p x).one_mem
end GroundTheory.LocalField
