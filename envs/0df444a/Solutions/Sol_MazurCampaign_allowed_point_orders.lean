-- Prove2me | solution 1 for MazurCampaign.allowed_point_orders
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T09:00:58.589283+00:00
-- url     : https://prove2.me/submissions/1b11ed0f-6dc2-4252-ad62-3488cf9f40d5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints
import Theorems.Thm_MazurCampaign_no_prime_ge_seventeen
import Theorems.Thm_MazurCampaign_no_order_eleven
import Theorems.Thm_MazurCampaign_no_order_thirteen
import Theorems.Thm_MazurCampaign_no_order_twenty_five
import Theorems.Thm_MazurCampaign_no_order_thirty_five
import Theorems.Thm_MazurCampaign_nine_composite_exclusions
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Reduction of rational point orders

This file isolates the elementary divisor argument behind the point-order part of Mazur's
theorem. If a positive integer is not one of

`1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12`,

then it has either a prime divisor at least `11` or one of the eleven minimal composite
forbidden divisors

`14, 15, 16, 18, 20, 21, 24, 25, 27, 35, 49`.

For an element of finite additive order, multiplication by the complementary quotient extracts
an element having exactly any prescribed positive divisor of its order. Consequently, excluding
large prime orders and these eleven composite orders is enough to prove the point-order theorem.
-/

namespace MazurTorsion

def cyclicOrders : Finset ℕ :=
  {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12}

/-- The minimal composite orders outside Mazur's cyclic list. -/
def kubertForbiddenOrders : Finset ℕ :=
  {14, 15, 16, 18, 20, 21, 24, 25, 27, 35, 49}

private def excludedProperDivisors (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun d ↦ (d : ℕ) ∣ n ∧ (d : ℕ) ∉ cyclicOrders

private def IsMinimalExcludedOrder (n : ℕ) : Prop :=
  n ∉ cyclicOrders ∧ excludedProperDivisors n = ∅

private instance (n : ℕ) : Decidable (IsMinimalExcludedOrder n) := by
  unfold IsMinimalExcludedOrder
  infer_instance

private lemma mem_cyclicOrders_le_twelve {n : ℕ} (hn : n ∈ cyclicOrders) :
    n ≤ 12 := by
  simp only [cyclicOrders, Finset.mem_insert, Finset.mem_singleton] at hn
  omega

private lemma finite_minimal_excluded_classification
    (n : Fin 145) (hnpos : 0 < (n : ℕ)) (hnprime : ¬(n : ℕ).Prime)
    (hn : IsMinimalExcludedOrder n) :
    (n : ℕ) ∈ kubertForbiddenOrders := by
  fin_cases n <;> revert hnpos hnprime hn <;> decide

/-- Every positive order outside Mazur's cyclic list has either a large prime divisor or one of
Kubert's eleven minimal composite forbidden divisors. -/
theorem exists_prime_or_kubertForbiddenOrder_dvd
    {n : ℕ} (hnpos : 0 < n) (hn : n ∉ cyclicOrders) :
    (∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ p ∣ n) ∨
      ∃ d ∈ kubertForbiddenOrders, d ∣ n := by
  classical
  let P : ℕ → Prop := fun d ↦ d ∣ n ∧ d ∉ cyclicOrders
  have hP : ∃ d, P d := ⟨n, dvd_rfl, hn⟩
  let d := Nat.find hP
  have hdP : P d := Nat.find_spec hP
  have hddiv : d ∣ n := hdP.1
  have hdnot : d ∉ cyclicOrders := hdP.2
  have hdpos : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    rw [hd0] at hddiv
    exact hnpos.ne' (zero_dvd_iff.mp hddiv)
  have hdminimal :
      ∀ e : ℕ, e ∣ d → e < d → e ∈ cyclicOrders := by
    intro e hediv helt
    by_contra henot
    have hedivn : e ∣ n := hediv.trans hddiv
    have hle : d ≤ e := Nat.find_min' hP ⟨hedivn, henot⟩
    omega
  by_cases hdprime : d.Prime
  · left
    refine ⟨d, hdprime, ?_, hddiv⟩
    by_contra h
    have hdlt : d < 11 := by omega
    interval_cases d <;> norm_num [cyclicOrders] at hdnot
  · right
    have hd2 : 2 ≤ d := by
      by_contra h
      have hd1 : d = 1 := by omega
      apply hdnot
      simp [hd1, cyclicOrders]
    obtain ⟨a, b, halt, hblt, hab⟩ :=
      (Nat.not_prime_iff_exists_mul_eq hd2).mp hdprime
    have ha0 : a ≠ 0 := by
      intro ha
      subst a
      simp at hab
      omega
    have hb0 : b ≠ 0 := by
      intro hb
      subst b
      simp at hab
      omega
    have hadvd : a ∣ d := ⟨b, hab.symm⟩
    have hbdvd : b ∣ d := ⟨a, by simpa [Nat.mul_comm] using hab.symm⟩
    have hain : a ∈ cyclicOrders := hdminimal a hadvd halt
    have hbin : b ∈ cyclicOrders := hdminimal b hbdvd hblt
    have hale : a ≤ 12 := mem_cyclicOrders_le_twelve hain
    have hble : b ≤ 12 := mem_cyclicOrders_le_twelve hbin
    have hdle : d < 145 := by
      nlinarith
    let d' : Fin 145 := ⟨d, hdle⟩
    have hd'minimal : IsMinimalExcludedOrder d' := by
      constructor
      · exact hdnot
      · apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e he
        simp only [excludedProperDivisors, Finset.mem_filter, Finset.mem_univ,
          true_and] at he
        exact he.2 (hdminimal e he.1 e.isLt)
    exact ⟨d, finite_minimal_excluded_classification d' hdpos hdprime hd'minimal, hddiv⟩

/-- If all large prime orders and the eleven minimal composite orders are absent, every element
of finite additive order has order in Mazur's cyclic list. -/
theorem addOrderOf_mem_cyclicOrders_of_order_obstructions
    {G : Type*} [AddGroup G] (x : G) (hx : IsOfFinAddOrder x)
    (hprime :
      ∀ (p : ℕ), p.Prime → 11 ≤ p → ∀ y : G, addOrderOf y ≠ p)
    (hkubert :
      ∀ d ∈ kubertForbiddenOrders, ∀ y : G, addOrderOf y ≠ d) :
    addOrderOf x ∈ cyclicOrders := by
  by_contra hxnot
  have hxpos : 0 < addOrderOf x := hx.addOrderOf_pos
  rcases exists_prime_or_kubertForbiddenOrder_dvd hxpos hxnot with
      ⟨p, hpprime, hp11, hpdvd⟩ | ⟨d, hdmem, hddvd⟩
  · apply hprime p hpprime hp11 ((addOrderOf x / p) • x)
    rw [hx.addOrderOf_nsmul, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hpdvd),
      Nat.div_div_self hpdvd hxpos.ne']
  · apply hkubert d hdmem ((addOrderOf x / d) • x)
    rw [hx.addOrderOf_nsmul, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hddvd),
      Nat.div_div_self hddvd hxpos.ne']

end MazurTorsion

theorem torsion_solution (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ∈ MazurCampaign.cyclicOrders := by
  intro x
  have hx : IsOfFinAddOrder x := by
    obtain ⟨n, hn, hnx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp x.property
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, Subtype.ext hnx⟩
  apply MazurTorsion.addOrderOf_mem_cyclicOrders_of_order_obstructions x hx
  · intro p hp hple y
    by_cases hp17 : 17 ≤ p
    · exact MazurCampaign.no_prime_ge_seventeen E p hp hp17 y
    · have hpCases : p = 11 ∨ p = 13 := by
        interval_cases p <;> norm_num at *
      rcases hpCases with rfl | rfl
      · exact MazurCampaign.no_order_eleven E y
      · exact MazurCampaign.no_order_thirteen E y
  · intro d hd y
    by_cases hd25 : d = 25
    · subst d
      exact MazurCampaign.no_order_twenty_five E y
    by_cases hd35 : d = 35
    · subst d
      exact MazurCampaign.no_order_thirty_five E y
    apply MazurCampaign.nine_composite_exclusions E d _ y
    simpa [MazurTorsion.kubertForbiddenOrders, hd25, hd35] using hd

open WeierstrassCurve WeierstrassCurve.Affine

theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : IsOfFinAddOrder P) :
    addOrderOf P ∈ MazurCampaign.cyclicOrders := by
  let x : MazurCampaign.RationalTorsion E := ⟨P, hP⟩
  have horder : addOrderOf (x : (E⁄ℚ).Point) = addOrderOf x :=
    addOrderOf_injective (AddCommGroup.torsion (E⁄ℚ).Point).subtype
      (AddCommGroup.torsion (E⁄ℚ).Point).subtype_injective x
  change addOrderOf (x : (E⁄ℚ).Point) ∈ MazurCampaign.cyclicOrders
  rw [horder]
  exact torsion_solution E x

example : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (P : (E⁄ℚ).Point),
    IsOfFinAddOrder P → addOrderOf P ∈ MazurCampaign.cyclicOrders := solution

#print axioms solution
