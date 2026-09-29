-- Prove2me | solution 1 for ModularCurve.coeff_slotSubst_tateUnivX_eq_zero_of_lt_min_and_coeff_eq_and_order_eq_min
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/56794b9d-e90f-5d06-837d-7687885bca82

import Definitions.Def_ModularCurve_TateSlots
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivX
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeff_slotSubst_tateUnivX_eq_zero_of_lt_min_and_coeff_eq_and_order_eq_min

set_option autoImplicit false

namespace SlotOrdSol

open ModularCurve

variable {K : Type*} [CommRing K]

theorem upper_ne (p j n M e : ℕ) (hn : n < p) (hM : M ≠ 0) : n ≠ p * M + j * e := by
  have h1 : p ≤ p * M := Nat.le_mul_of_pos_right p (Nat.pos_of_ne_zero hM)
  omega

theorem diag_ne (p n M : ℕ) (hn : n < p) (hM : M ≠ 0) : n ≠ p * M := by
  have h1 : p ≤ p * M := Nat.le_mul_of_pos_right p (Nat.pos_of_ne_zero hM)
  omega

theorem lower_ne_of_lt (p j n M e : ℕ) (hjp : j < p) (hn : n < p - j) (hM : M ≠ 0) (he : e ∣ M) :
    n + j * e ≠ p * M := by
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM
  have heM : e ≤ M := Nat.le_of_dvd hMpos he
  have hsplit : (p - j) * M + j * M = p * M := by
    rw [← add_mul, Nat.sub_add_cancel hjp.le]
  have h1 : p - j ≤ (p - j) * M := Nat.le_mul_of_pos_right _ hMpos
  have h2 : j * e ≤ j * M := Nat.mul_le_mul_left j heM
  omega

theorem lower_ne_at_j (p j M e : ℕ) (h2j : j + j < p) (hM : M ≠ 0) (he : e ∣ M) :
    j + j * e ≠ p * M := by
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM
  have heM : e ≤ M := Nat.le_of_dvd hMpos he
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos he hMpos
  have h1 : p * e ≤ p * M := Nat.mul_le_mul_left p heM
  have h2 : (j + j) * e < p * e := Nat.mul_lt_mul_of_lt_of_le h2j le_rfl hepos
  have h3 : j ≤ j * e := Nat.le_mul_of_pos_right j hepos
  have h4 : (j + j) * e = j * e + j * e := add_mul j j e
  omega

theorem lower_eq_at_iff (p j M e : ℕ) (hjp : j < p) (hM : M ≠ 0) (he : e ∣ M) :
    p - j + j * e = p * M ↔ M = 1 ∧ e = 1 := by
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM
  have heM : e ≤ M := Nat.le_of_dvd hMpos he
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos he hMpos
  constructor
  · intro h
    by_cases he1 : e = 1
    · subst he1
      refine ⟨?_, rfl⟩
      have hp : p * 1 = p * M := by rw [mul_one]; omega
      exact (Nat.eq_of_mul_eq_mul_left (by omega) hp).symm
    · exfalso
      have he2 : 2 ≤ e := by omega
      have h1 : p * e ≤ p * M := Nat.mul_le_mul_left p heM
      have hpe : p * e = p + p * (e - 1) := by
        conv_lhs => rw [show e = 1 + (e - 1) by omega]
        rw [mul_add, mul_one]
      have hje : j * e = j + j * (e - 1) := by
        conv_lhs => rw [show e = 1 + (e - 1) by omega]
        rw [mul_add, mul_one]
      have hlt : j * (e - 1) < p * (e - 1) := Nat.mul_lt_mul_of_lt_of_le hjp le_rfl (by omega)
      omega
  · rintro ⟨rfl, rfl⟩
    rw [mul_one, mul_one, Nat.sub_add_cancel hjp.le]

variable (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
include hj hjp

theorem coeff_eq_zero_of_lt (n : ℕ) (hn : n < min j (p - j)) :
    PowerSeries.coeff n (slotSubst K p c j tateUnivX) = 0 := by
  have hnj : n < j := lt_of_lt_of_le hn (min_le_left _ _)
  have hnpj : n < p - j := lt_of_lt_of_le hn (min_le_right _ _)
  have hnp : n < p := by omega
  rw [ModularCurve.coeff_slotSubst_tateUnivX p c j hj hjp n]
  have hhead : (if j ∣ n then ((n / j : ℕ) : K) * (c : K) ^ (n / j) else 0) = 0 := by
    split_ifs with hdiv
    · have hn0 : n = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hnj
      subst hn0
      simp
    · rfl
  rw [hhead, zero_add]
  refine Finset.sum_eq_zero fun M hM => Finset.sum_eq_zero fun e he => ?_
  obtain ⟨heM, hM0⟩ := Nat.mem_divisors.mp he
  rw [if_neg (upper_ne p j n M e hnp hM0), if_neg (lower_ne_of_lt p j n M e hjp hnpj hM0 heM),
    if_neg (diag_ne p n M hnp hM0)]
  ring

theorem coeff_j (h : j < p - j) : PowerSeries.coeff j (slotSubst K p c j tateUnivX) = (c : K) := by
  have h2j : j + j < p := by omega
  rw [ModularCurve.coeff_slotSubst_tateUnivX p c j hj hjp j]
  have hhead : (if j ∣ j then ((j / j : ℕ) : K) * (c : K) ^ (j / j) else 0) = (c : K) := by
    rw [if_pos (dvd_refl j), Nat.div_self hj]
    simp
  rw [hhead, add_eq_left]
  refine Finset.sum_eq_zero fun M hM => Finset.sum_eq_zero fun e he => ?_
  obtain ⟨heM, hM0⟩ := Nat.mem_divisors.mp he
  rw [if_neg (upper_ne p j j M e hjp hM0), if_neg (lower_ne_at_j p j M e h2j hM0 heM),
    if_neg (diag_ne p j M hjp hM0)]
  ring

theorem coeff_p_sub_j (h : p - j < j) :
    PowerSeries.coeff (p - j) (slotSubst K p c j tateUnivX) = ((c⁻¹ : Kˣ) : K) := by
  have hpj : 0 < p - j := Nat.sub_pos_of_lt hjp
  have hpjp : p - j < p := by omega
  rw [ModularCurve.coeff_slotSubst_tateUnivX p c j hj hjp (p - j)]
  have hhead : (if j ∣ (p - j) then (((p - j) / j : ℕ) : K) * (c : K) ^ ((p - j) / j) else 0) = 0 := by
    rw [if_neg (Nat.not_dvd_of_pos_of_lt hpj h)]
  rw [hhead, zero_add]

  rw [Finset.sum_eq_single 1]
  ·
    rw [Nat.divisors_one, Finset.sum_singleton]
    rw [if_neg (upper_ne p j (p - j) 1 1 hpjp one_ne_zero), if_neg (diag_ne p (p - j) 1 hpjp one_ne_zero),
      if_pos ((lower_eq_at_iff p j 1 1 hjp one_ne_zero (dvd_refl 1)).mpr ⟨rfl, rfl⟩)]
    simp
  ·
    intro M hM hM1
    refine Finset.sum_eq_zero fun e he => ?_
    obtain ⟨heM, hM0⟩ := Nat.mem_divisors.mp he
    have hne : p - j + j * e ≠ p * M := fun heq =>
      hM1 ((lower_eq_at_iff p j M e hjp hM0 heM).mp heq).1
    rw [if_neg (upper_ne p j (p - j) M e hpjp hM0), if_neg hne, if_neg (diag_ne p (p - j) M hpjp hM0)]
    ring
  ·
    intro h1
    exfalso
    exact h1 (Finset.mem_range.mpr (by omega))

theorem order_eq [Nontrivial K] (h2 : 2 * j ≠ p) :
    PowerSeries.order (slotSubst K p c j tateUnivX) = (min j (p - j) : ℕ) := by
  rw [PowerSeries.order_eq_nat]
  refine ⟨?_, fun i hi => coeff_eq_zero_of_lt p c j hj hjp i hi⟩
  rcases lt_trichotomy j (p - j) with hlt | heq | hgt
  · rw [min_eq_left hlt.le, coeff_j p c j hj hjp hlt]
    exact Units.ne_zero c
  · exfalso; apply h2; omega
  · rw [min_eq_right hgt.le, coeff_p_sub_j p c j hj hjp hgt]
    exact Units.ne_zero c⁻¹

end SlotOrdSol

open ModularCurve in
theorem solution
    {K : Type*} [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    (∀ n : ℕ, n < min j (p - j) → PowerSeries.coeff n (slotSubst K p c j tateUnivX) = 0) ∧
    (j < p - j → PowerSeries.coeff j (slotSubst K p c j tateUnivX) = (c : K)) ∧
    (p - j < j → PowerSeries.coeff (p - j) (slotSubst K p c j tateUnivX) = ((c⁻¹ : Kˣ) : K)) ∧
    (Nontrivial K → 2 * j ≠ p → PowerSeries.order (slotSubst K p c j tateUnivX) = (min j (p - j) : ℕ)) :=
  ⟨fun n hn => SlotOrdSol.coeff_eq_zero_of_lt p c j hj hjp n hn,
   fun h => SlotOrdSol.coeff_j p c j hj hjp h,
   fun h => SlotOrdSol.coeff_p_sub_j p c j hj hjp h,
   fun hK h2 => by haveI := hK; exact SlotOrdSol.order_eq p c j hj hjp h2⟩

end S_ModularCurve_coeff_slotSubst_tateUnivX_eq_zero_of_lt_min_and_coeff_eq_and_order_eq_min
end P2MW
export P2MW.S_ModularCurve_coeff_slotSubst_tateUnivX_eq_zero_of_lt_min_and_coeff_eq_and_order_eq_min (solution)
