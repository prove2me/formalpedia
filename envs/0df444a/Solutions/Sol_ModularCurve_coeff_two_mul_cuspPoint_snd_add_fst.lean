-- Prove2me | solution 1 for ModularCurve.coeff_two_mul_cuspPoint_snd_add_fst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/da661364-f8b1-51e3-9043-fb3849b5440f

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_ModularCurve_coeff_two_mul_tateUnivY_add_tateUnivX
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeff_two_mul_cuspPoint_snd_add_fst

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries

namespace ModularCurve
p2m_export "ModularCurve" "tateUnivX tateUnivY slotFamily slotSubst nonToricPoint nonToricPoint_fst nonToricPoint_snd tateUnivX_apply tateToricPoint tateToricPoint_fst tateToricPoint_snd cuspPoint cuspPoint_of_eq_zero cuspPoint_of_ne_zero coeff_two_mul_tateUnivY_add_tateUnivX"
p2m_open "ModularCurve"

section SlotSubstAPI

variable (K : Type*) [CommRing K]

theorem hasSubst_slotFamily (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    MvPowerSeries.HasSubst (slotFamily K p c j) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
  intro s
  fin_cases s
  · show PowerSeries.constantCoeff (PowerSeries.C (c : K) * PowerSeries.X ^ j) = 0
    rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow hj.ne', mul_zero]
  · show PowerSeries.constantCoeff (PowerSeries.C ((c⁻¹ : Kˣ) : K) * PowerSeries.X ^ (p - j)) = 0
    rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (Nat.sub_ne_zero_of_lt hjp), mul_zero]

def slotHom (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    MvPowerSeries (Fin 2) ℤ →+* LaurentSeries K :=
  (HahnSeries.ofPowerSeries ℤ K).comp
    (MvPowerSeries.substAlgHom (hasSubst_slotFamily K p c j hj hjp)).toRingHom

theorem slotHom_apply (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
    (f : MvPowerSeries (Fin 2) ℤ) :
    slotHom K p c j hj hjp f = HahnSeries.ofPowerSeries ℤ K (slotSubst K p c j f) := by
  simp only [slotHom, slotSubst, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    MvPowerSeries.substAlgHom_apply]

end SlotSubstAPI

section SpecS0

def reidxLineSet (a b N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (N+1) ×ˢ Finset.range (N+1)).filter fun e => a * e.1 + b * e.2 = N

def toFin2 (e : ℕ × ℕ) : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![e.1, e.2]

@[scoped simp] theorem toFin2_apply_zero (e : ℕ × ℕ) : toFin2 e 0 = e.1 := by simp [toFin2]

@[scoped simp] theorem toFin2_apply_one (e : ℕ × ℕ) : toFin2 e 1 = e.2 := by simp [toFin2]

theorem toFin2_injective : Function.Injective toFin2 := by
  intro x y h
  have h0 := DFunLike.congr_fun h 0
  have h1 := DFunLike.congr_fun h 1
  simp only [toFin2_apply_zero, toFin2_apply_one] at h0 h1
  exact Prod.ext h0 h1

theorem toFin2_pair (d : Fin 2 →₀ ℕ) : toFin2 (d 0, d 1) = d := by
  ext i
  fin_cases i
  · exact toFin2_apply_zero _
  · exact toFin2_apply_one _

theorem mem_reidxLineSet {a b N : ℕ} (ha : 0 < a) (hb : 0 < b) {e : ℕ × ℕ} :
    e ∈ reidxLineSet a b N ↔ a * e.1 + b * e.2 = N := by
  simp only [reidxLineSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    and_iff_right_iff_imp]
  intro h
  have h1 : e.1 ≤ a * e.1 := Nat.le_mul_of_pos_left _ ha
  have h2 : e.2 ≤ b * e.2 := Nat.le_mul_of_pos_left _ hb
  exact ⟨Nat.lt_succ_of_le (h1.trans (le_of_le_of_eq (Nat.le_add_right _ _) h)),
    Nat.lt_succ_of_le (h2.trans (le_of_le_of_eq (Nat.le_add_left _ _) h))⟩

end SpecS0

section SpecS1

theorem prod_pow_fin_two {M : Type*} [CommMonoid M] (a : Fin 2 → M) (d : Fin 2 →₀ ℕ) :
    (d.prod fun s n => a s ^ n) = a 0 ^ (d 0) * a 1 ^ (d 1) := by
  rw [Finsupp.prod_fintype d (fun s n => a s ^ n) fun _ => pow_zero _, Fin.prod_univ_two]

theorem coeff_subst_pair {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (A B : PowerSeries S) (hA : PowerSeries.constantCoeff A = 0)
    (hB : PowerSeries.constantCoeff B = 0) (f : MvPowerSeries (Fin 2) R) (N : ℕ) :
    PowerSeries.coeff N (MvPowerSeries.subst ![A, B] f : PowerSeries S) =
      ∑ e ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
        MvPowerSeries.coeff (toFin2 e) f • PowerSeries.coeff N (A ^ e.1 * B ^ e.2) := by
  have ha : MvPowerSeries.HasSubst (![A, B] : Fin 2 → PowerSeries S) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by
      fin_cases s
      · exact hA
      · exact hB
  have key : ∀ d : Fin 2 →₀ ℕ, ¬(d 0 ≤ N ∧ d 1 ≤ N) →
      PowerSeries.coeff N (A ^ (d 0) * B ^ (d 1)) = 0 := by
    intro d hd
    obtain ⟨A', hA'⟩ := PowerSeries.X_dvd_iff.mpr hA
    obtain ⟨B', hB'⟩ := PowerSeries.X_dvd_iff.mpr hB
    rw [hA', hB', mul_pow, mul_pow, mul_mul_mul_comm, ← _root_.pow_add, PowerSeries.coeff_X_pow_mul',
      if_neg (by omega)]
  change MvPowerSeries.coeff (Finsupp.single () N) (MvPowerSeries.subst ![A, B] f) = _
  rw [MvPowerSeries.coeff_subst ha,
    finsum_eq_sum_of_support_subset _
      (s := (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).image toFin2)]
  · rw [Finset.sum_image fun x _ y _ h => toFin2_injective h]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [prod_pow_fin_two]
    change MvPowerSeries.coeff (toFin2 e) f •
        PowerSeries.coeff N (A ^ (toFin2 e 0) * B ^ (toFin2 e 1)) = _
    rw [toFin2_apply_zero, toFin2_apply_one]
  · intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.coe_image, Set.mem_image]
    refine ⟨(d 0, d 1), ?_, toFin2_pair d⟩
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    by_contra hbox
    apply hd
    rw [prod_pow_fin_two]
    change MvPowerSeries.coeff d f • PowerSeries.coeff N (A ^ (d 0) * B ^ (d 1)) = 0
    rw [key d (by omega), smul_zero]

end SpecS1

section SpecS2

variable (K : Type*) [CommRing K]

theorem coeff_slotSubst (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
    (f : MvPowerSeries (Fin 2) ℤ) (N : ℕ) :
    PowerSeries.coeff N (slotSubst K p c j f) =
      ∑ e ∈ reidxLineSet j (p - j) N,
        ((f (toFin2 e) : ℤ) : K) * ((c ^ e.1 * c⁻¹ ^ e.2 : Kˣ) : K) := by
  have hA : PowerSeries.constantCoeff (PowerSeries.C (c : K) * PowerSeries.X ^ j) = 0 := by
    rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow hj.ne', mul_zero]
  have hB : PowerSeries.constantCoeff
      (PowerSeries.C ((c⁻¹ : Kˣ) : K) * PowerSeries.X ^ (p - j)) = 0 := by
    rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (Nat.sub_ne_zero_of_lt hjp),
      mul_zero]
  rw [slotSubst, slotFamily, coeff_subst_pair _ _ hA hB, reidxLineSet, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mul_pow, mul_pow, ← map_pow, ← map_pow, ← pow_mul, ← pow_mul, mul_mul_mul_comm, ← map_mul,
    ← _root_.pow_add, PowerSeries.coeff_C_mul_X_pow]
  by_cases h : j * e.1 + (p - j) * e.2 = N
  · rw [if_pos h.symm, if_pos h, Algebra.smul_def, eq_intCast, MvPowerSeries.coeff_apply,
      Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
  · rw [if_neg (Ne.symm h), if_neg h, smul_zero]

end SpecS2

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_coeff_two_mul_cuspPoint_snd_add_fst.ModularCurve"

namespace WP3

p2m_open "ModularCurve P2MW.S_ModularCurve_coeff_two_mul_cuspPoint_snd_add_fst.ModularCurve"

theorem coe_pow_add_mul_inv_pow {K : Type*} [CommRing K] (c : Kˣ) (b e : ℕ) :
    (c : K) ^ (b + e) * ((c⁻¹ : Kˣ) : K) ^ b = (c : K) ^ e := by
  rw [_root_.pow_add, mul_comm ((c : K) ^ b), mul_assoc, ← mul_pow, Units.mul_inv, one_pow, mul_one]

theorem coe_pow_mul_inv_pow_add {K : Type*} [CommRing K] (c : Kˣ) (b e : ℕ) :
    (c : K) ^ b * ((c⁻¹ : Kˣ) : K) ^ (b + e) = ((c⁻¹ : Kˣ) : K) ^ e := by
  rw [_root_.pow_add, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]

theorem lhs_eq_lineSum {K : Type*} [CommRing K] (N : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjN : j < N) (n : ℕ) :
    (2 * (nonToricPoint K N c j).2 + (nonToricPoint K N c j).1).coeff (n : ℤ) =
      ∑ e ∈ reidxLineSet j (N - j) n,
        (((((e.1 : ℤ) - e.2) * tateUnivX (toFin2 e) : ℤ)) : K) * ((c ^ e.1 * c⁻¹ ^ e.2 : Kˣ) : K) := by
  have h1 : 2 * (nonToricPoint K N c j).2 + (nonToricPoint K N c j).1 =
      slotHom K N c j hj hjN (2 * tateUnivY + tateUnivX) := by
    rw [map_add, map_mul, map_ofNat, slotHom_apply, slotHom_apply, nonToricPoint_snd, nonToricPoint_fst]
  rw [h1, slotHom_apply, HahnSeries.ofPowerSeries_apply_coeff, coeff_slotSubst K N c j hj hjN]
  refine Finset.sum_congr rfl fun e _ => ?_
  have h := ModularCurve.coeff_two_mul_tateUnivY_add_tateUnivX e.1 e.2
  have he : (Finsupp.single 0 e.1 + Finsupp.single 1 e.2 : Fin 2 →₀ ℕ) = toFin2 e := by
    rw [← toFin2_pair (Finsupp.single 0 e.1 + Finsupp.single 1 e.2)]
    simp [Finsupp.add_apply, Finsupp.single_apply]
  rw [he, MvPowerSeries.coeff_apply, MvPowerSeries.coeff_apply] at h
  rw [h]

theorem lineTerm_eq {K : Type*} [CommRing K] (c : Kˣ) (e : ℕ × ℕ) :
    (((((e.1 : ℤ) - e.2) * tateUnivX (toFin2 e) : ℤ)) : K) * ((c ^ e.1 * c⁻¹ ^ e.2 : Kˣ) : K) =
      if e.1 = e.2 then 0
      else if e.2 < e.1 then (if e.1 - e.2 ∣ e.2 then (((e.1 - e.2 : ℕ) : K)) ^ 2 * (c : K) ^ (e.1 - e.2) else 0)
      else (if e.2 - e.1 ∣ e.2 then -((((e.2 - e.1 : ℕ) : K)) ^ 2 * ((c⁻¹ : Kˣ) : K) ^ (e.2 - e.1)) else 0) := by
  have hX : tateUnivX (toFin2 e) = MvPowerSeries.coeff (toFin2 e) tateUnivX := rfl
  rw [hX, tateUnivX_apply, toFin2_apply_zero, toFin2_apply_one]
  by_cases h : e.1 = e.2
  · simp [h]
  · rw [if_neg h, if_neg h]
    by_cases hlt : e.2 < e.1
    · rw [if_pos hlt, if_pos hlt]
      by_cases hd : e.1 - e.2 ∣ e.2
      · rw [if_pos hd, if_pos hd]
        obtain ⟨d, hd'⟩ : ∃ d, e.1 = e.2 + d := ⟨e.1 - e.2, by omega⟩
        rw [hd', Nat.add_sub_cancel_left, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
          coe_pow_add_mul_inv_pow]
        push_cast; ring
      · rw [if_neg hd, if_neg hd]; simp
    · rw [if_neg hlt, if_neg hlt]
      by_cases hd : e.2 - e.1 ∣ e.2
      · rw [if_pos hd, if_pos hd]
        obtain ⟨d, hd'⟩ : ∃ d, e.2 = e.1 + d := ⟨e.2 - e.1, by omega⟩
        rw [hd', Nat.add_sub_cancel_left, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
          coe_pow_mul_inv_pow_add]
        push_cast; ring
      · rw [if_neg hd, if_neg hd]; simp

theorem sum_above_eq {K : Type*} [CommRing K] (N : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjN : j < N) (n : ℕ) (hn : 1 ≤ n) :
    ∑ e ∈ ((reidxLineSet j (N - j) n).filter fun e => e.2 < e.1).filter fun e => e.1 - e.2 ∣ e.2,
        (((e.1 - e.2 : ℕ) : K)) ^ 2 * (c : K) ^ (e.1 - e.2) =
      ∑ md ∈ (Nat.divisorsAntidiagonal n).filter fun md => md.1 % N = j % N,
        ((md.2 : ℕ) : K) ^ 2 * (c : K) ^ md.2 := by
  have hNj : 0 < N - j := Nat.sub_pos_of_lt hjN
  have hjmod : j % N = j := Nat.mod_eq_of_lt hjN
  refine Finset.sum_nbij' (fun e => (n / (e.1 - e.2), e.1 - e.2))
    (fun md => (md.2 * ((md.1 - j) / N) + md.2, md.2 * ((md.1 - j) / N))) ?_ ?_ ?_ ?_ ?_
  ·
    intro e he
    simp only [Finset.mem_filter] at he
    obtain ⟨⟨hline, hlt⟩, hdvd⟩ := he
    rw [mem_reidxLineSet hj hNj] at hline
    obtain ⟨t, ht⟩ := hdvd
    set d := e.1 - e.2 with hd
    have he1 : e.1 = d * t + d := by omega
    have hn' : n = d * (N * t + j) := by
      rw [← hline, he1, ht]
      have : (N - j) * (d * t) + j * (d * t) = N * (d * t) := by
        rw [← add_mul, Nat.sub_add_cancel hjN.le]
      nlinarith [this]
    have hd0 : 0 < d := by omega
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
    refine ⟨⟨?_, by omega⟩, ?_⟩
    · rw [hn', Nat.mul_div_cancel_left _ hd0, mul_comm]
    · rw [hn', Nat.mul_div_cancel_left _ hd0, Nat.add_comm, Nat.add_mul_mod_self_left, hjmod]
  ·
    intro md hmd
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hmd
    obtain ⟨⟨hmul, hn0⟩, hmod⟩ := hmd
    set q := (md.1 - j) / N with hq
    have hm : md.1 = N * q + j := by
      have h1 := Nat.div_add_mod md.1 N
      rw [hmod, hjmod] at h1
      have : md.1 - j = N * (md.1 / N) := by omega
      rw [hq, this, Nat.mul_div_cancel_left _ (by omega)]
      omega
    have hd0 : 0 < md.2 := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hmul; exact hn0 hmul.symm
    simp only [Finset.mem_filter, mem_reidxLineSet hj hNj]
    try rw [← hq]
    refine ⟨⟨?_, by omega⟩, ?_⟩
    · rw [← hmul, hm]
      have : (N - j) * (md.2 * q) + j * (md.2 * q) = N * (md.2 * q) := by
        rw [← add_mul, Nat.sub_add_cancel hjN.le]
      nlinarith [this]
    · rw [Nat.add_sub_cancel_left]; exact Dvd.intro _ rfl
  ·
    intro e he
    simp only [Finset.mem_filter] at he
    obtain ⟨⟨hline, hlt⟩, hdvd⟩ := he
    rw [mem_reidxLineSet hj hNj] at hline
    obtain ⟨t, ht⟩ := hdvd
    set d := e.1 - e.2 with hd
    have he1 : e.1 = d * t + d := by omega
    have hn' : n = d * (N * t + j) := by
      rw [← hline, he1, ht]
      have : (N - j) * (d * t) + j * (d * t) = N * (d * t) := by
        rw [← add_mul, Nat.sub_add_cancel hjN.le]
      nlinarith [this]
    have hd0 : 0 < d := by omega
    have hq : (n / d - j) / N = t := by
      rw [hn', Nat.mul_div_cancel_left _ hd0, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by omega)]
    ext
    · show d * ((n / d - j) / N) + d = e.1
      rw [hq]; omega
    · show d * ((n / d - j) / N) = e.2
      rw [hq, ht]
  ·
    intro md hmd
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hmd
    obtain ⟨⟨hmul, hn0⟩, hmod⟩ := hmd
    have hd0 : 0 < md.2 := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hmul; exact hn0 hmul.symm
    ext
    · show n / (md.2 * ((md.1 - j) / N) + md.2 - md.2 * ((md.1 - j) / N)) = md.1
      rw [Nat.add_sub_cancel_left, ← hmul, Nat.mul_div_cancel _ hd0]
    · show md.2 * ((md.1 - j) / N) + md.2 - md.2 * ((md.1 - j) / N) = md.2
      rw [Nat.add_sub_cancel_left]
  ·
    intro e he
    rfl

theorem sum_below_eq {K : Type*} [CommRing K] (N : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjN : j < N) (n : ℕ) (hn : 1 ≤ n) :
    ∑ e ∈ ((reidxLineSet j (N - j) n).filter fun e => e.1 < e.2).filter fun e => e.2 - e.1 ∣ e.2,
        (((e.2 - e.1 : ℕ) : K)) ^ 2 * ((c⁻¹ : Kˣ) : K) ^ (e.2 - e.1) =
      ∑ md ∈ (Nat.divisorsAntidiagonal n).filter fun md => (md.1 + j) % N = 0,
        ((md.2 : ℕ) : K) ^ 2 * ((c⁻¹ : Kˣ) : K) ^ md.2 := by
  have hNj : 0 < N - j := Nat.sub_pos_of_lt hjN
  refine Finset.sum_nbij' (fun e => (n / (e.2 - e.1), e.2 - e.1))
    (fun md => (md.2 * ((md.1 + j) / N) - md.2, md.2 * ((md.1 + j) / N))) ?_ ?_ ?_ ?_ ?_
  ·
    intro e he
    simp only [Finset.mem_filter] at he
    obtain ⟨⟨hline, hlt⟩, hdvd⟩ := he
    rw [mem_reidxLineSet hj hNj] at hline
    obtain ⟨t, ht⟩ := hdvd
    set d := e.2 - e.1 with hd
    have hd0 : 0 < d := by omega
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by
      rcases t with _ | t
      · rw [mul_zero] at ht; omega
      · omega⟩
    have he1 : e.1 = d * s := by
      have : e.1 = e.2 - d := by omega
      rw [this, ht]; rw [Nat.mul_succ, Nat.add_sub_cancel]
    have hn' : n = d * (N * s + (N - j)) := by
      rw [← hline, he1, ht, Nat.mul_succ]
      have h1 : (N - j) + j = N := Nat.sub_add_cancel hjN.le
      nlinarith [h1]
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
    refine ⟨⟨?_, by omega⟩, ?_⟩
    · rw [hn', Nat.mul_div_cancel_left _ hd0, mul_comm]
    · rw [hn', Nat.mul_div_cancel_left _ hd0, add_assoc, Nat.sub_add_cancel hjN.le, ← Nat.mul_succ,
        Nat.mul_mod_right]
  ·
    intro md hmd
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hmd
    obtain ⟨⟨hmul, hn0⟩, hmod⟩ := hmd
    set q := (md.1 + j) / N with hq
    have hmq : md.1 + j = N * q := by
      have h1 := Nat.div_add_mod (md.1 + j) N
      rw [hmod, add_zero] at h1
      exact h1.symm
    have hm1 : 1 ≤ md.1 := Nat.pos_of_ne_zero fun h => by rw [h, zero_mul] at hmul; exact hn0 hmul.symm
    have hq1 : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · rw [h0, mul_zero] at hmq; omega
      · exact h0
    obtain ⟨s, hs⟩ : ∃ s, q = s + 1 := ⟨q - 1, by omega⟩
    have hm : md.1 = N * s + (N - j) := by
      have : md.1 + j = N * s + N := by rw [hmq, hs, Nat.mul_succ]
      omega
    have hd0 : 0 < md.2 := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hmul; exact hn0 hmul.symm
    simp only [Finset.mem_filter, mem_reidxLineSet hj hNj]
    (try rw [← hq]); rw [hs, Nat.mul_succ, Nat.add_sub_cancel]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← hmul, hm]
      have h1 : (N - j) + j = N := Nat.sub_add_cancel hjN.le
      have h2 : (N - j) * (md.2 * s) + j * (md.2 * s) = N * (md.2 * s) := by rw [← add_mul, h1]
      linarith [h2]
    · omega
    · rw [show md.2 * s + md.2 - md.2 * s = md.2 by omega]; exact Dvd.intro (s + 1) (by ring)
  ·
    intro e he
    simp only [Finset.mem_filter] at he
    obtain ⟨⟨hline, hlt⟩, hdvd⟩ := he
    rw [mem_reidxLineSet hj hNj] at hline
    obtain ⟨t, ht⟩ := hdvd
    set d := e.2 - e.1 with hd
    have hd0 : 0 < d := by omega
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by
      rcases t with _ | t
      · rw [mul_zero] at ht; omega
      · omega⟩
    have he1 : e.1 = d * s := by
      have : e.1 = e.2 - d := by omega
      rw [this, ht]; rw [Nat.mul_succ, Nat.add_sub_cancel]
    have hn' : n = d * (N * s + (N - j)) := by
      rw [← hline, he1, ht, Nat.mul_succ]
      have h1 : (N - j) + j = N := Nat.sub_add_cancel hjN.le
      nlinarith [h1]
    have hq : (n / d + j) / N = s + 1 := by
      rw [hn', Nat.mul_div_cancel_left _ hd0, add_assoc, Nat.sub_add_cancel hjN.le, ← Nat.mul_succ,
        Nat.mul_div_cancel_left _ (by omega)]
    ext
    · show d * ((n / d + j) / N) - d = e.1
      rw [hq, he1, Nat.mul_succ, Nat.add_sub_cancel]
    · show d * ((n / d + j) / N) = e.2
      rw [hq, ht]
  ·
    intro md hmd
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hmd
    obtain ⟨⟨hmul, hn0⟩, hmod⟩ := hmd
    have hd0 : 0 < md.2 := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hmul; exact hn0 hmul.symm
    have hq1 : 1 ≤ (md.1 + j) / N := by
      have hm1 : 1 ≤ md.1 := Nat.pos_of_ne_zero fun h => by rw [h, zero_mul] at hmul; exact hn0 hmul.symm
      have hmq : md.1 + j = N * ((md.1 + j) / N) := by
        have h1 := Nat.div_add_mod (md.1 + j) N
        rw [hmod, add_zero] at h1; exact h1.symm
      rcases Nat.eq_zero_or_pos ((md.1 + j) / N) with h0 | h0
      · rw [h0, mul_zero] at hmq; omega
      · exact h0
    have hsub : md.2 * ((md.1 + j) / N) - (md.2 * ((md.1 + j) / N) - md.2) = md.2 := by
      have : md.2 ≤ md.2 * ((md.1 + j) / N) := Nat.le_mul_of_pos_right _ hq1
      omega
    ext
    · show n / (md.2 * ((md.1 + j) / N) - (md.2 * ((md.1 + j) / N) - md.2)) = md.1
      rw [hsub, ← hmul, Nat.mul_div_cancel _ hd0]
    · show md.2 * ((md.1 + j) / N) - (md.2 * ((md.1 + j) / N) - md.2) = md.2
      exact hsub
  · intro e he
    rfl

end WP3
p2m_reactivate "P2MW.S_ModularCurve_coeff_two_mul_cuspPoint_snd_add_fst.ModularCurve"

namespace WP3

p2m_open "ModularCurve P2MW.S_ModularCurve_coeff_two_mul_cuspPoint_snd_add_fst.ModularCurve"

theorem lineSum_eq_divisorSum {K : Type*} [CommRing K] (N : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjN : j < N)
    (n : ℕ) (hn : 1 ≤ n) :
    ∑ e ∈ reidxLineSet j (N - j) n,
        (((((e.1 : ℤ) - e.2) * tateUnivX (toFin2 e) : ℤ)) : K) * ((c ^ e.1 * c⁻¹ ^ e.2 : Kˣ) : K) =
      ∑ md ∈ Nat.divisorsAntidiagonal n,
        ((md.2 : ℕ) : K) ^ 2 *
          ((if md.1 % N = j % N then (c : K) ^ md.2 else 0) -
            (if (md.1 + j) % N = 0 then ((c⁻¹ : Kˣ) : K) ^ md.2 else 0)) := by
  classical
  rw [Finset.sum_congr rfl fun e _ => lineTerm_eq c e]
  rw [← Finset.sum_filter_add_sum_filter_not (reidxLineSet j (N - j) n) (fun e => e.2 < e.1)]
  have hA : ∑ e ∈ (reidxLineSet j (N - j) n).filter (fun e => e.2 < e.1),
      (if e.1 = e.2 then (0 : K)
        else if e.2 < e.1 then (if e.1 - e.2 ∣ e.2 then (((e.1 - e.2 : ℕ) : K)) ^ 2 * (c : K) ^ (e.1 - e.2) else 0)
        else (if e.2 - e.1 ∣ e.2 then -((((e.2 - e.1 : ℕ) : K)) ^ 2 * ((c⁻¹ : Kˣ) : K) ^ (e.2 - e.1)) else 0)) =
      ∑ md ∈ (Nat.divisorsAntidiagonal n).filter fun md => md.1 % N = j % N,
        ((md.2 : ℕ) : K) ^ 2 * (c : K) ^ md.2 := by
    rw [← sum_above_eq N c j hj hjN n hn]
    conv_rhs => rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun e he => ?_
    have hlt : e.2 < e.1 := (Finset.mem_filter.mp he).2
    rw [if_neg (by omega), if_pos hlt]
  have hB : ∑ e ∈ (reidxLineSet j (N - j) n).filter (fun e => ¬ e.2 < e.1),
      (if e.1 = e.2 then (0 : K)
        else if e.2 < e.1 then (if e.1 - e.2 ∣ e.2 then (((e.1 - e.2 : ℕ) : K)) ^ 2 * (c : K) ^ (e.1 - e.2) else 0)
        else (if e.2 - e.1 ∣ e.2 then -((((e.2 - e.1 : ℕ) : K)) ^ 2 * ((c⁻¹ : Kˣ) : K) ^ (e.2 - e.1)) else 0)) =
      -∑ md ∈ (Nat.divisorsAntidiagonal n).filter fun md => (md.1 + j) % N = 0,
        ((md.2 : ℕ) : K) ^ 2 * ((c⁻¹ : Kˣ) : K) ^ md.2 := by
    rw [← sum_below_eq N c j hj hjN n hn, ← Finset.sum_neg_distrib]
    conv_rhs => rw [Finset.sum_filter]
    rw [← Finset.sum_filter_add_sum_filter_not ((reidxLineSet j (N - j) n).filter (fun e => ¬ e.2 < e.1)) (fun e => e.1 < e.2)]
    rw [Finset.filter_filter, Finset.filter_filter]
    have h0 : ∑ e ∈ (reidxLineSet j (N - j) n).filter (fun e => ¬ e.2 < e.1 ∧ ¬ e.1 < e.2),
        (if e.1 = e.2 then (0 : K)
          else if e.2 < e.1 then (if e.1 - e.2 ∣ e.2 then (((e.1 - e.2 : ℕ) : K)) ^ 2 * (c : K) ^ (e.1 - e.2) else 0)
          else (if e.2 - e.1 ∣ e.2 then -((((e.2 - e.1 : ℕ) : K)) ^ 2 * ((c⁻¹ : Kˣ) : K) ^ (e.2 - e.1)) else 0)) = 0 := by
      refine Finset.sum_eq_zero fun e he => ?_
      simp only [Finset.mem_filter] at he
      rw [if_pos (by omega)]
    rw [h0, add_zero]
    have hset : (reidxLineSet j (N - j) n).filter (fun e => ¬ e.2 < e.1 ∧ e.1 < e.2) =
        (reidxLineSet j (N - j) n).filter (fun e => e.1 < e.2) := by
      refine Finset.filter_congr fun e _ => ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
    rw [hset]
    refine Finset.sum_congr rfl fun e he => ?_
    have hlt : e.1 < e.2 := (Finset.mem_filter.mp he).2
    rw [if_neg (by omega), if_neg (by omega)]
  rw [hA, hB, Finset.sum_filter, Finset.sum_filter, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun md _ => ?_
  split_ifs <;> ring

theorem nonToric {K : Type*} [CommRing K] (N : ℕ) [NeZero N] (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjN : j < N)
    (n : ℕ) (hn : 1 ≤ n) :
    (2 * (nonToricPoint K N c j).2 + (nonToricPoint K N c j).1).coeff (n : ℤ) =
      ∑ md ∈ Nat.divisorsAntidiagonal n,
        ((md.2 : ℕ) : K) ^ 2 *
          ((if md.1 % N = j % N then (c : K) ^ md.2 else 0) -
            (if (md.1 + j) % N = 0 then ((c⁻¹ : Kˣ) : K) ^ md.2 else 0)) := by
  rw [lhs_eq_lineSum N c j hj hjN n, lineSum_eq_divisorSum N c j hj hjN n hn]

theorem two_mul_choose_two_add (e : ℕ) : 2 * e.choose 2 + e = e * e := by
  rw [Nat.choose_two_right, Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self e)]
  rcases e with _ | k
  · simp
  · rw [Nat.add_sub_cancel]; ring

theorem two_mul_choose_succ_two (e : ℕ) : 2 * (e + 1).choose 2 = e * e + e := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.two_mul_div_two_of_even]
  · ring
  · simpa [mul_comm] using Nat.even_mul_succ_self e

theorem toric {K : Type*} [CommRing K] (N : ℕ) (c : Kˣ) (n : ℕ) (hn : 1 ≤ n) :
    (2 * (tateToricPoint K N c).2 + (tateToricPoint K N c).1).coeff (n : ℤ) =
      ∑ md ∈ Nat.divisorsAntidiagonal n,
        ((md.2 : ℕ) : K) ^ 2 *
          ((if N ∣ md.1 then (c : K) ^ md.2 else 0) - (if N ∣ md.1 then ((c⁻¹ : Kˣ) : K) ^ md.2 else 0)) := by
  have hR : ∑ md ∈ Nat.divisorsAntidiagonal n,
        ((md.2 : ℕ) : K) ^ 2 *
          ((if N ∣ md.1 then (c : K) ^ md.2 else 0) - (if N ∣ md.1 then ((c⁻¹ : Kˣ) : K) ^ md.2 else 0)) =
      ∑ d ∈ n.divisors, ((n / d : ℕ) : K) ^ 2 *
          ((if N ∣ d then (c : K) ^ (n / d) else 0) - (if N ∣ d then ((c⁻¹ : Kˣ) : K) ^ (n / d) else 0)) :=
    Nat.sum_divisorsAntidiagonal (fun m d => ((d : ℕ) : K) ^ 2 *
      ((if N ∣ m then (c : K) ^ d else 0) - (if N ∣ m then ((c⁻¹ : Kˣ) : K) ^ d else 0)))
  have hn0 : n ≠ 0 := by omega
  rw [hR, tateToricPoint_snd, tateToricPoint_fst, two_mul, HahnSeries.coeff_add, HahnSeries.coeff_add,
    HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk,
    PowerSeries.coeff_mk, if_neg hn0, if_neg hn0]
  have hring : ∀ A B S : K, (A + S) + (A + S) + (B - 2 * S) = A + A + B := fun A B S => by ring
  rw [hring, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs with h
  · have h1 : (2 : K) * ((n / d).choose 2 : K) + ((n / d : ℕ) : K) = ((n / d : ℕ) : K) * ((n / d : ℕ) : K) := by
      exact_mod_cast congrArg (Nat.cast (R := K)) (two_mul_choose_two_add (n / d))
    have h2 : (2 : K) * ((n / d + 1).choose 2 : K) = ((n / d : ℕ) : K) * ((n / d : ℕ) : K) + ((n / d : ℕ) : K) := by
      exact_mod_cast congrArg (Nat.cast (R := K)) (two_mul_choose_succ_two (n / d))
    linear_combination ((c : K) ^ (n / d)) * h1 - (((c⁻¹ : Kˣ) : K) ^ (n / d)) * h2
  · simp

end WP3
p2m_reactivate "P2MW.S_ModularCurve_coeff_two_mul_cuspPoint_snd_add_fst.ModularCurve"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_coeff_two_mul_cuspPoint_snd_add_fst.ModularCurve WP3 in
theorem solution
    (L : Type) [Field L] (N : ℕ) [NeZero N] (ξ : Lˣ) (hξ : IsPrimitiveRoot (ξ : L) N)
    (v : Fin 2 → ZMod N) (hv : v ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    (2 * (ModularCurve.cuspPoint L N ξ v).2 + (ModularCurve.cuspPoint L N ξ v).1).coeff (n : ℤ) =
      ∑ md ∈ Nat.divisorsAntidiagonal n,
        ((md.2 : ℕ) : L) ^ 2 *
          ((if ((md.1 : ℕ) : ZMod N) = v 1 then ((ξ ^ (md.2 * (v 0).val) : Lˣ) : L) else 0) -
            (if ((md.1 : ℕ) : ZMod N) = -v 1 then ((ξ⁻¹ ^ (md.2 * (v 0).val) : Lˣ) : L) else 0)) := by
  classical
  have v1eq : ∀ md : ℕ × ℕ, ((ξ ^ (v 0).val : Lˣ) : L) ^ md.2 = ((ξ ^ (md.2 * (v 0).val) : Lˣ) : L) := fun md => by
    rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm]
  have v2eq : ∀ md : ℕ × ℕ, (((ξ ^ (v 0).val)⁻¹ : Lˣ) : L) ^ md.2 = ((ξ⁻¹ ^ (md.2 * (v 0).val) : Lˣ) : L) := fun md => by
    rw [← Units.val_pow_eq_pow_val, ← inv_pow, ← pow_mul, mul_comm, inv_pow]
  by_cases hv1 : v 1 = 0
  ·
    rw [ModularCurve.cuspPoint_of_eq_zero ξ hv1, toric N (ξ ^ (v 0).val) n hn]
    refine Finset.sum_congr rfl fun md _ => ?_
    congr 1
    have e1 : (N ∣ md.1) ↔ (((md.1 : ℕ) : ZMod N) = v 1) := by
      rw [hv1, ZMod.natCast_eq_zero_iff]
    have e2 : (N ∣ md.1) ↔ (((md.1 : ℕ) : ZMod N) = -v 1) := by
      rw [hv1, neg_zero, ZMod.natCast_eq_zero_iff]
    rw [v1eq, v2eq]
    exact congrArg₂ (· - ·) (if_congr e1 rfl rfl) (if_congr e2 rfl rfl)
  ·
    have hj : 0 < (v 1).val := by
      rw [Nat.pos_iff_ne_zero]; exact fun h => hv1 ((ZMod.val_eq_zero _).mp h)
    have hjN : (v 1).val < N := ZMod.val_lt _
    rw [ModularCurve.cuspPoint_of_ne_zero ξ hv1, nonToric N (ξ ^ (v 0).val) (v 1).val hj hjN n hn]
    refine Finset.sum_congr rfl fun md _ => ?_
    congr 1
    have e1 : (md.1 % N = (v 1).val % N) ↔ (((md.1 : ℕ) : ZMod N) = v 1) := by
      rw [← ZMod.natCast_eq_natCast_iff', ZMod.natCast_zmod_val]
    have e2 : ((md.1 + (v 1).val) % N = 0) ↔ (((md.1 : ℕ) : ZMod N) = -v 1) := by
      rw [← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff, Nat.cast_add, ZMod.natCast_zmod_val,
        add_eq_zero_iff_eq_neg]
    rw [v1eq, v2eq]
    exact congrArg₂ (· - ·) (if_congr e1 rfl rfl) (if_congr e2 rfl rfl)

end
p2m_reactivate "P2MW.S_ModularCurve_coeff_two_mul_cuspPoint_snd_add_fst.ModularCurve"

end S_ModularCurve_coeff_two_mul_cuspPoint_snd_add_fst
end P2MW
export P2MW.S_ModularCurve_coeff_two_mul_cuspPoint_snd_add_fst (solution)
