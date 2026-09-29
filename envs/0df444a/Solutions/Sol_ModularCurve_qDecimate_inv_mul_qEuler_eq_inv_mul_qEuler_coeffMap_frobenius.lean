-- Prove2me | solution 1 for ModularCurve.qDecimate_inv_mul_qEuler_eq_inv_mul_qEuler_coeffMap_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/e8a67691-7f4f-5372-9a2b-20731ef4665c

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qDecimate_inv_mul_qEuler_eq_inv_mul_qEuler_coeffMap_frobenius

set_option autoImplicit false

noncomputable section

open HahnSeries Finset

namespace ModularCurve
p2m_export "ModularCurve" "qDecimate coeff_qDecimate qDecimate_qExpand qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single qExpand_injective coeffMap coeffMap_coeff pow_char_eq_coeffMap_frobenius_qExpand qEuler qEuler_coeff"
namespace D6bCore
p2m_open "ModularCurve"

theorem choose_div_mul_succ {n m : ℕ} (hp : (n + 1).Prime) (hm : m < n) :
    (n + 1).choose (m + 1) / (n + 1) * (m + 1) = n.choose m := by
  have hdvd : (n + 1) ∣ (n + 1).choose (m + 1) :=
    hp.dvd_choose_self (Nat.succ_ne_zero m) (by omega)
  have h : (n + 1) * n.choose m = (n + 1).choose (m + 1) * (m + 1) := Nat.add_one_mul_choose_eq n m
  rw [Nat.div_mul_right_comm hdvd, ← h, Nat.mul_div_cancel_left _ hp.pos]

theorem choose_div_mul_sub {n m : ℕ} (hp : (n + 1).Prime) (hm : m < n) :
    (n + 1).choose (m + 1) / (n + 1) * (n - m) = n.choose (m + 1) := by
  have hdvd : (n + 1) ∣ (n + 1).choose (m + 1) :=
    hp.dvd_choose_self (Nat.succ_ne_zero m) (by omega)
  have h : n.choose (m + 1) * (n + 1) = (n + 1).choose (m + 1) * (n + 1 - (m + 1)) :=
    Nat.choose_mul_succ_eq n (m + 1)
  have hsub : n + 1 - (m + 1) = n - m := by omega
  rw [hsub] at h
  rw [Nat.div_mul_right_comm hdvd, ← h, Nat.mul_div_cancel _ hp.pos]

section Pointwise

variable (K : Type*) [Field K] (p : ℕ) [hp : Fact p.Prime]

scoped instance (priority := low) neZero_of_fact_prime' : NeZero p := ⟨hp.out.ne_zero⟩

theorem coeff_iterate_qEuler (k : ℕ) (x : LaurentSeries K) (n : ℤ) :
    ((ModularCurve.qEuler K)^[k] x).coeff n = (n : K) ^ k * x.coeff n := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', qEuler_coeff, ih, pow_succ]
    ring

omit hp in

theorem deriv_add_mul_add_pow {n : ℕ} (hp : (n + 1).Prime) (f g : LaurentSeries K) :
    ModularCurve.qEuler K (f + g) * (f + g) ^ n =
      ModularCurve.qEuler K f * f ^ n + ModularCurve.qEuler K g * g ^ n +
        ModularCurve.qEuler K (∑ m ∈ range n, (((n + 1).choose (m + 1) / (n + 1) : ℕ) : LaurentSeries K) * (f ^ (m + 1) * g ^ (n - m))) := by
  have key : ∀ m ∈ range n,
      ModularCurve.qEuler K ((((n + 1).choose (m + 1) / (n + 1) : ℕ) : LaurentSeries K) * (f ^ (m + 1) * g ^ (n - m))) =
        ((n.choose m : ℕ) : LaurentSeries K) * (f ^ m * g ^ (n - m)) * ModularCurve.qEuler K f +
          ((n.choose (m + 1) : ℕ) : LaurentSeries K) * (f ^ (m + 1) * g ^ (n - (m + 1))) * ModularCurve.qEuler K g := by
    intro m hm
    rw [mem_range] at hm
    have hnm : n - m = n - (m + 1) + 1 := by omega
    rw [← choose_div_mul_succ hp hm, ← choose_div_mul_sub hp hm]
    have hcd : ModularCurve.qEuler K ((((n + 1).choose (m + 1) / (n + 1) : ℕ) : LaurentSeries K)) = 0 := (ModularCurve.qEuler K).map_natCast _
    rw [(ModularCurve.qEuler K).leibniz, hcd, smul_zero, add_zero, (ModularCurve.qEuler K).leibniz, (ModularCurve.qEuler K).leibniz_pow, (ModularCurve.qEuler K).leibniz_pow, hnm]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel, pow_succ]
    push_cast
    ring
  rw [map_sum, sum_congr rfl key, sum_add_distrib, add_pow, mul_sum]
  have hsplit : ∀ m ∈ range (n + 1),
      ModularCurve.qEuler K (f + g) * (f ^ m * g ^ (n - m) * ((n.choose m : ℕ) : LaurentSeries K)) =
        ((n.choose m : ℕ) : LaurentSeries K) * (f ^ m * g ^ (n - m)) * ModularCurve.qEuler K f +
          ((n.choose m : ℕ) : LaurentSeries K) * (f ^ m * g ^ (n - m)) * ModularCurve.qEuler K g := by
    intro m _
    rw [map_add]
    ring
  rw [sum_congr rfl hsplit, sum_add_distrib,
    sum_range_succ (fun m => ((n.choose m : ℕ) : LaurentSeries K) * (f ^ m * g ^ (n - m)) * ModularCurve.qEuler K f),
    sum_range_succ' (fun m => ((n.choose m : ℕ) : LaurentSeries K) * (f ^ m * g ^ (n - m)) * ModularCurve.qEuler K g)]
  simp only [Nat.choose_self, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_self, Nat.sub_zero,
    pow_zero, mul_one]
  ring

theorem qEuler_coeffMap (φ : K →+* K) (x : LaurentSeries K) :
    ModularCurve.qEuler K (ModularCurve.coeffMap φ x) =
      ModularCurve.coeffMap φ (ModularCurve.qEuler K x) := by
  ext n
  rw [qEuler_coeff, coeffMap_coeff, coeffMap_coeff, qEuler_coeff, map_mul, map_intCast]

theorem qExpand_coeffMap (φ : K →+* K) (x : LaurentSeries K) :
    ModularCurve.qExpand K p (ModularCurve.coeffMap φ x) =
      ModularCurve.coeffMap φ (ModularCurve.qExpand K p x) := by
  ext n
  by_cases hn : (p : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hn
    rw [qExpand_coeff_mul, coeffMap_coeff, coeffMap_coeff, qExpand_coeff_mul]
  · rw [qExpand_coeff_of_not_dvd p _ hn, coeffMap_coeff, qExpand_coeff_of_not_dvd p _ hn, map_zero]

variable [CharP K p]

theorem intCast_pow_sub_one_eq_one {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) : (n : K) ^ (p - 1) = 1 := by
  have hz : ((n : ℤ) : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h1 : ((n : ℤ) : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hz
  have hcast : (ZMod.castHom (dvd_refl p) K) ((n : ℤ) : ZMod p) = (n : K) := map_intCast _ n
  rw [← hcast, ← map_pow, h1, map_one]

omit hp in
theorem intCast_eq_zero_of_dvd {n : ℤ} (hn : (p : ℤ) ∣ n) : (n : K) = 0 := by
  obtain ⟨k, rfl⟩ := hn
  rw [Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero K p, zero_mul]

theorem qExpand_qDecimate (x : LaurentSeries K) :
    ModularCurve.qExpand K p (ModularCurve.qDecimate K p x) = x - (ModularCurve.qEuler K)^[p - 1] x := by
  ext n
  rw [HahnSeries.coeff_sub, coeff_iterate_qEuler]
  by_cases hn : (p : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hn
    rw [qExpand_coeff_mul, coeff_qDecimate, intCast_eq_zero_of_dvd K p (dvd_mul_right _ _),
      zero_pow (Nat.sub_ne_zero_of_lt hp.out.one_lt), zero_mul, sub_zero]
  · rw [qExpand_coeff_of_not_dvd p _ hn, intCast_pow_sub_one_eq_one K p hn, one_mul, sub_self]

theorem qEuler_qExpand (y : LaurentSeries K) :
    ModularCurve.qEuler K (ModularCurve.qExpand K p y) = 0 := by
  ext n
  rw [qEuler_coeff, HahnSeries.coeff_zero]
  by_cases hn : (p : ℤ) ∣ n
  · rw [intCast_eq_zero_of_dvd K p hn, zero_mul]
  · rw [qExpand_coeff_of_not_dvd p _ hn, mul_zero]

theorem iterate_qEuler_mul_qExpand (k : ℕ) (x y : LaurentSeries K) :
    (ModularCurve.qEuler K)^[k] (x * ModularCurve.qExpand K p y) =
      (ModularCurve.qEuler K)^[k] x * ModularCurve.qExpand K p y := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', (ModularCurve.qEuler K).leibniz,
      qEuler_qExpand, smul_zero, zero_add, smul_eq_mul, mul_comm]

theorem qDecimate_mul_qExpand (x y : LaurentSeries K) :
    ModularCurve.qDecimate K p (x * ModularCurve.qExpand K p y) = ModularCurve.qDecimate K p x * y := by
  apply qExpand_injective p
  rw [map_mul (ModularCurve.qExpand K p) (ModularCurve.qDecimate K p x) y, qExpand_qDecimate, qExpand_qDecimate, iterate_qEuler_mul_qExpand, sub_mul]

theorem qDecimate_qEuler (x : LaurentSeries K) :
    ModularCurve.qDecimate K p (ModularCurve.qEuler K x) = 0 := by
  ext k
  rw [coeff_qDecimate, qEuler_coeff, intCast_eq_zero_of_dvd K p (dvd_mul_right _ _), zero_mul,
    HahnSeries.coeff_zero]

theorem pow_eq_qExpand_coeffMap (s : LaurentSeries K) :
    s ^ p = ModularCurve.qExpand K p (ModularCurve.coeffMap (frobenius K p) s) := by
  rw [pow_char_eq_coeffMap_frobenius_qExpand p s, qExpand_coeffMap]

def Q : LaurentSeries K →+ LaurentSeries K where
  toFun f := ModularCurve.qDecimate K p (ModularCurve.qEuler K f * f ^ (p - 1))
  map_zero' := by rw [map_zero, zero_mul, map_zero]
  map_add' f g := by
    obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.out.one_le).symm⟩
    have hp' : (n + 1).Prime := hn ▸ hp.out
    have hpn : p - 1 = n := by omega
    simp only [hpn]
    rw [deriv_add_mul_add_pow K hp' f g, map_add, map_add, qDecimate_qEuler,
      add_zero]

theorem Q_apply (f : LaurentSeries K) :
    Q K p f = ModularCurve.qDecimate K p (ModularCurve.qEuler K f * f ^ (p - 1)) := rfl

omit [CharP K p] in
theorem qExpand_single_zero (c : K) : ModularCurve.qExpand K p (single 0 c) = single 0 c := by
  rw [qExpand_single, mul_zero]

omit hp [CharP K p] in
theorem coeffMap_single_zero (φ : K →+* K) (c : K) :
    ModularCurve.coeffMap φ (single 0 c) = single 0 (φ c) := by
  ext n
  rw [coeffMap_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs <;> simp

theorem Q_of_qEuler_eq (i : ℕ) (h : LaurentSeries K)
    (hh : ModularCurve.qEuler K h = single 0 ((i : ℕ) : K) * h) :
    Q K p h = ModularCurve.qEuler K (ModularCurve.coeffMap (frobenius K p) h) := by
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.out.one_le
  have hpow : ModularCurve.qEuler K h * h ^ (p - 1) =
      h ^ p * ModularCurve.qExpand K p (single 0 ((i : ℕ) : K)) := by
    rw [hh, qExpand_single_zero, mul_assoc, ← pow_succ', hp1, mul_comm]
  rw [Q_apply, hpow, qDecimate_mul_qExpand, pow_eq_qExpand_coeffMap, qDecimate_qExpand, qEuler_coeffMap,
    hh, map_mul (ModularCurve.coeffMap (frobenius K p)), coeffMap_single_zero, map_natCast (frobenius K p), mul_comm]

def piece (i : ℤ) (f : LaurentSeries K) : LaurentSeries K :=
  single i (1 : K) * ModularCurve.qExpand K p (ModularCurve.qDecimate K p (single (-i) (1 : K) * f))

omit [CharP K p] in
theorem coeff_piece (i : ℤ) (f : LaurentSeries K) (n : ℤ) :
    (piece K p i f).coeff n = if (p : ℤ) ∣ n - i then f.coeff n else 0 := by
  rw [piece]
  have hn : n = (n - i) + i := by ring
  conv_lhs => rw [hn, HahnSeries.coeff_single_mul_add, one_mul]
  by_cases hd : (p : ℤ) ∣ n - i
  · rw [if_pos hd]
    obtain ⟨k, hk⟩ := hd
    rw [hk, qExpand_coeff_mul, coeff_qDecimate, ← hk,
      show n - i = n + -i by ring, HahnSeries.coeff_single_mul_add, one_mul]
  · rw [if_neg hd, qExpand_coeff_of_not_dvd p _ hd]

theorem qEuler_piece (i : ℕ) (f : LaurentSeries K) :
    ModularCurve.qEuler K (piece K p i f) = single 0 ((i : ℕ) : K) * piece K p i f := by
  ext n
  rw [qEuler_coeff, HahnSeries.coeff_single_zero_mul, coeff_piece]
  by_cases hd : (p : ℤ) ∣ n - i
  · rw [if_pos hd]
    have h0 : ((n - (i : ℕ) : ℤ) : K) = 0 := intCast_eq_zero_of_dvd K p hd
    rw [Int.cast_sub, Int.cast_natCast, sub_eq_zero] at h0
    rw [h0]
  · rw [if_neg hd, mul_zero, mul_zero]

theorem sum_piece (f : LaurentSeries K) :
    ∑ i ∈ range p, piece K p (i : ℕ) f = f := by
  ext n
  rw [HahnSeries.coeff_sum]
  simp only [coeff_piece]
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  set i₀ : ℕ := (n % (p : ℤ)).toNat with hi₀
  have hi₀' : ((i₀ : ℕ) : ℤ) = n % (p : ℤ) := by
    rw [hi₀, Int.toNat_of_nonneg (Int.emod_nonneg _ hp0.ne')]
  have hmem : i₀ ∈ range p := by
    rw [mem_range, ← Int.ofNat_lt, hi₀']
    exact Int.emod_lt_of_pos _ hp0
  rw [sum_eq_single_of_mem i₀ hmem]
  · rw [if_pos]
    rw [hi₀', ← Int.modEq_iff_dvd]
    exact Int.mod_modEq n p
  · intro j hj hji
    rw [if_neg]
    intro hdvd
    apply hji
    rw [mem_range] at hj
    have hmod : ((j : ℕ) : ℤ) % (p : ℤ) = n % (p : ℤ) := (Int.modEq_iff_dvd.mpr hdvd)
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hj)] at hmod
    exact_mod_cast hmod.trans hi₀'.symm

theorem qDecimate_qEuler_mul_pow (f : LaurentSeries K) :
    ModularCurve.qDecimate K p (ModularCurve.qEuler K f * f ^ (p - 1)) =
      ModularCurve.qEuler K (ModularCurve.coeffMap (frobenius K p) f) := by
  rw [← Q_apply]
  conv_lhs => rw [← sum_piece K p f]
  rw [map_sum]
  rw [sum_congr rfl fun i _ => Q_of_qEuler_eq K p i _ (qEuler_piece K p i f)]
  rw [← map_sum (ModularCurve.qEuler K), ← map_sum (ModularCurve.coeffMap (frobenius K p)), sum_piece]

theorem main (f : LaurentSeries K) :
    ModularCurve.qDecimate K p (f⁻¹ * ModularCurve.qEuler K f) =
      (ModularCurve.coeffMap (frobenius K p) f)⁻¹ *
        ModularCurve.qEuler K (ModularCurve.coeffMap (frobenius K p) f) := by
  by_cases hf : f = 0
  · subst hf
    simp
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.out.one_le
  have hfpow : f ^ p = f ^ (p - 1) * f := by rw [← pow_succ, hp1]
  have hrew : f⁻¹ * ModularCurve.qEuler K f =
      (ModularCurve.qEuler K f * f ^ (p - 1)) *
        ModularCurve.qExpand K p ((ModularCurve.coeffMap (frobenius K p) f)⁻¹) := by
    rw [map_inv₀, ← pow_eq_qExpand_coeffMap, hfpow, mul_inv, ← mul_assoc,
      mul_assoc (ModularCurve.qEuler K f), mul_inv_cancel₀ (pow_ne_zero _ hf), mul_one, mul_comm]
  rw [hrew, qDecimate_mul_qExpand, qDecimate_qEuler_mul_pow, mul_comm]

end Pointwise

end ModularCurve.D6bCore
p2m_reactivate "P2MW.S_ModularCurve_qDecimate_inv_mul_qEuler_eq_inv_mul_qEuler_coeffMap_frobenius.ModularCurve P2MW.S_ModularCurve_qDecimate_inv_mul_qEuler_eq_inv_mul_qEuler_coeffMap_frobenius.ModularCurve.D6bCore"
p2m_reactivate "P2MW.S_ModularCurve_qDecimate_inv_mul_qEuler_eq_inv_mul_qEuler_coeffMap_frobenius.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_qDecimate_inv_mul_qEuler_eq_inv_mul_qEuler_coeffMap_frobenius.ModularCurve P2MW.S_ModularCurve_qDecimate_inv_mul_qEuler_eq_inv_mul_qEuler_coeffMap_frobenius.ModularCurve.D6bCore"

theorem solution
    (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (f : LaurentSeries K) :
    (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩;
      ModularCurve.qDecimate K p (f⁻¹ * ModularCurve.qEuler K f)) =
      (ModularCurve.coeffMap (frobenius K p) f)⁻¹ *
        ModularCurve.qEuler K (ModularCurve.coeffMap (frobenius K p) f) :=
  ModularCurve.D6bCore.main K p f

end S_ModularCurve_qDecimate_inv_mul_qEuler_eq_inv_mul_qEuler_coeffMap_frobenius
end P2MW
export P2MW.S_ModularCurve_qDecimate_inv_mul_qEuler_eq_inv_mul_qEuler_coeffMap_frobenius (solution)
