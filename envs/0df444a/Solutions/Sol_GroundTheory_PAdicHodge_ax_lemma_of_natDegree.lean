-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ax_lemma_of_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:50:04.925489+00:00
-- url     : https://prove2.me/submissions/357195e1-dc3d-4b49-a536-2f0ee6b415e4

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Theorems.Thm_GroundTheory_PAdicHodge_not_dvd_choose_pow_of_lt
import Theorems.Thm_GroundTheory_PAdicHodge_not_sq_dvd_choose_pow_pow
import Theorems.Thm_GroundTheory_PAdicHodge_norm_natCast_padicAlgCl_of_not_dvd
import Theorems.Thm_GroundTheory_PAdicHodge_inv_le_norm_natCast_padicAlgCl
import Theorems.Thm_GroundTheory_PAdicHodge_exists_close_of_hasseDeriv
import Theorems.Thm_GroundTheory_PAdicHodge_norm_gal_apply_sub_le
import Theorems.Thm_GroundTheory_PAdicHodge_one_lt_prime_cast
import Theorems.Thm_GroundTheory_PAdicHodge_axExponent_succ
import Theorems.Thm_GroundTheory_PAdicHodge_one_le_rpow_axExponent
import Theorems.Thm_GroundTheory_PAdicHodge_rpow_axExponent_mono
import Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_le_max_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (d : ℕ) : ∀ x : PadicAlgCl p, (minpoly K x).natDegree = d →
    ∀ ρ : ℝ, (∀ σ : Gal(PadicAlgCl p/K), ‖σ x - x‖ ≤ ρ) →
      ∃ y ∈ K, ‖x - y‖ ≤ (p : ℝ) ^ axExponent p (Nat.log p d) * ρ := by
  induction d using Nat.strong_induction_on with
  | _ d IH =>
  intro x hxd ρ hρ
  have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hρ0 : 0 ≤ ρ := by simpa using hρ 1
  have hp1 := one_lt_prime_cast (p := p)
  have hdpos : 0 < d := hxd ▸ minpoly.natDegree_pos hx

  by_cases hd1 : d = 1
  · obtain ⟨k, hk⟩ := (minpoly.natDegree_eq_one_iff).1 (hxd.trans hd1)
    refine ⟨(k : PadicAlgCl p), k.2, ?_⟩
    rw [← hk]
    change ‖(k : PadicAlgCl p) - (k : PadicAlgCl p)‖ ≤ _
    rw [sub_self, norm_zero]
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) hρ0
  have hd2 : 2 ≤ d := by omega
  set k := Nat.log p d with hk
  have hk1 : p ^ k ≤ d := Nat.pow_log_le_self p (by omega)
  have hk2 : d < p ^ (k + 1) := Nat.lt_pow_succ_log_self hp.out.one_lt d
  have hpk : 0 < p ^ k := pow_pos hp.out.pos k
  by_cases hpow : d = p ^ k
  ·
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := by
      refine ⟨k - 1, ?_⟩
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, pow_zero] at hpow; omega
      · omega
    have hqd : p ^ j < d := by
      rw [hpow, hj, pow_succ]
      exact lt_mul_of_one_lt_right (pow_pos hp.out.pos j) hp.out.one_lt
    obtain ⟨b, hbdeg, hb⟩ := exists_close_of_hasseDeriv x hρ (hxd ▸ hqd)
    rw [hxd] at hbdeg hb
    set m := d - p ^ j with hm
    have hm0 : m ≠ 0 := by omega
    have hmreal : (m : ℝ) = (p : ℝ) ^ j * ((p : ℝ) - 1) := by
      rw [hm, Nat.cast_sub hqd.le, hpow, hj]
      push_cast
      ring
    have hmpos : (0 : ℝ) < m := by positivity

    have hchoose : (p : ℝ)⁻¹ ≤ ‖((Nat.choose d (p ^ j) : ℕ) : PadicAlgCl p)‖ := by
      have h := not_sq_dvd_choose_pow_pow (p := p) (k := k) (by omega)
      rw [hj, Nat.add_sub_cancel] at h
      rw [hpow, hj]
      exact inv_le_norm_natCast_padicAlgCl (Nat.choose_pos (by
        rw [pow_succ]; exact Nat.le_mul_of_pos_right _ hp.out.pos)).ne' h
    set c : ℝ := (p : ℝ) ^ ((1 : ℝ) / m) with hc
    have hc1 : 1 ≤ c := Real.one_le_rpow hp1.le (by positivity)
    have hcm : c ^ m = p := by
      rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), one_div,
        inv_mul_cancel₀ hmpos.ne', Real.rpow_one]
    have hxb : ‖x - b‖ ≤ c * ρ := by
      by_contra hlt
      replace hlt := lt_of_not_ge hlt
      have h1 : (c * ρ) ^ m < ‖x - b‖ ^ m :=
        pow_lt_pow_left₀ hlt (mul_nonneg (by linarith) hρ0) hm0
      rw [mul_pow, hcm] at h1
      have h2 : (p : ℝ)⁻¹ * ‖x - b‖ ^ m ≤ ρ ^ m :=
        (mul_le_mul_of_nonneg_right hchoose (pow_nonneg (norm_nonneg _) _)).trans hb
      have h3 : ‖x - b‖ ^ m ≤ p * ρ ^ m := by
        rw [inv_mul_le_iff₀ (by linarith)] at h2
        exact h2
      linarith
    have hρc : ρ ≤ c * ρ := le_mul_of_one_le_left hρ0 hc1
    have hbρ : ∀ σ : Gal(PadicAlgCl p/K), ‖σ b - b‖ ≤ c * ρ := fun σ =>
      (norm_gal_apply_sub_le x b hρ σ).trans (max_le hxb hρc)
    have hpj : 0 < p ^ j := pow_pos hp.out.pos j
    have hbd : (minpoly K b).natDegree < d := by omega
    obtain ⟨y, hyK, hy⟩ := IH _ hbd b rfl (c * ρ) hbρ
    refine ⟨y, hyK, ?_⟩
    have hlog : Nat.log p (minpoly K b).natDegree ≤ j := by
      have hb0 : (minpoly K b).natDegree ≠ 0 :=
        (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral b)).ne'
      have : (minpoly K b).natDegree < p ^ (j + 1) := by
        rw [← hj]; omega
      exact Nat.lt_succ_iff.1 (Nat.log_lt_of_lt_pow hb0 this)
    have hEk : (p : ℝ) ^ axExponent p k = (p : ℝ) ^ axExponent p j * c := by
      rw [hj, axExponent_succ, Real.rpow_add (by linarith), hc, hmreal]
    have hy' : ‖b - y‖ ≤ (p : ℝ) ^ axExponent p j * (c * ρ) :=
      hy.trans (mul_le_mul_of_nonneg_right (rpow_axExponent_mono hlog)
        (mul_nonneg (by linarith) hρ0))
    refine (norm_sub_le_max_of_le hxb hy').trans (max_le ?_ ?_)
    · rw [hEk, mul_assoc]
      exact le_mul_of_one_le_left (mul_nonneg (by linarith) hρ0) (one_le_rpow_axExponent j)
    · rw [hEk, mul_assoc]
  ·
    have hlt : p ^ k < d := lt_of_le_of_ne hk1 (Ne.symm hpow)
    have hqd : d - p ^ k < d := by omega
    obtain ⟨b, hbdeg, hb⟩ := exists_close_of_hasseDeriv x hρ (hxd ▸ hqd)
    rw [hxd] at hbdeg hb
    have hm : d - (d - p ^ k) = p ^ k := by omega
    rw [hm, Nat.choose_symm hk1,
      norm_natCast_padicAlgCl_of_not_dvd (not_dvd_choose_pow_of_lt hk1 hk2), one_mul] at hb
    rw [hm] at hbdeg
    have hxb : ‖x - b‖ ≤ ρ := (pow_le_pow_iff_left₀ (norm_nonneg _) hρ0 hpk.ne').1 hb
    have hbρ : ∀ σ : Gal(PadicAlgCl p/K), ‖σ b - b‖ ≤ ρ := fun σ =>
      (norm_gal_apply_sub_le x b hρ σ).trans (max_le hxb le_rfl)
    have hbd : (minpoly K b).natDegree < d := by omega
    obtain ⟨y, hyK, hy⟩ := IH _ hbd b rfl ρ hbρ
    refine ⟨y, hyK, ?_⟩
    have hy' : ‖b - y‖ ≤ (p : ℝ) ^ axExponent p k * ρ :=
      hy.trans (mul_le_mul_of_nonneg_right (rpow_axExponent_mono
        (Nat.log_mono_right hbd.le)) hρ0)
    refine (norm_sub_le_max_of_le hxb hy').trans (max_le ?_ le_rfl)
    exact le_mul_of_one_le_left hρ0 (one_le_rpow_axExponent k)
end GroundTheory.PAdicHodge
