-- Prove2me | solution 1 for HindsightGain.Uniform.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T01:53:17.166445+00:00
-- url     : https://prove2.me/submissions/94fa140d-8e2d-4ae4-936d-a4d31673a4ce

import Mathlib
import Definitions.Def_HindsightGain_Uniform_model
import Definitions.Def_HindsightGain_Uniform_optima
import Theorems.Thm_HindsightGain_Uniform_lemma_4_2

section
set_option autoImplicit false

namespace HindsightGain.Uniform.Dev.Thm2
open HindsightGain.Uniform

lemma compensated_one {n D r : ℕ} (M : Model n D r) : compensated M 1 = fullVal M := by
  unfold compensated retentionMean thinningMean
  have : ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, thinningMass Finset.univ S 1 * setVal M S
      = setVal M Finset.univ := by
    rw [Finset.sum_eq_single (Finset.univ : Finset (Fin n))]
    · simp [thinningMass]
    · intro S hS hne
      have hlt : S.card < n := by
        have := Finset.card_lt_card (lt_of_le_of_ne (Finset.subset_univ S) hne)
        simpa using this
      have : (Finset.univ : Finset (Fin n)).card - S.card ≠ 0 := by simp; omega
      simp [thinningMass]
      left; omega
    · intro h; exact absurd (Finset.mem_powerset.2 (Finset.subset_univ _)) h
  rw [this]
  simp [setVal, fullVal]

/-- one step, from lemma_4_2 -/
lemma step {n D r : ℕ} (M : Model n D r) (s t b : ℝ) (hs : 1 / 2 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 < t) (ht1 : t ≤ 1) (hb : Real.sqrt (1 - s) ≤ b) :
    compensated M (s * t) - compensated M t ≤
      ((r : ℝ) * Real.sqrt 5 * Real.sqrt (Nat.descFactorial n (r - 1) : ℝ) * frobenius M) *
        (2 : ℝ) ^ ((r : ℝ) / 2) * b * t ^ (-(1 : ℝ) / 2) := by
  have hs0 : 0 < s := by linarith
  have h := (HindsightGain.Uniform.lemma_4_2 M s t hs0 hs1 ht0 ht1).2
  have e : (r : ℝ) * Real.sqrt 5 * (Real.sqrt (1 - s) / s ^ ((r : ℝ) / 2)) *
          t ^ (-(1 : ℝ) / 2) * Real.sqrt (Nat.descFactorial n (r - 1) : ℝ) * frobenius M =
      ((r : ℝ) * Real.sqrt 5 * Real.sqrt (Nat.descFactorial n (r - 1) : ℝ) * frobenius M) *
        (Real.sqrt (1 - s) / s ^ ((r : ℝ) / 2)) * t ^ (-(1 : ℝ) / 2) := by ring
  rw [e] at h
  refine h.trans ?_
  have hQ : 0 ≤ (r : ℝ) * Real.sqrt 5 * Real.sqrt (Nat.descFactorial n (r - 1) : ℝ) * frobenius M := by
    unfold frobenius; positivity
  have hsr : 0 < s ^ ((r : ℝ) / 2) := Real.rpow_pos_of_pos hs0 _
  have hE : Real.sqrt (1 - s) / s ^ ((r : ℝ) / 2) ≤ (2 : ℝ) ^ ((r : ℝ) / 2) * b := by
    rw [div_le_iff₀ hsr]
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((r : ℝ) / 2) * s ^ ((r : ℝ) / 2) := by
      rw [← Real.mul_rpow (by norm_num) hs0.le]
      exact Real.one_le_rpow (by linarith) (by positivity)
    have hb0 : 0 ≤ Real.sqrt (1 - s) := Real.sqrt_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right h1 (hb0.trans hb)]
  have ht : 0 ≤ t ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg ht0.le _
  have := mul_le_mul_of_nonneg_left hE hQ
  nlinarith [mul_le_mul_of_nonneg_right this ht]

lemma w_succ (k : ℕ) :
    (((1 : ℝ) / 2) ^ (k + 1)) ^ (-(1 : ℝ) / 2) = Real.sqrt 2 * (((1 : ℝ) / 2) ^ k) ^ (-(1 : ℝ) / 2) := by
  rw [pow_succ, mul_comm, Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  rw [Real.sqrt_eq_rpow, show (-(1 : ℝ) / 2) = -(1/2) by ring, Real.rpow_neg (by norm_num), one_div]
  rw [Real.inv_rpow (by norm_num), inv_inv]

lemma telescope {n D r : ℕ} (M : Model n D r) (b : ℝ) (hb : 0 ≤ b) (k : ℕ)
    (hb2 : 0 < k → Real.sqrt (1 / 2) ≤ b) :
    compensated M (((1 : ℝ) / 2) ^ k) - compensated M 1 ≤
      ((r : ℝ) * Real.sqrt 5 * Real.sqrt (Nat.descFactorial n (r - 1) : ℝ) * frobenius M) *
        (2 : ℝ) ^ ((r : ℝ) / 2) * b *
        ((((((1 : ℝ) / 2) ^ k) ^ (-(1 : ℝ) / 2)) - 1) / (Real.sqrt 2 - 1)) := by
  have hQ : 0 ≤ (r : ℝ) * Real.sqrt 5 * Real.sqrt (Nat.descFactorial n (r - 1) : ℝ) * frobenius M := by
    unfold frobenius; positivity
  have ha : 0 < Real.sqrt 2 - 1 := by
    have : (1 : ℝ) < Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  induction k with
  | zero => simp
  | succ k ih =>
    have ih := ih (fun hk => hb2 (by omega))
    have st := step M (1 / 2) (((1 : ℝ) / 2) ^ k) b (le_refl _) (by norm_num) (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num))
      (by
        have := hb2 (by omega)
        rwa [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num])
    rw [show (1 : ℝ) / 2 * ((1 : ℝ) / 2) ^ k = ((1 : ℝ) / 2) ^ (k + 1) by ring] at st
    rw [w_succ]
    have e : ∀ w : ℝ, (Real.sqrt 2 * w - 1) / (Real.sqrt 2 - 1) = (w - 1) / (Real.sqrt 2 - 1) + w := by
      intro w; field_simp; ring
    rw [e, mul_add]
    linarith

lemma tel_nonneg {n D r : ℕ} (M : Model n D r) (k : ℕ) :
    0 ≤ compensated M (((1 : ℝ) / 2) ^ k) - compensated M 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := (HindsightGain.Uniform.lemma_4_2 M (1 / 2) (((1 : ℝ) / 2) ^ k) (by norm_num) (by norm_num)
      (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))).1
    rw [show (1 : ℝ) / 2 * ((1 : ℝ) / 2) ^ k = ((1 : ℝ) / 2) ^ (k + 1) by ring] at h
    linarith

lemma sqrt_two_facts : (1 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.4143 := by
  constructor
  · rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- the key bound c(p) - c(1) -/
lemma key {n D r : ℕ} (M : Model n D r) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    0 ≤ compensated M p - compensated M 1 ∧ compensated M p - compensated M 1 ≤
      (8 * (r : ℝ) * (2 : ℝ) ^ ((r : ℝ) / 2)) * p ^ (-(1 : ℝ) / 2) * Real.sqrt (1 - p) *
        Real.sqrt (Nat.descFactorial n (r - 1) : ℝ) * frobenius M := by
  obtain ⟨ha1, ha2⟩ := sqrt_two_facts
  have hex : ∃ k : ℕ, ((1 : ℝ) / 2) ^ k ≤ p := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hp0 (by norm_num : (1 : ℝ) / 2 < 1)
    exact ⟨k, hk.le⟩
  classical
  set l := Nat.find hex with hl
  have hlp : ((1 : ℝ) / 2) ^ l ≤ p := Nat.find_spec hex
  have hE0 : 0 ≤ (2 : ℝ) ^ ((r : ℝ) / 2) := by positivity
  have hF : 0 ≤ Real.sqrt (Nat.descFactorial n (r - 1) : ℝ) * frobenius M := by
    unfold frobenius; positivity
  have hQ : 0 ≤ (r : ℝ) * Real.sqrt 5 * Real.sqrt (Nat.descFactorial n (r - 1) : ℝ) * frobenius M := by
    unfold frobenius; positivity
  have hpw : 0 ≤ p ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hp0.le _
  have hs1' : 0 ≤ Real.sqrt (1 - p) := Real.sqrt_nonneg _
  rcases Nat.eq_zero_or_pos l with h0 | hlpos
  · -- l = 0, p = 1
    have : p = 1 := by
      have := hlp; rw [h0] at this; simp at this; linarith
    subst this
    rw [sub_self]
    refine ⟨le_refl _, ?_⟩
    unfold frobenius; positivity
  · obtain ⟨m, hm⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    have hnot : ¬ ((1 : ℝ) / 2) ^ m ≤ p := Nat.find_min hex (by omega)
    push_neg at hnot
    set t : ℝ := ((1 : ℝ) / 2) ^ m with ht
    have ht0 : 0 < t := by positivity
    have ht1 : t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hlp' : t / 2 ≤ p := by
      have := hlp; rw [hm, pow_succ] at this; rw [ht]; linarith
    set s := p / t with hs
    have hs0 : 0 < s := by positivity
    have hsp : p ≤ s := by
      rw [hs, le_div_iff₀ ht0]; nlinarith
    have hs1 : s ≤ 1 := by rw [hs, div_le_one ht0]; exact hnot.le
    have hs2 : 1 / 2 ≤ s := by rw [hs, le_div_iff₀ ht0]; linarith
    have hst : s * t = p := by rw [hs]; field_simp
    have hbs : Real.sqrt (1 - s) ≤ Real.sqrt (1 - p) := Real.sqrt_le_sqrt (by linarith)
    have st := step M s t (Real.sqrt (1 - p)) hs2 hs1 ht0 ht1 hbs
    rw [hst] at st
    have lower : 0 ≤ compensated M p - compensated M 1 := by
      have h1 := (HindsightGain.Uniform.lemma_4_2 M s t hs0 hs1 ht0 ht1).1
      rw [hst] at h1
      linarith [tel_nonneg M m]
    have tel := telescope M (Real.sqrt (1 - p)) hs1' m (by
      intro hm0
      apply Real.sqrt_le_sqrt
      have : t ≤ 1 / 2 := by
        rw [ht]
        calc ((1 : ℝ) / 2) ^ m ≤ ((1 : ℝ) / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm0
          _ = 1 / 2 := by norm_num
      linarith)
    rw [← ht] at tel
    have hw : t ^ (-(1 : ℝ) / 2) ≤ p ^ (-(1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos hp0 hnot.le (by norm_num)
    have hw1 : 1 ≤ t ^ (-(1 : ℝ) / 2) := by
      apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1 (by norm_num)
    set Q := (r : ℝ) * Real.sqrt 5 * Real.sqrt (Nat.descFactorial n (r - 1) : ℝ) * frobenius M with hQdef
    set E := (2 : ℝ) ^ ((r : ℝ) / 2) with hEdef
    set b := Real.sqrt (1 - p) with hbdef
    set w := t ^ (-(1 : ℝ) / 2) with hwdef
    have hsum : compensated M p - compensated M 1 ≤ Q * E * b * (w + (w - 1) / (Real.sqrt 2 - 1)) := by
      rw [mul_add]; linarith
    have hfrac : w + (w - 1) / (Real.sqrt 2 - 1) ≤ (2 + Real.sqrt 2) * w := by
      have : (w - 1) / (Real.sqrt 2 - 1) ≤ (1 + Real.sqrt 2) * w := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      linarith
    have h5 : Real.sqrt 5 < 2.2361 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have h5' : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
    have hc : Real.sqrt 5 * (2 + Real.sqrt 2) ≤ 8 := by nlinarith
    have hR : 0 ≤ (r : ℝ) * Real.sqrt (Nat.descFactorial n (r - 1) : ℝ) * frobenius M := by
      unfold frobenius; positivity
    have hQR : Q = Real.sqrt 5 * ((r : ℝ) * Real.sqrt (Nat.descFactorial n (r - 1) : ℝ) * frobenius M) := by
      rw [hQdef]; ring
    set R := (r : ℝ) * Real.sqrt (Nat.descFactorial n (r - 1) : ℝ) * frobenius M with hRdef
    have hX : Q * E * b * (w + (w - 1) / (Real.sqrt 2 - 1)) ≤ Q * E * b * ((2 + Real.sqrt 2) * p ^ (-(1 : ℝ) / 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc _ ≤ (2 + Real.sqrt 2) * w := hfrac
        _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)
    have hfin : Q * E * b * ((2 + Real.sqrt 2) * p ^ (-(1 : ℝ) / 2)) ≤ 8 * R * E * p ^ (-(1 : ℝ) / 2) * b := by
      have h0 : 0 ≤ R * E * b * p ^ (-(1 : ℝ) / 2) := by positivity
      have e1 : Q * E * b * ((2 + Real.sqrt 2) * p ^ (-(1 : ℝ) / 2)) =
          (Real.sqrt 5 * (2 + Real.sqrt 2)) * (R * E * b * p ^ (-(1 : ℝ) / 2)) := by
        rw [hQR]; ring
      rw [e1]
      calc _ ≤ 8 * (R * E * b * p ^ (-(1 : ℝ) / 2)) := mul_le_mul_of_nonneg_right hc h0
        _ = _ := by ring
    have hgoal : 8 * R * E * p ^ (-(1 : ℝ) / 2) * b =
        (8 * (r : ℝ) * E) * p ^ (-(1 : ℝ) / 2) * b * Real.sqrt (Nat.descFactorial n (r - 1) : ℝ) * frobenius M := by
      rw [hRdef]; ring
    exact ⟨lower, by linarith⟩

end HindsightGain.Uniform.Dev.Thm2

namespace HindsightGain.Uniform
open HindsightGain.Uniform.Dev.Thm2 in
theorem chk_theorem_2 {n D r : ℕ} (M : Model n D r) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    0 ≤ retentionMean M p - p ^ r * fullVal M ∧
      retentionMean M p - p ^ r * fullVal M ≤
        (8 * (r : ℝ) * (2 : ℝ) ^ ((r : ℝ) / 2)) *
          p ^ ((r : ℝ) - (1 : ℝ) / 2) * Real.sqrt (1 - p) *
            (n : ℝ) ^ (((r : ℝ) - 1) / 2) * frobenius M := by
  obtain ⟨k0, k1⟩ := key M p hp0 hp1
  rw [← compensated_one M]
  have hpr : 0 < p ^ r := pow_pos hp0 r
  have hid : retentionMean M p - p ^ r * compensated M 1 = p ^ r * (compensated M p - compensated M 1) := by
    have : retentionMean M p = p ^ r * compensated M p := by
      unfold compensated; field_simp
    rw [this]; ring
  rw [hid]
  refine ⟨mul_nonneg hpr.le k0, ?_⟩
  have hd : Real.sqrt (Nat.descFactorial n (r - 1) : ℝ) ≤ (n : ℝ) ^ (((r : ℝ) - 1) / 2) := by
    rw [Real.sqrt_eq_rpow]
    have hle : (Nat.descFactorial n (r - 1) : ℝ) ≤ (n : ℝ) ^ (r - 1) := by
      exact_mod_cast Nat.descFactorial_le_pow n (r - 1)
    have hr : 2 ≤ r := M.hr
    calc _ ≤ ((n : ℝ) ^ (r - 1)) ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by positivity) hle (by norm_num)
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hpe : p ^ r * p ^ (-(1 : ℝ) / 2) = p ^ ((r : ℝ) - (1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hp0]; congr 1; ring
  have hF : 0 ≤ frobenius M := Real.sqrt_nonneg _
  have hE : 0 ≤ (8 * (r : ℝ) * (2 : ℝ) ^ ((r : ℝ) / 2)) := by positivity
  have hP : 0 ≤ p ^ (-(1 : ℝ) / 2) := by positivity
  have hb : 0 ≤ Real.sqrt (1 - p) := Real.sqrt_nonneg _
  have step2 := mul_le_mul_of_nonneg_left k1 hpr.le
  refine step2.trans ?_
  rw [← hpe]
  have h0 : 0 ≤ (8 * (r : ℝ) * (2 : ℝ) ^ ((r : ℝ) / 2)) * p ^ r * p ^ (-(1 : ℝ) / 2) * Real.sqrt (1 - p) * frobenius M := by positivity
  have := mul_le_mul_of_nonneg_left hd h0
  nlinarith [this]

end HindsightGain.Uniform
end

theorem solution : type_of% @HindsightGain.Uniform.chk_theorem_2 := @HindsightGain.Uniform.chk_theorem_2
