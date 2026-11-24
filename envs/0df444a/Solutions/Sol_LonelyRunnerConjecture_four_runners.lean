-- Prove2me | solution 1 for LonelyRunnerConjecture.four_runners
-- status  : ACCEPTED   (prove)
-- author  : @bbchallenge_user
-- created : 2026-11-24T21:41:21.375988+00:00
-- url     : https://prove2.me/submissions/4a461d13-d0cb-4a3d-b0da-ad46ea1bb61e

import Mathlib
import Definitions.Def_LonelyRunnerConjecture_Defs

namespace LonelyRunnerConjecture.FourRunnersAux
open LonelyRunnerConjecture

lemma dist_add_int (x : ℝ) (n : ℤ) : distToNearestInt (x + n) = distToNearestInt x := by
  simp [distToNearestInt, Int.fract_add_intCast]

lemma dist_neg (x : ℝ) : distToNearestInt (-x) = distToNearestInt x := by
  unfold distToNearestInt
  by_cases h : Int.fract x = 0
  · have h' : Int.fract (-x) = 0 := by rw [Int.fract_neg_eq_zero]; exact h
    rw [h, h']
  · rw [Int.fract_neg h, sub_sub_cancel, min_comm]

lemma dist_of_mem (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) :
    distToNearestInt x = min x (1 - x) := by
  unfold distToNearestInt
  rw [Int.fract_eq_self.mpr ⟨h0, h1⟩]

theorem lrc_zero : LRC 0 := by
  intro S hS _
  refine ⟨0, ?_⟩
  intro v hv
  rw [Finset.card_eq_zero] at hS
  simp [hS] at hv

theorem lrc_one : LRC 1 := by
  intro S hS hpos
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hS
  have ha : (0 : ℝ) < a := by exact_mod_cast hpos a (Finset.mem_singleton_self a)
  refine ⟨1 / (2 * a), ?_⟩
  intro v hv
  rw [Finset.mem_singleton] at hv
  subst hv
  have : 1 / (2 * (v : ℝ)) * v = 1 / 2 := by field_simp
  rw [this, dist_of_mem _ (by norm_num) (by norm_num)]
  norm_num

theorem lrc_two : LRC 2 := by
  intro S hS hpos
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
  have ha : 0 < a := hpos a (by simp)
  have hb : 0 < b := hpos b (by simp)
  set g := Nat.gcd a b with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b ha
  obtain ⟨a', ha'⟩ : g ∣ a := Nat.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ : g ∣ b := Nat.gcd_dvd_right a b
  have hcop : Nat.Coprime a' b' := by
    have := Nat.coprime_div_gcd_div_gcd (m := a) (n := b) hgpos
    rwa [← hg, ha', hb', Nat.mul_div_cancel_left _ hgpos, Nat.mul_div_cancel_left _ hgpos] at this
  have ha'pos : 0 < a' := by
    rcases Nat.eq_zero_or_pos a' with h | h
    · rw [h] at ha'; omega
    · exact h
  have hb'pos : 0 < b' := by
    rcases Nat.eq_zero_or_pos b' with h | h
    · rw [h] at hb'; omega
    · exact h
  have hab' : a' ≠ b' := by
    intro h; apply hab; rw [ha', hb', h]
  set M := a' + b' with hM
  have hM3 : 3 ≤ M := by omega
  have hcopM : Nat.Coprime a' M := by
    rw [hM]
    exact (Nat.coprime_add_self_right).mpr hcop |>.symm.symm |> fun h => by
      simpa [Nat.Coprime, Nat.gcd_comm, add_comm] using
        (Nat.coprime_add_self_right (m := a') (n := b')).mpr hcop
  obtain ⟨w, -, hw⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcopM (by omega)
  set m := (M + 2) / 3 with hm
  have hm1 : M ≤ 3 * m := by omega
  have hm2 : 3 * m ≤ 2 * M := by omega
  have hmM : m < M := by omega
  set u := w * m with hu
  have hmod : a' * u % M = m := by
    rw [hu, ← mul_assoc, Nat.mul_mod, hw, one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hmM]
  set q := a' * u / M with hq
  have hdiv : a' * u = M * q + m := by rw [← hmod, hq]; exact (Nat.div_add_mod _ _).symm
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hgR : (0 : ℝ) < g := by exact_mod_cast hgpos
  set X : ℝ := (m : ℝ) / M with hX
  have hX0 : 0 ≤ X := by positivity
  have hX1 : X < 1 := by rw [hX, div_lt_one hMpos]; exact_mod_cast hmM
  have hXlo : 1 / 3 ≤ X := by
    rw [hX, le_div_iff₀ hMpos]; have : (M : ℝ) ≤ 3 * m := by exact_mod_cast hm1
    linarith
  have hXhi : X ≤ 2 / 3 := by
    rw [hX, div_le_iff₀ hMpos]; have : (3 * m : ℝ) ≤ 2 * M := by exact_mod_cast hm2
    linarith
  have hdX : 1 / 3 ≤ distToNearestInt X := by
    rw [dist_of_mem X hX0 hX1]
    exact le_min hXlo (by linarith)
  have hdivR : (a' : ℝ) * u = M * q + m := by exact_mod_cast hdiv
  have hMR : (M : ℝ) = a' + b' := by rw [hM]; push_cast; ring
  refine ⟨(u : ℝ) / (g * M), ?_⟩
  intro v hv
  have hk : (1 : ℝ) / ((2 : ℕ) + 1 : ℝ) = 1 / 3 := by norm_num
  rw [hk]
  rcases Finset.mem_insert.mp hv with rfl | hv
  · have : (u : ℝ) / (g * M) * (v : ℝ) = X + (q : ℤ) := by
      rw [ha']; push_cast
      rw [hX]; field_simp
      linear_combination hdivR
    rw [this, dist_add_int]; exact hdX
  · rw [Finset.mem_singleton] at hv
    subst hv
    have : (u : ℝ) / (g * M) * (v : ℝ) = -X + ((u : ℤ) - (q : ℤ) : ℤ) := by
      rw [hb']; push_cast
      rw [hX]; field_simp
      linear_combination (-1 : ℝ) * hdivR - (u : ℝ) * hMR
    rw [this, dist_add_int, dist_neg]; exact hdX


/-! ## Four runners (k = 3), following Renault's extremal argument, discretized -/

noncomputable def F (v : ℕ) (t : ℝ) : ℝ := Int.fract (t * v)
def Safe (v : ℕ) (t : ℝ) : Prop := 1/4 ≤ F v t ∧ F v t ≤ 3/4
def Good (a b c : ℕ) : Prop := ∃ t, Safe a t ∧ Safe b t ∧ Safe c t

lemma F_nonneg (v : ℕ) (t : ℝ) : 0 ≤ F v t := Int.fract_nonneg _
lemma F_lt_one (v : ℕ) (t : ℝ) : F v t < 1 := Int.fract_lt_one _

lemma dist_of_safe {v : ℕ} {t : ℝ} (h : Safe v t) : 1/4 ≤ distToNearestInt (t * v) := by
  have h1 := h.1; have h2 := h.2
  unfold F at h1 h2
  unfold distToNearestInt
  exact le_min h1 (by linarith)

lemma F_of_dist {v : ℕ} {t : ℝ} (h : 1/3 ≤ distToNearestInt (t * v)) :
    1/3 ≤ F v t ∧ F v t ≤ 2/3 := by
  unfold distToNearestInt at h
  rw [le_min_iff] at h
  unfold F
  constructor <;> linarith [h.1, h.2]

lemma fract_add_small (y δ : ℝ) (h0 : 0 ≤ δ) (h1 : Int.fract y + δ < 1) :
    Int.fract (y + δ) = Int.fract y + δ := by
  rw [Int.fract_eq_iff]
  refine ⟨by linarith [Int.fract_nonneg y], h1, ⌊y⌋, ?_⟩
  rw [← Int.self_sub_fract y]; ring

lemma F_shift (v : ℕ) (t s : ℝ) (hs : 0 ≤ s) (h : F v t + v * s < 1) :
    F v (t + s) = F v t + v * s := by
  unfold F at *
  rw [show (t + s) * (v : ℝ) = t * v + v * s by ring]
  exact fract_add_small _ _ (by positivity) h

lemma fract_congr_fract (x c : ℝ) : Int.fract (x + c) = Int.fract (Int.fract x + c) := by
  conv_lhs => rw [← Int.fract_add_floor x]
  rw [show Int.fract x + (⌊x⌋ : ℝ) + c = (Int.fract x + c) + (⌊x⌋ : ℝ) by ring,
    Int.fract_add_intCast]

lemma F_half_even (v : ℕ) (hv : 2 ∣ v) (t : ℝ) : F v (t + 1/2) = F v t := by
  obtain ⟨k, rfl⟩ := hv
  unfold F; push_cast
  rw [show (t + 1/2) * (2 * (k:ℝ)) = t * (2 * k) + ((k:ℤ):ℝ) by push_cast; ring,
    Int.fract_add_intCast]

lemma F_half_odd (v : ℕ) (hv : ¬ 2 ∣ v) (t : ℝ) :
    F v (t + 1/2) = Int.fract (F v t + 1/2) := by
  obtain ⟨k, rfl⟩ : ∃ k, v = 2 * k + 1 := ⟨v / 2, by omega⟩
  unfold F; push_cast
  rw [show (t + 1/2) * (2 * (k:ℝ) + 1) = (t * (2 * k + 1) + 1/2) + ((k:ℤ):ℝ) by push_cast; ring,
    Int.fract_add_intCast, fract_congr_fract]

lemma F_mul (v n : ℕ) (t : ℝ) : F v (n * t) = Int.fract (n * F v t) := by
  unfold F
  have h := Int.fract_add_floor (t * v)
  rw [show (n : ℝ) * t * v = n * Int.fract (t * v) + ((n * ⌊t * v⌋ : ℤ) : ℝ) by
    push_cast; rw [← mul_add, h]; ring, Int.fract_add_intCast]

lemma F_neg (v : ℕ) (t : ℝ) (h : F v t ≠ 0) : F v (-t) = 1 - F v t := by
  unfold F at *
  rw [neg_mul, Int.fract_neg h]

lemma fract_of_mem (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) : Int.fract x = x :=
  Int.fract_eq_self.mpr ⟨h0, h1⟩

lemma fract_sub_one (x : ℝ) (h0 : 1 ≤ x) (h1 : x < 2) : Int.fract x = x - 1 := by
  rw [Int.fract_eq_iff]
  exact ⟨by linarith, by linarith, 1, by push_cast; ring⟩

lemma fract_sub_two (x : ℝ) (h0 : 2 ≤ x) (h1 : x < 3) : Int.fract x = x - 2 := by
  rw [Int.fract_eq_iff]
  exact ⟨by linarith, by linarith, 2, by push_cast; ring⟩

lemma integral_b (a b c : ℕ) (t : ℝ) (h : F b t = 3/4) :
    ∃ n : ℤ, (4 * b * c : ℝ) * F a t = n := by
  unfold F at *
  have hb : t * b = (⌊t * b⌋ : ℝ) + 3/4 := by rw [← h, Int.floor_add_fract]
  refine ⟨a * c * (4 * ⌊t * b⌋ + 3) - 4 * b * c * ⌊t * a⌋, ?_⟩
  have ha := Int.floor_add_fract (t * (a : ℝ))
  have : Int.fract (t * (a : ℝ)) = t * a - ⌊t * (a : ℝ)⌋ := by linarith
  rw [this]; push_cast
  linear_combination (4 * (a : ℝ) * c) * hb

lemma integral_c (a b c : ℕ) (t : ℝ) (h : F c t = 3/4) :
    ∃ n : ℤ, (4 * b * c : ℝ) * F a t = n := by
  unfold F at *
  have hc : t * c = (⌊t * c⌋ : ℝ) + 3/4 := by rw [← h, Int.floor_add_fract]
  refine ⟨a * b * (4 * ⌊t * c⌋ + 3) - 4 * b * c * ⌊t * a⌋, ?_⟩
  have ha := Int.floor_add_fract (t * (a : ℝ))
  have : Int.fract (t * (a : ℝ)) = t * a - ⌊t * (a : ℝ)⌋ := by linarith
  rw [this]; push_cast
  linear_combination (4 * (a : ℝ) * b) * hc

/-- Flow forward until runner `b` or `c` reaches `3/4`. -/
lemma flow (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hng : ¬ Good a b c) (t : ℝ)
    (hb1 : 1/4 ≤ F b t) (hb2 : F b t ≤ 3/4) (hc1 : 1/4 ≤ F c t) (hc2 : F c t ≤ 3/4)
    (ha1 : F a t < 1/4) :
    ∃ s, 0 ≤ s ∧ Safe b (t + s) ∧ Safe c (t + s) ∧ (F b (t + s) = 3/4 ∨ F c (t + s) = 3/4) ∧
      F a (t + s) = F a t + a * s ∧ F a (t + s) < 1/4 ∧
      (F b t < 3/4 → F c t < 3/4 → 0 < s) := by
  have haR : (0:ℝ) < a := by exact_mod_cast ha
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hcR : (0:ℝ) < c := by exact_mod_cast hc
  have ha0 := F_nonneg a t
  set s := min ((3/4 - F b t) / b) ((3/4 - F c t) / c) with hs
  have hs0 : 0 ≤ s := le_min (div_nonneg (by linarith) hbR.le) (div_nonneg (by linarith) hcR.le)
  have hsb : (b : ℝ) * s ≤ 3/4 - F b t := by
    have := min_le_left ((3/4 - F b t) / b) ((3/4 - F c t) / c)
    rw [← hs, le_div_iff₀ hbR] at this; linarith
  have hsc : (c : ℝ) * s ≤ 3/4 - F c t := by
    have := min_le_right ((3/4 - F b t) / b) ((3/4 - F c t) / c)
    rw [← hs, le_div_iff₀ hcR] at this; linarith
  have hFb : F b (t + s) = F b t + b * s := F_shift b t s hs0 (by linarith)
  have hFc : F c (t + s) = F c t + c * s := F_shift c t s hs0 (by linarith)
  have heq : F b (t + s) = 3/4 ∨ F c (t + s) = 3/4 := by
    rcases min_choice ((3/4 - F b t) / b) ((3/4 - F c t) / c) with h | h
    · left; rw [hFb, show s = (3/4 - F b t) / b from hs.trans h]; field_simp; ring
    · right; rw [hFc, show s = (3/4 - F c t) / c from hs.trans h]; field_simp; ring
  by_cases hlt : F a t + a * s < 1/4
  · have hFa : F a (t + s) = F a t + a * s := F_shift a t s hs0 (by linarith)
    refine ⟨s, hs0, ⟨by rw [hFb]; nlinarith, by rw [hFb]; linarith⟩,
      ⟨by rw [hFc]; nlinarith, by rw [hFc]; linarith⟩, heq, hFa, by rw [hFa]; exact hlt, ?_⟩
    intro h1 h2
    exact lt_min (div_pos (by linarith) hbR) (div_pos (by linarith) hcR)
  · exfalso; apply hng
    set s' := (1/4 - F a t) / a with hs'
    have hs'0 : 0 ≤ s' := div_nonneg (by linarith) haR.le
    have has' : (a : ℝ) * s' = 1/4 - F a t := by rw [hs']; field_simp
    have hs's : s' ≤ s := by
      rw [hs', div_le_iff₀ haR]; linarith
    have hbs' : (b : ℝ) * s' ≤ b * s := mul_le_mul_of_nonneg_left hs's hbR.le
    have hcs' : (c : ℝ) * s' ≤ c * s := mul_le_mul_of_nonneg_left hs's hcR.le
    have hFa : F a (t + s') = 1/4 := by rw [F_shift a t s' hs'0 (by linarith)]; linarith
    have hFb' : F b (t + s') = F b t + b * s' := F_shift b t s' hs'0 (by linarith)
    have hFc' : F c (t + s') = F c t + c * s' := F_shift c t s' hs'0 (by linarith)
    refine ⟨t + s', ⟨by rw [hFa], by rw [hFa]; norm_num⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [hFb']; nlinarith
    · rw [hFb']; linarith
    · rw [hFc']; nlinarith
    · rw [hFc']; linarith

def Q (a b c : ℕ) (n : ℤ) : Prop :=
  ∃ t, Safe b t ∧ Safe c t ∧ (F b t = 3/4 ∨ F c t = 3/4) ∧ 0 < F a t ∧ F a t < 1/4 ∧
    (4 * b * c : ℝ) * F a t = n

lemma to_Q (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hng : ¬ Good a b c) (t : ℝ)
    (hb1 : 1/4 ≤ F b t) (hb2 : F b t ≤ 3/4) (hc1 : 1/4 ≤ F c t) (hc2 : F c t ≤ 3/4)
    (ha1 : F a t < 1/4) (hpos : 0 < F a t ∨ (F b t < 3/4 ∧ F c t < 3/4)) :
    ∃ n : ℤ, Q a b c n ∧ (4 * b * c : ℝ) * F a t ≤ n ∧
      ((F b t < 3/4 ∧ F c t < 3/4) → (4 * b * c : ℝ) * F a t < n) := by
  obtain ⟨s, hs0, hbS, hcS, h34, hFa, hFa1, hspos⟩ :=
    flow a b c ha hb hc hng t hb1 hb2 hc1 hc2 ha1
  have haR : (0:ℝ) < a := by exact_mod_cast ha
  have hbcR : (0:ℝ) < 4 * b * c := by positivity
  have ha0 := F_nonneg a t
  have hpos' : 0 < F a (t + s) := by
    rw [hFa]
    rcases hpos with h | ⟨h1, h2⟩
    · nlinarith
    · have := hspos h1 h2; nlinarith
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (4 * b * c : ℝ) * F a (t + s) = n := by
    rcases h34 with h | h
    · exact integral_b a b c (t + s) h
    · exact integral_c a b c (t + s) h
  refine ⟨n, ⟨t + s, hbS, hcS, h34, hpos', hFa1, hn⟩, ?_, ?_⟩
  · rw [← hn, hFa]
    have h0 : 0 ≤ (a : ℝ) * s := mul_nonneg haR.le hs0
    exact mul_le_mul_of_nonneg_left (by linarith) hbcR.le
  · rintro ⟨h1, h2⟩
    have := hspos h1 h2
    rw [← hn, hFa]
    have h0 : 0 < (a : ℝ) * s := mul_pos haR this
    exact mul_lt_mul_of_pos_left (by linarith) hbcR

lemma Q_swap {a b c : ℕ} {n : ℤ} (h : Q a c b n) : Q a b c n := by
  obtain ⟨t, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨t, h2, h1, h3.symm, h4, h5, by rw [← h6]; ring⟩

lemma good_swap {a b c : ℕ} (h : Good a c b) : Good a b c := by
  obtain ⟨t, h1, h2, h3⟩ := h
  exact ⟨t, h1, h3, h2⟩

lemma fract_five_quarters : Int.fract ((3:ℝ)/4 + 1/2) = 1/4 := by
  rw [fract_sub_one _ (by norm_num) (by norm_num)]; norm_num

/-- Renault's step: from a boundary time with `b` at `3/4`, find a better boundary time. -/
lemma step (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h4 : 4 ∣ a)
    (hpar : ¬ (2 ∣ b ∧ 2 ∣ c)) (hng : ¬ Good a b c) (t0 : ℝ)
    (hbS : Safe b t0) (hcS : Safe c t0) (hb34 : F b t0 = 3/4)
    (hx0 : 0 < F a t0) (hx1 : F a t0 < 1/4) :
    ∃ m : ℤ, Q a b c m ∧ (4 * b * c : ℝ) * F a t0 < m := by
  have h2a : 2 ∣ a := dvd_trans ⟨2, by norm_num⟩ h4
  have hbcR : (0:ℝ) < 4 * b * c := by positivity
  set x := F a t0 with hx
  by_cases hc2 : 2 ∣ c
  · have hb2 : ¬ 2 ∣ b := fun h => hpar ⟨h, hc2⟩
    by_cases hclt : F c t0 < 3/4
    · -- shift by 1/2, then flow strictly forward
      have hA : F a (t0 + 1/2) = x := F_half_even a h2a t0
      have hC : F c (t0 + 1/2) = F c t0 := F_half_even c hc2 t0
      have hB : F b (t0 + 1/2) = 1/4 := by
        rw [F_half_odd b hb2, hb34, fract_five_quarters]
      obtain ⟨m, hm, -, hlt⟩ := to_Q a b c ha hb hc hng (t0 + 1/2)
        (by rw [hB]) (by rw [hB]; norm_num) (by rw [hC]; exact hcS.1) (by rw [hC]; exact hcS.2)
        (by rw [hA]; exact hx1) (Or.inl (by rw [hA]; exact hx0))
      refine ⟨m, hm, ?_⟩
      have := hlt ⟨by rw [hB]; norm_num, by rw [hC]; exact hclt⟩
      rwa [hA] at this
    · have hc34 : F c t0 = 3/4 := le_antisymm hcS.2 (not_lt.mp hclt)
      have hA : F a (2 * t0) = 2 * x := by
        have := F_mul a 2 t0; push_cast at this
        rw [this, fract_of_mem _ (by linarith) (by linarith)]
      have hB : F b (2 * t0) = 1/2 := by
        have := F_mul b 2 t0; push_cast at this
        rw [this, hb34, fract_sub_one _ (by norm_num) (by norm_num)]; norm_num
      have hC : F c (2 * t0) = 1/2 := by
        have := F_mul c 2 t0; push_cast at this
        rw [this, hc34, fract_sub_one _ (by norm_num) (by norm_num)]; norm_num
      by_cases h2x : 1/4 ≤ 2 * x
      · exact absurd ⟨2 * t0, ⟨by rw [hA]; exact h2x, by rw [hA]; linarith⟩,
          ⟨by rw [hB]; norm_num, by rw [hB]; norm_num⟩,
          ⟨by rw [hC]; norm_num, by rw [hC]; norm_num⟩⟩ hng
      · rw [not_le] at h2x
        obtain ⟨m, hm, hle, -⟩ := to_Q a b c ha hb hc hng (2 * t0)
          (by rw [hB]; norm_num) (by rw [hB]; norm_num) (by rw [hC]; norm_num)
          (by rw [hC]; norm_num) (by rw [hA]; exact h2x) (Or.inl (by rw [hA]; linarith))
        refine ⟨m, hm, ?_⟩
        rw [hA] at hle; nlinarith
  · -- c odd: triple the time, possibly shift by 1/2
    have hA1 : F a (3 * t0) = 3 * x := by
      have := F_mul a 3 t0; push_cast at this
      rw [this, fract_of_mem _ (by linarith) (by linarith)]
    have hB1 : F b (3 * t0) = 1/4 := by
      have := F_mul b 3 t0; push_cast at this
      rw [this, hb34, fract_sub_two _ (by norm_num) (by norm_num)]; norm_num
    have hA2 : F a (3 * t0 + 1/2) = 3 * x := by rw [F_half_even a h2a, hA1]
    have hB2 : Safe b (3 * t0 + 1/2) := by
      by_cases hb2 : 2 ∣ b
      · rw [Safe, F_half_even b hb2, hB1]; norm_num
      · rw [Safe, F_half_odd b hb2, hB1, fract_of_mem _ (by norm_num) (by norm_num)]; norm_num
    have hC2 : F c (3 * t0 + 1/2) = Int.fract (F c (3 * t0) + 1/2) := F_half_odd c hc2 _
    -- some time among 3 t0, 3 t0 + 1/2 has b and c safe
    obtain ⟨ts, hAs, hBs, hCs⟩ : ∃ ts, F a ts = 3 * x ∧ Safe b ts ∧ Safe c ts := by
      by_cases hy : Safe c (3 * t0)
      · exact ⟨3 * t0, hA1, ⟨by rw [hB1], by rw [hB1]; norm_num⟩, hy⟩
      · refine ⟨3 * t0 + 1/2, hA2, hB2, ?_⟩
        have hy0 := F_nonneg c (3 * t0)
        have hy1 := F_lt_one c (3 * t0)
        rw [Safe, not_and_or, not_le, not_le] at hy
        rw [Safe, hC2]
        rcases hy with hy | hy
        · rw [fract_of_mem _ (by linarith) (by linarith)]; constructor <;> linarith
        · rw [fract_sub_one _ (by linarith) (by linarith)]; constructor <;> linarith
    by_cases h3x : 1/4 ≤ 3 * x
    · exact absurd ⟨ts, ⟨by rw [hAs]; exact h3x, by rw [hAs]; linarith⟩, hBs, hCs⟩ hng
    · rw [not_le] at h3x
      obtain ⟨m, hm, hle, -⟩ := to_Q a b c ha hb hc hng ts hBs.1 hBs.2 hCs.1 hCs.2
        (by rw [hAs]; exact h3x) (Or.inl (by rw [hAs]; linarith))
      refine ⟨m, hm, ?_⟩
      rw [hAs] at hle; nlinarith

lemma core (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hbc : b ≠ c) (h4 : 4 ∣ a)
    (hpar : ¬ (2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c)) : Good a b c := by
  by_contra hng
  have h2a : 2 ∣ a := dvd_trans ⟨2, by norm_num⟩ h4
  have hpar' : ¬ (2 ∣ b ∧ 2 ∣ c) := fun h => hpar ⟨h2a, h.1, h.2⟩
  have hng' : ¬ Good a c b := fun h => hng (good_swap h)
  have hbcR : (0:ℝ) < 4 * b * c := by positivity
  have hbound : ∀ n, Q a b c n → n < b * c := by
    rintro n ⟨t, -, -, -, -, h1, hn⟩
    have : (n : ℝ) < b * c := by rw [← hn]; nlinarith
    exact_mod_cast this
  have hstep : ∀ n, Q a b c n → ∃ m, n < m ∧ Q a b c m := by
    rintro n ⟨t, hbS, hcS, h34, hx0, hx1, hn⟩
    rcases h34 with h | h
    · obtain ⟨m, hm, hlt⟩ := step a b c ha hb hc h4 hpar' hng t hbS hcS h hx0 hx1
      exact ⟨m, by rw [hn] at hlt; exact_mod_cast hlt, hm⟩
    · obtain ⟨m, hm, hlt⟩ := step a c b ha hc hb h4 (fun h' => hpar' ⟨h'.2, h'.1⟩) hng' t
        hcS hbS h hx0 hx1
      refine ⟨m, ?_, Q_swap hm⟩
      have : (4 * c * b : ℝ) * F a t = 4 * b * c * F a t := by ring
      rw [this, hn] at hlt; exact_mod_cast hlt
  -- an initial boundary time
  obtain ⟨n0, hQ0⟩ : ∃ n, Q a b c n := by
    obtain ⟨t, ht⟩ := lrc_two {b, c} (Finset.card_pair hbc) (by
      intro v hv; rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hb
      · rw [Finset.mem_singleton] at hv; rw [hv]; exact hc)
    have hb3 := ht b (by simp)
    have hc3 := ht c (by simp)
    have hk : (1 : ℝ) / ((2 : ℕ) + 1 : ℝ) = 1 / 3 := by norm_num
    rw [hk] at hb3 hc3
    obtain ⟨hb1, hb2⟩ := F_of_dist (v := b) (t := t) hb3
    obtain ⟨hc1, hc2⟩ := F_of_dist (v := c) (t := t) hc3
    by_cases hlo : F a t < 1/4
    · obtain ⟨n, hn, -⟩ := to_Q a b c ha hb hc hng t (by linarith) (by linarith) (by linarith)
        (by linarith) hlo (Or.inr ⟨by linarith, by linarith⟩)
      exact ⟨n, hn⟩
    · by_cases hhi : F a t ≤ 3/4
      · exact absurd ⟨t, ⟨not_lt.mp hlo, hhi⟩, ⟨by linarith, by linarith⟩,
          ⟨by linarith, by linarith⟩⟩ hng
      · rw [not_le] at hhi
        have hA := F_neg a t (by linarith)
        have hB := F_neg b t (by linarith)
        have hC := F_neg c t (by linarith)
        obtain ⟨n, hn, -⟩ := to_Q a b c ha hb hc hng (-t) (by rw [hB]; linarith)
          (by rw [hB]; linarith) (by rw [hC]; linarith) (by rw [hC]; linarith)
          (by rw [hA]; linarith) (Or.inr ⟨by rw [hB]; linarith, by rw [hC]; linarith⟩)
        exact ⟨n, hn⟩
  have key : ∀ d : ℕ, ∀ n : ℤ, (b * c : ℤ) - n ≤ d → ¬ Q a b c n := by
    intro d
    induction d with
    | zero =>
      intro n hn hQ
      have := hbound n hQ
      push_cast at hn
      omega
    | succ d ih =>
      intro n hn hQ
      obtain ⟨m, hnm, hQm⟩ := hstep n hQ
      exact ih m (by push_cast at hn ⊢; omega) hQm
  exact key ((b * c : ℤ) - n0).toNat n0 (Int.self_le_toNat _) hQ0

lemma safe_quarter (v : ℕ) (hv : ¬ 4 ∣ v) : Safe v (1/4) := by
  have hr : v % 4 = 1 ∨ v % 4 = 2 ∨ v % 4 = 3 := by omega
  have hF : F v (1/4) = ((v % 4 : ℕ) : ℝ) / 4 := by
    unfold F
    rw [Int.fract_eq_iff]
    refine ⟨by positivity, ?_, ((v / 4 : ℕ) : ℤ), ?_⟩
    · rcases hr with h | h | h <;> rw [h] <;> norm_num
    · have h := Nat.div_add_mod v 4
      have h' : (v : ℝ) = 4 * ((v / 4 : ℕ) : ℝ) + ((v % 4 : ℕ) : ℝ) := by exact_mod_cast h.symm
      rw [Int.cast_natCast, h']; ring
  rw [Safe, hF]
  rcases hr with h | h | h <;> rw [h] <;> norm_num

lemma safe_scale (g v : ℕ) (hg : 0 < g) (t : ℝ) (h : Safe v t) : Safe (g * v) (t / g) := by
  have : F (g * v) (t / g) = F v t := by
    unfold F; congr 1; push_cast
    have : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
    field_simp
  rw [Safe, this]; exact h

theorem lrc_three : LRC 3 := by
  intro S hS hpos
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS
  have ha : 0 < a := hpos a (by simp)
  have hb : 0 < b := hpos b (by simp)
  have hc : 0 < c := hpos c (by simp)
  suffices hG : ∃ t, Safe a t ∧ Safe b t ∧ Safe c t by
    obtain ⟨t, h1, h2, h3⟩ := hG
    refine ⟨t, ?_⟩
    intro v hv
    have hk : (1 : ℝ) / ((3 : ℕ) + 1 : ℝ) = 1 / 4 := by norm_num
    rw [hk]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact dist_of_safe h1
    · exact dist_of_safe h2
    · exact dist_of_safe h3
  set g := Nat.gcd a (Nat.gcd b c) with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ ha
  obtain ⟨a', ha'⟩ : g ∣ a := Nat.gcd_dvd_left _ _
  obtain ⟨b', hb'⟩ : g ∣ b := dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
  obtain ⟨c', hc'⟩ : g ∣ c := dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)
  have hcop : Nat.gcd a' (Nat.gcd b' c') = 1 := by
    have h1 : g = g * Nat.gcd a' (Nat.gcd b' c') := by
      conv_lhs => rw [hg, ha', hb', hc', Nat.gcd_mul_left g b' c', Nat.gcd_mul_left]
    have : g * Nat.gcd a' (Nat.gcd b' c') = g * 1 := by rw [← h1, mul_one]
    exact Nat.eq_of_mul_eq_mul_left hgpos this
  have hpar : ∀ x y z : ℕ, ({x, y, z} : Finset ℕ) = {a', b', c'} →
      ¬ (2 ∣ x ∧ 2 ∣ y ∧ 2 ∣ z) := by
    intro x y z hxyz ⟨hx, hy, hz⟩
    have hmem : ∀ w ∈ ({a', b', c'} : Finset ℕ), 2 ∣ w := by
      rw [← hxyz]; intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> assumption
    have : 2 ∣ Nat.gcd a' (Nat.gcd b' c') :=
      Nat.dvd_gcd (hmem a' (by simp)) (Nat.dvd_gcd (hmem b' (by simp)) (hmem c' (by simp)))
    rw [hcop] at this; omega
  have ha'0 : 0 < a' := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at ha'; omega)
  have hb'0 : 0 < b' := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hb'; omega)
  have hc'0 : 0 < c' := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hc'; omega)
  have hab' : a' ≠ b' := fun h => hab (by rw [ha', hb', h])
  have hac' : a' ≠ c' := fun h => hac (by rw [ha', hc', h])
  have hbc' : b' ≠ c' := fun h => hbc (by rw [hb', hc', h])
  obtain ⟨t, h1, h2, h3⟩ : ∃ t, Safe a' t ∧ Safe b' t ∧ Safe c' t := by
    by_cases h4a : 4 ∣ a'
    · exact core a' b' c' ha'0 hb'0 hc'0 hbc' h4a (hpar a' b' c' rfl)
    by_cases h4b : 4 ∣ b'
    · obtain ⟨t, h1, h2, h3⟩ := core b' a' c' hb'0 ha'0 hc'0 hac' h4b
        (hpar b' a' c' (by ext; simp; tauto))
      exact ⟨t, h2, h1, h3⟩
    by_cases h4c : 4 ∣ c'
    · obtain ⟨t, h1, h2, h3⟩ := core c' a' b' hc'0 ha'0 hb'0 hab' h4c
        (hpar c' a' b' (by ext; simp; tauto))
      exact ⟨t, h2, h3, h1⟩
    exact ⟨1/4, safe_quarter a' h4a, safe_quarter b' h4b, safe_quarter c' h4c⟩
  refine ⟨t / g, ?_, ?_, ?_⟩
  · rw [ha']; exact safe_scale g a' hgpos t h1
  · rw [hb']; exact safe_scale g b' hgpos t h2
  · rw [hc']; exact safe_scale g c' hgpos t h3

end LonelyRunnerConjecture.FourRunnersAux

theorem solution : LonelyRunnerConjecture.LRC 3 :=
  LonelyRunnerConjecture.FourRunnersAux.lrc_three
