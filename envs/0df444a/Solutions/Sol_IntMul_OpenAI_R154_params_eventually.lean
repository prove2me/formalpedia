-- Prove2me | solution 1 for IntMul.OpenAI.R154.params_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T21:05:19.079988+00:00
-- url     : https://prove2.me/submissions/6d40ff56-ceaa-43e8-9c4a-5deafc19e65f

import Mathlib
import Definitions.Def_IntMul_OpenAI_R154

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open Real

namespace IntMul.OpenAI.R154.Pm

open IntMul.OpenAI.R154

noncomputable section

/-! ### `ℓ = ⌈L/d⌉` -/

lemma ell_spec (L d : ℕ) (hd : 0 < d) :
    L ≤ d * IntMul.OpenAI.RP.ell L d ∧ d * IntMul.OpenAI.RP.ell L d ≤ L + d - 1 := by
  unfold IntMul.OpenAI.RP.ell
  constructor
  · have := Nat.lt_div_mul_add (a := L + d - 1) hd
    rw [mul_comm]; omega
  · have := Nat.div_mul_le_self (L + d - 1) d
    rw [mul_comm]; exact this

lemma ell_le (L d b : ℕ) (hd : 0 < d) (hdb : d ≤ b) (hL2 : L ≤ b) :
    (IntMul.OpenAI.RP.ell L d : ℝ) ≤ (6 * b : ℝ) / (3 * d) := by
  have hs := ell_spec L d hd
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [le_div_iff₀ (by positivity)]
  have : ((d * IntMul.OpenAI.RP.ell L d : ℕ) : ℝ) ≤ 2 * b := by
    have : d * IntMul.OpenAI.RP.ell L d ≤ 2 * b := by omega
    exact_mod_cast this
  push_cast at this
  nlinarith

/-! ### The threshold `b ≥ b₁ = 2^{2^{103}}` -/

/-- `b₁ = 2^{2^{103}}`, as the ceiling of a real so the kernel never evaluates the tower. -/
def b1 : ℕ := ⌈(2 : ℝ) ^ ((2 : ℝ) ^ 103)⌉₊

lemma b1_real_ge : (2 : ℝ) ^ ((2 : ℝ) ^ 103) ≤ (b1 : ℝ) := Nat.le_ceil _

lemma b1_ge (k : ℕ) (hk : k ≤ 2 ^ 103) : 2 ^ k ≤ b1 := by
  have hk' : (k : ℝ) ≤ (2 : ℝ) ^ 103 := by exact_mod_cast hk
  have : (2 : ℝ) ^ k ≤ (b1 : ℝ) := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) hk').trans b1_real_ge
  exact_mod_cast this

lemma b_ge {n : ℕ} (hn : 2 ^ b1 ≤ n) : b1 ≤ Glue.bP n := by
  have h := Nat.clog_mono_right 2 hn
  rw [Nat.clog_pow 2 b1 (by norm_num)] at h
  exact h.trans (le_max_left _ _)

lemma bP_eq {n : ℕ} (hn : 2 ^ b1 ≤ n) : Glue.bP n = Nat.clog 2 n := by
  have h := Nat.clog_mono_right 2 hn
  rw [Nat.clog_pow 2 b1 (by norm_num)] at h
  have : 1 ≤ b1 := b1_ge 0 (by norm_num)
  exact max_eq_left (by omega)

lemma n_le {n : ℕ} (hn : 2 ^ b1 ≤ n) : n ≤ 2 ^ Glue.bP n := by
  rw [bP_eq hn]; exact Nat.le_pow_clog (by norm_num) n

lemma n_gt {n : ℕ} (hn : 2 ^ b1 ≤ n) : 2 ^ (Glue.bP n - 1) < n := by
  have h2 : 2 ≤ 2 ^ b1 := by
    have : 2 ^ 1 ≤ 2 ^ b1 := Nat.pow_le_pow_right (by norm_num) (b1_ge 0 (by norm_num))
    simpa using this
  rw [bP_eq hn]
  have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < n by omega)
  simpa [Nat.pred_eq_sub_one] using this

lemma L_facts {n : ℕ} (hn : 2 ^ b1 ≤ n) :
    4 * n ≤ Glue.TP n * Glue.bP n ∧ Glue.TP n * Glue.bP n < 8 * n ∧ Glue.LP n < Glue.bP n := by
  have hb : 2 ^ 4 ≤ Glue.bP n := (b1_ge 4 (by norm_num)).trans (b_ge hn)
  have hb' : 16 ≤ Glue.bP n := by simpa using hb
  have hle := n_le hn
  have hgt := n_gt hn
  set b := Glue.bP n with hbdef
  have hpow : 2 ^ b = 2 * 2 ^ (b - 1) := by
    rw [← pow_succ']; congr 1; omega
  have spec : 4 * n ≤ 2 ^ Glue.LP n * b := Nat.find_spec (Glue.LP_exists n)
  have hLb : Glue.LP n ≤ b - 1 := by
    apply Nat.find_min' (Glue.LP_exists n)
    show 4 * n ≤ 2 ^ (b - 1) * b
    have : 4 * n ≤ 8 * 2 ^ (b - 1) := by omega
    nlinarith
  have hL1 : 1 ≤ Glue.LP n := by
    by_contra h0
    have h0' : Glue.LP n = 0 := by omega
    have : 4 * n ≤ b := by simpa [h0'] using spec
    have hb2 : b < 2 ^ (b - 1) := by
      have := Nat.lt_two_pow_self (n := b - 1); omega
    omega
  have hTb : Glue.TP n * b < 8 * n := by
    have hmin : ¬ 4 * n ≤ 2 ^ (Glue.LP n - 1) * b := Nat.find_min (Glue.LP_exists n) (m := Glue.LP n - 1)
      (by show Glue.LP n - 1 < Glue.LP n; omega)
    have : Glue.TP n = 2 * 2 ^ (Glue.LP n - 1) := by
      rw [Glue.TP, ← pow_succ']; congr 1; omega
    rw [this]; push Not at hmin; nlinarith
  exact ⟨spec, hTb, by omega⟩

/-! ### `d` and `K` -/

lemma beps_big {n : ℕ} (hn : 2 ^ b1 ≤ n) : (2 : ℝ) ^ ((2 : ℝ) ^ 52) ≤ (Glue.bP n : ℝ) ^ ε := by
  have hB : (2 : ℝ) ^ ((2 : ℝ) ^ 103) ≤ (Glue.bP n : ℝ) := by
    exact b1_real_ge.trans (by exact_mod_cast b_ge hn)
  have h0 : 0 ≤ (2 : ℝ) ^ ((2 : ℝ) ^ 103) := by positivity
  calc (2 : ℝ) ^ ((2 : ℝ) ^ 52) = ((2 : ℝ) ^ ((2 : ℝ) ^ 103)) ^ ε := by
        rw [← Real.rpow_mul (by norm_num), show (2 : ℝ) ^ 103 * ε = (2 : ℝ) ^ 52 by
          unfold ε; norm_num]
    _ ≤ (Glue.bP n : ℝ) ^ ε := Real.rpow_le_rpow h0 hB (by unfold ε; norm_num)

lemma two_le_beps {n : ℕ} (hn : 2 ^ b1 ≤ n) : 2 ≤ (Glue.bP n : ℝ) ^ ε := by
  refine le_trans ?_ (beps_big hn)
  calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
    _ ≤ (2 : ℝ) ^ ((2 : ℝ) ^ 52) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)

lemma floor_half {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have := Nat.lt_floor_add_one x
  linarith

lemma d_half {n : ℕ} (hn : 2 ^ b1 ≤ n) : (Glue.bP n : ℝ) ^ ε / 2 ≤ (dP n : ℝ) :=
  floor_half (two_le_beps hn)

lemma d_le_beps (n : ℕ) : (dP n : ℝ) ≤ (Glue.bP n : ℝ) ^ ε :=
  Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma two_le_dc {n : ℕ} (hn : 2 ^ b1 ≤ n) : 2 ≤ (dP n : ℝ) ^ c := by
  have hY : (2 : ℝ) ^ ((2 : ℝ) ^ 52 - 1) ≤ (dP n : ℝ) := by
    rw [Real.rpow_sub_one (by norm_num)]
    exact le_trans (div_le_div_of_nonneg_right (beps_big hn) (by norm_num)) (d_half hn)
  have h0 : 0 ≤ (2 : ℝ) ^ ((2 : ℝ) ^ 52 - 1) := by positivity
  calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
    _ ≤ (2 : ℝ) ^ (((2 : ℝ) ^ 52 - 1) * c) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by unfold c; norm_num)
    _ = ((2 : ℝ) ^ ((2 : ℝ) ^ 52 - 1)) ^ c := by rw [Real.rpow_mul (by norm_num)]
    _ ≤ (dP n : ℝ) ^ c := Real.rpow_le_rpow h0 hY (by unfold c; norm_num)

lemma d_pos {n : ℕ} (hn : 2 ^ b1 ≤ n) : 1 ≤ dP n := by
  have h1 := d_half hn
  have h2 := two_le_beps hn
  have : (1 : ℝ) ≤ dP n := by linarith
  exact_mod_cast this

lemma d_le_b (n : ℕ) : dP n ≤ Glue.bP n := by
  have hb1 : (1 : ℝ) ≤ Glue.bP n := by exact_mod_cast Glue.bP_pos n
  have : (dP n : ℝ) ≤ Glue.bP n := (d_le_beps n).trans (by
    calc (Glue.bP n : ℝ) ^ ε ≤ (Glue.bP n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hb1 (by unfold ε; norm_num)
      _ = Glue.bP n := Real.rpow_one _)
  exact_mod_cast this

lemma concrete_d_bounds (b : ℝ) (hb : 1 ≤ b) (h2 : 2 ≤ b ^ ε) :
    (6 * b) ^ ε / 12 ≤ (⌊b ^ ε⌋₊ : ℝ) ∧ (⌊b ^ ε⌋₊ : ℝ) ≤ (6 * b) ^ ε := by
  have hb0 : 0 ≤ b := by linarith
  have h6 : (6 * b) ^ ε = 6 ^ ε * b ^ ε := Real.mul_rpow (by norm_num) hb0
  have h6le : (6 : ℝ) ^ ε ≤ 6 := by
    calc (6 : ℝ) ^ ε ≤ 6 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by unfold ε; norm_num)
      _ = 6 := Real.rpow_one 6
  have h1le : (1 : ℝ) ≤ 6 ^ ε := Real.one_le_rpow (by norm_num) (by unfold ε; norm_num)
  have hbe : 0 ≤ b ^ ε := Real.rpow_nonneg hb0 ε
  constructor
  · rw [h6]
    have := floor_half h2
    nlinarith
  · rw [h6]
    have := Nat.floor_le hbe
    nlinarith

lemma concrete_K_bounds (p d : ℝ) (hp : 1 ≤ p) (hd1 : p ^ ε / 12 ≤ d) (hd2 : d ≤ p ^ ε)
    (h2 : 2 ≤ d ^ c) :
    p ^ (ε * c) / 24 ≤ (⌊d ^ c⌋₊ : ℝ) ∧ (⌊d ^ c⌋₊ : ℝ) ≤ p ^ (ε * c) := by
  have hp0 : 0 < p := by linarith
  have hpe : 0 < p ^ ε := Real.rpow_pos_of_pos hp0 ε
  have hc0 : 0 ≤ c := by unfold c; norm_num
  have hd0 : 0 ≤ d := le_trans (by positivity) hd1
  constructor
  · have hfl := floor_half h2
    have hlow : (p ^ ε / 12) ^ c ≤ d ^ c := Real.rpow_le_rpow (by positivity) hd1 hc0
    have e : (p ^ ε / 12) ^ c = p ^ (ε * c) / 12 ^ c := by
      rw [Real.div_rpow hpe.le (by norm_num), ← Real.rpow_mul hp0.le]
    have h12 : (12 : ℝ) ^ c ≤ 12 := by
      calc (12 : ℝ) ^ c ≤ 12 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by unfold c; norm_num)
        _ = 12 := Real.rpow_one 12
    have h12' : 0 < (12 : ℝ) ^ c := Real.rpow_pos_of_pos (by norm_num) c
    have : p ^ (ε * c) / 12 ≤ p ^ (ε * c) / 12 ^ c := by
      apply div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hp0 _).le h12' h12
    rw [e] at hlow
    linarith
  · have := Nat.floor_le (Real.rpow_nonneg hd0 c)
    have hup : d ^ c ≤ (p ^ ε) ^ c := Real.rpow_le_rpow hd0 hd2 hc0
    rw [← Real.rpow_mul hp0.le] at hup
    linarith

lemma concrete_alpha_bound (b d : ℝ) (hb : 1 ≤ b) (hd0 : 0 ≤ d) (hd : d ≤ (6 * b) ^ ε)
    (h1 : 1 ≤ (12 * d ^ 2 * b) ^ ((1 : ℝ) / 4)) :
    (⌈(12 * d ^ 2 * b) ^ ((1 : ℝ) / 4)⌉₊ : ℝ) ≤ 4 * (6 * b) ^ (1 / 4 + ε / 2) := by
  set X := (12 * d ^ 2 * b) ^ ((1 : ℝ) / 4)
  have hceil : (⌈X⌉₊ : ℝ) ≤ 2 * X := by
    have := Nat.ceil_lt_add_one (show 0 ≤ X by linarith)
    linarith
  have hp0 : 0 < 6 * b := by linarith
  have hpe : 0 < (6 * b) ^ ε := Real.rpow_pos_of_pos hp0 ε
  have hY : 12 * d ^ 2 * b ≤ 2 * ((6 * b) ^ (2 * ε) * (6 * b)) := by
    have : d ^ 2 ≤ ((6 * b) ^ ε) ^ 2 := by gcongr
    have e : ((6 * b) ^ ε) ^ 2 = (6 * b) ^ (2 * ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num; ring_nf
    rw [e] at this
    nlinarith
  have hX : X ≤ (2 * ((6 * b) ^ (2 * ε) * (6 * b))) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (by positivity) hY (by norm_num)
  have e2 : (2 * ((6 * b) ^ (2 * ε) * (6 * b))) ^ ((1 : ℝ) / 4) =
      2 ^ ((1 : ℝ) / 4) * (6 * b) ^ (1 / 4 + ε / 2) := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    congr 1
    rw [← Real.rpow_add_one hp0.ne', ← Real.rpow_mul hp0.le]
    congr 1; ring
  have h2 : (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 := by
    calc (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have hq : 0 < (6 * b) ^ (1 / 4 + ε / 2) := Real.rpow_pos_of_pos hp0 _
  rw [e2] at hX
  nlinarith

theorem params_eventually' : ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n →
    IntMul.OpenAI.Glue.VP n ≤ 48 * n ∧ 0 ≤ IntMul.OpenAI.Glue.VP n ∧
      (6 * (IntMul.lg n : ℝ)) ^ ε / 12 ≤ (dP n : ℝ) ∧ (dP n : ℝ) ≤ (6 * (IntMul.lg n : ℝ)) ^ ε ∧
      (6 * (IntMul.lg n : ℝ)) ^ (ε * c) / 24 ≤ (KP n : ℝ) ∧
      (KP n : ℝ) ≤ (6 * (IntMul.lg n : ℝ)) ^ (ε * c) ∧
      (ℓP n : ℝ) ≤ 6 * (IntMul.lg n : ℝ) / (3 * (dP n : ℝ)) ∧
      (αP n : ℝ) ≤ 4 * (6 * (IntMul.lg n : ℝ)) ^ (1 / 4 + ε / 2) := by
  refine ⟨2 ^ b1, fun n hn => ?_⟩
  obtain ⟨hT1, hT2, hLb⟩ := L_facts hn
  have hbe := two_le_beps hn
  have hdc := two_le_dc hn
  have hd1 := d_pos hn
  have hdb := d_le_b n
  have hb1 : (1 : ℝ) ≤ Glue.bP n := by exact_mod_cast Glue.bP_pos n
  obtain ⟨hD1, hD2⟩ := concrete_d_bounds (Glue.bP n : ℝ) hb1 hbe
  have hp1 : (1 : ℝ) ≤ 6 * Glue.bP n := by linarith
  obtain ⟨hK1, hK2⟩ := concrete_K_bounds (6 * Glue.bP n) (dP n) hp1 hD1 hD2 hdc
  have hl2 := ell_le (Glue.LP n) (dP n) (Glue.bP n) (by omega) hdb hLb.le
  have hX1 : (1 : ℝ) ≤ (12 * (dP n : ℝ) ^ 2 * Glue.bP n) ^ ((1 : ℝ) / 4) := by
    apply Real.one_le_rpow _ (by norm_num)
    have : (1 : ℝ) ≤ dP n := by exact_mod_cast hd1
    nlinarith
  have hα := concrete_alpha_bound (Glue.bP n) (dP n) hb1 (Nat.cast_nonneg _) hD2 hX1
  have hV2 : Glue.VP n ≤ 48 * n := by
    unfold Glue.VP Glue.pP; push_cast
    have : ((Glue.TP n * Glue.bP n : ℕ) : ℝ) ≤ ((8 * n : ℕ) : ℝ) := by exact_mod_cast hT2.le
    push_cast at this; nlinarith
  have hV0 : 0 ≤ Glue.VP n := by unfold Glue.VP; positivity
  exact ⟨hV2, hV0, hD1, hD2, hK1, hK2, hl2, hα⟩

end

end IntMul.OpenAI.R154.Pm

section
open IntMul.OpenAI.R154

theorem solution : ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n →
    IntMul.OpenAI.Glue.VP n ≤ 48 * n ∧ 0 ≤ IntMul.OpenAI.Glue.VP n ∧
      (6 * (IntMul.lg n : ℝ)) ^ ε / 12 ≤ (dP n : ℝ) ∧ (dP n : ℝ) ≤ (6 * (IntMul.lg n : ℝ)) ^ ε ∧
      (6 * (IntMul.lg n : ℝ)) ^ (ε * c) / 24 ≤ (KP n : ℝ) ∧
      (KP n : ℝ) ≤ (6 * (IntMul.lg n : ℝ)) ^ (ε * c) ∧
      (ℓP n : ℝ) ≤ 6 * (IntMul.lg n : ℝ) / (3 * (dP n : ℝ)) ∧
      (αP n : ℝ) ≤ 4 * (6 * (IntMul.lg n : ℝ)) ^ (1 / 4 + ε / 2) :=
  IntMul.OpenAI.R154.Pm.params_eventually'

end
