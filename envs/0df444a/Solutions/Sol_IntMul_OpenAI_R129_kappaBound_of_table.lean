-- Prove2me | solution 1 for IntMul.OpenAI.R129.kappaBound_of_table
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-20T13:45:15.660063+00:00
-- url     : https://prove2.me/submissions/56c11cc2-5b78-45d2-ba72-82f7bae79db5

import Mathlib
import Definitions.Def_IntMul_OpenAI_R129

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open Real

namespace IntMul.OpenAI.R129.Pf

open IntMul.OpenAI.R129

/-! ## Margins -/

theorem margins' :
    2 * κ ≤ 1 - ε * (1 + c) ∧ 2 * κ ≤ ε * c * (1 - τ) ∧ 2 * κ ≤ ε * (1 - lam') ∧
      2 * κ ≤ 1 - τ - ε * (2 - τ) ∧ 2 * κ ≤ 1 / 4 - δ - 3 * ε / 2 ∧ 2 * κ ≤ 1 - δ - ε ∧
      2 * κ ≤ ε ∧ τ * (1 + c / (1 / 2)) < lam' ∧ lam' < 1 ∧ 0 < lam' - τ - c := by
  unfold κ ε c τ lam' δ
  norm_num

/-! ## The cost table -/

lemma pw {p e : ℝ} (hp : 1 ≤ p) (he : e ≤ es) : p ^ e ≤ p ^ es :=
  Real.rpow_le_rpow_of_exponent_le hp he

lemma es_pos : 0 < es := by unfold es κ; norm_num

/-- `x ≥ a p^e`, `-1 ≤ z ≤ 0`, `0 < a ≤ 1` ⇒ `x^z ≤ a⁻¹ p^{ez}`. -/
lemma rpow_neg_bound {x a p e z : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hp : 0 < p)
    (hx : a * p ^ e ≤ x) (hz : z ≤ 0) (hz1 : -1 ≤ z) : x ^ z ≤ a⁻¹ * p ^ (e * z) := by
  have hpe : 0 < p ^ e := Real.rpow_pos_of_pos hp e
  calc x ^ z ≤ (a * p ^ e) ^ z := Real.rpow_le_rpow_of_nonpos (by positivity) hx hz
    _ = a ^ z * p ^ (e * z) := by rw [Real.mul_rpow ha.le hpe.le, ← Real.rpow_mul hp.le]
    _ ≤ a⁻¹ * p ^ (e * z) := by
        gcongr
        rw [← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_ge ha ha1 hz1

theorem Ncost_le' (p d K ℓ α : ℝ) (hp : 1 ≤ p)
    (hd1 : p ^ ε / 12 ≤ d) (hd2 : d ≤ p ^ ε)
    (hK1 : p ^ (ε * c) / 24 ≤ K) (hK2 : K ≤ p ^ (ε * c))
    (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ p / (3 * d))
    (hα0 : 0 ≤ α) (hα : α ≤ 4 * p ^ (1 / 4 + ε / 2)) :
    Ncost p d K ℓ α ≤ 50 * p ^ es := by
  have hp0 : 0 < p := by linarith
  have hpe : ∀ e : ℝ, 0 < p ^ e := fun e => Real.rpow_pos_of_pos hp0 e
  have hd0 : 0 < d := lt_of_lt_of_le (by have := hpe ε; positivity) hd1
  have hK0 : 0 < K := lt_of_lt_of_le (by have := hpe (ε * c); positivity) hK1
  have hes1 : 1 ≤ p ^ es := Real.one_le_rpow hp es_pos.le
  -- 1. d K
  have t1 : d * K ≤ p ^ es := by
    calc d * K ≤ p ^ ε * p ^ (ε * c) := mul_le_mul hd2 hK2 hK0.le (hpe _).le
      _ = p ^ (ε + ε * c) := (Real.rpow_add hp0 _ _).symm
      _ ≤ p ^ es := (by apply pw hp; unfold ε c es κ; norm_num)
  -- 2. p K^{τ-1}
  have t2 : p * K ^ (τ - 1) ≤ 24 * p ^ es := by
    have h := rpow_neg_bound (x := K) (a := 1 / 24) (p := p) (e := ε * c) (z := τ - 1)
      (by norm_num) (by norm_num) hp0 (by linarith) (by unfold τ; norm_num)
      (by unfold τ; norm_num)
    calc p * K ^ (τ - 1) ≤ p * ((1 / 24)⁻¹ * p ^ (ε * c * (τ - 1))) :=
          mul_le_mul_of_nonneg_left h hp0.le
      _ = 24 * (p ^ (1 : ℝ) * p ^ (ε * c * (τ - 1))) := by rw [Real.rpow_one]; ring
      _ = 24 * p ^ (1 + ε * c * (τ - 1)) := by rw [← Real.rpow_add hp0]
      _ ≤ 24 * p ^ es := by
          gcongr; unfold ε c τ es κ; norm_num
  -- 3. ℓ d^{λ'}
  have t3 : ℓ * d ^ lam' ≤ 4 * p ^ es := by
    have hdl : d ^ lam' = d * d ^ (lam' - 1) := by
      rw [Real.rpow_sub hd0, Real.rpow_one]; field_simp
    have h := rpow_neg_bound (x := d) (a := 1 / 12) (p := p) (e := ε) (z := lam' - 1)
      (by norm_num) (by norm_num) hp0 (by linarith) (by unfold lam'; norm_num)
      (by unfold lam'; norm_num)
    have hd' : 0 ≤ d ^ (lam' - 1) := (Real.rpow_pos_of_pos hd0 _).le
    calc ℓ * d ^ lam' ≤ p / (3 * d) * (d * d ^ (lam' - 1)) := by
          rw [hdl]; exact mul_le_mul_of_nonneg_right hℓ (by positivity)
      _ = p / 3 * d ^ (lam' - 1) := by field_simp
      _ ≤ p / 3 * ((1 / 12)⁻¹ * p ^ (ε * (lam' - 1))) := by gcongr
      _ = 4 * (p ^ (1 : ℝ) * p ^ (ε * (lam' - 1))) := by rw [Real.rpow_one]; ring
      _ = 4 * p ^ (1 + ε * (lam' - 1)) := by rw [← Real.rpow_add hp0]
      _ ≤ 4 * p ^ es := by gcongr; unfold ε lam' es κ; norm_num
  -- 4. d²(1 + ℓ^τ)
  have t4 : d ^ 2 * (1 + ℓ ^ τ) ≤ 2 * p ^ es := by
    have hτ0 : 0 ≤ τ := by unfold τ; norm_num
    have hd2' : d ^ 2 ≤ p ^ es := by
      calc d ^ 2 ≤ (p ^ ε) ^ 2 := by gcongr
        _ = p ^ (ε * 2) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num
        _ ≤ p ^ es := (by apply pw hp; unfold ε es κ; norm_num)
    have hℓτ : ℓ ^ τ ≤ p ^ τ / d ^ τ := by
      calc ℓ ^ τ ≤ (p / d) ^ τ := by
            apply Real.rpow_le_rpow hℓ0 _ hτ0
            refine hℓ.trans (div_le_div_of_nonneg_left hp0.le hd0 (by linarith))
        _ = p ^ τ / d ^ τ := Real.div_rpow hp0.le hd0.le τ
    have hdτ : 0 < d ^ τ := Real.rpow_pos_of_pos hd0 τ
    have h2 : d ^ 2 * ℓ ^ τ ≤ p ^ es := by
      calc d ^ 2 * ℓ ^ τ ≤ d ^ 2 * (p ^ τ / d ^ τ) := by gcongr
        _ = d ^ ((2 : ℝ) - τ) * p ^ τ := by
            rw [Real.rpow_sub hd0, Real.rpow_two]; ring
        _ ≤ (p ^ ε) ^ ((2 : ℝ) - τ) * p ^ τ := by
            gcongr; unfold τ; norm_num
        _ = p ^ (ε * (2 - τ) + τ) := by
            rw [← Real.rpow_mul hp0.le, Real.rpow_add hp0]
        _ ≤ p ^ es := (by apply pw hp; unfold ε τ es κ; norm_num)
    nlinarith
  -- 5. d p^{1/2+δ} α
  have t5 : d * p ^ (1 / 2 + δ) * α ≤ 4 * p ^ es := by
    calc d * p ^ (1 / 2 + δ) * α ≤ p ^ ε * p ^ (1 / 2 + δ) * (4 * p ^ (1 / 4 + ε / 2)) := by
          gcongr
      _ = 4 * (p ^ ε * p ^ (1 / 2 + δ) * p ^ (1 / 4 + ε / 2)) := by ring
      _ = 4 * p ^ (ε + (1 / 2 + δ) + (1 / 4 + ε / 2)) := by
          rw [← Real.rpow_add hp0, ← Real.rpow_add hp0]
      _ ≤ 4 * p ^ es := by gcongr; unfold ε δ es κ; norm_num
  -- 6. d p^δ
  have t6 : d * p ^ δ ≤ p ^ es := by
    calc d * p ^ δ ≤ p ^ ε * p ^ δ := by gcongr
      _ = p ^ (ε + δ) := (Real.rpow_add hp0 _ _).symm
      _ ≤ p ^ es := (by apply pw hp; unfold ε δ es κ; norm_num)
  -- 7. ℓ + log₂ p
  have t7 : ℓ + Real.logb 2 p ≤ 7 * p ^ es := by
    have hℓ' : ℓ ≤ 4 * p ^ es := by
      calc ℓ ≤ p / (3 * d) := hℓ
        _ ≤ p / (3 * (p ^ ε / 12)) := by
            apply div_le_div_of_nonneg_left hp0.le (by have := hpe ε; positivity); linarith
        _ = 4 * (p ^ (1 : ℝ) / p ^ ε) := by rw [Real.rpow_one]; field_simp; ring
        _ = 4 * p ^ (1 - ε) := by rw [← Real.rpow_sub hp0]
        _ ≤ 4 * p ^ es := by gcongr; unfold ε es κ; norm_num
    have hlog : Real.logb 2 p ≤ 3 * p ^ es := by
      have h1 := Real.log_le_rpow_div hp0.le (show (0 : ℝ) < 1 / 2 by norm_num)
      have hl2 := Real.log_two_gt_d9
      have h2 : p ^ ((1 : ℝ) / 2) ≤ p ^ es := (by apply pw hp; unfold es κ; norm_num)
      have hlp : 0 ≤ Real.log p := Real.log_nonneg hp
      rw [Real.logb, div_le_iff₀ (by linarith)]
      have : p ^ ((1 : ℝ) / 2) / (1 / 2) = 2 * p ^ ((1 : ℝ) / 2) := by field_simp
      rw [this] at h1
      nlinarith
    linarith
  -- 8. p^δ + 1
  have t8 : p ^ δ ≤ p ^ es := (by apply pw hp; unfold δ es κ; norm_num)
  unfold Ncost
  linarith

/-! ## The reduction -/

theorem multipliesAt_mono' {M : IntMul.MultitapeTM} {n : ℕ} {T T' : ℝ}
    (h : IntMul.MultipliesAt M n T) (hT : T ≤ T') : IntMul.MultipliesAt M n T' := by
  intro x y hx hy
  obtain ⟨t, ht, hh⟩ := h x y hx hy
  exact ⟨t, ht.trans hT, hh⟩

/-- A fixed power of `log L + 1` is at most a constant times `L^κ`. -/
lemma polylog_le (A : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → (Real.log L + 1) ^ A ≤ C * L ^ κ := by
  have hκ : 0 < κ := by unfold κ; norm_num
  set e : ℝ := κ / (A + 1) with he
  have he0 : 0 < e := by positivity
  refine ⟨(1 / e + 1) ^ A, by positivity, fun L hL => ?_⟩
  have hL0 : 0 ≤ L := by linarith
  have hLe : 1 ≤ L ^ e := Real.one_le_rpow hL he0.le
  have hlog : Real.log L ≤ L ^ e / e := Real.log_le_rpow_div hL0 he0
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL
  have h1 : Real.log L + 1 ≤ (1 / e + 1) * L ^ e := by
    have : L ^ e / e = 1 / e * L ^ e := by ring
    nlinarith
  have h2 : (Real.log L + 1) ^ A ≤ ((1 / e + 1) * L ^ e) ^ A :=
    pow_le_pow_left₀ (by linarith) h1 A
  have h3 : ((1 / e + 1) * L ^ e) ^ A = (1 / e + 1) ^ A * L ^ (e * A) := by
    rw [mul_pow, ← Real.rpow_natCast (L ^ e), ← Real.rpow_mul hL0]
  have h4 : L ^ (e * A) ≤ L ^ κ := by
    apply Real.rpow_le_rpow_of_exponent_le hL
    rw [he, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  calc (Real.log L + 1) ^ A ≤ (1 / e + 1) ^ A * L ^ (e * A) := h3 ▸ h2
    _ ≤ (1 / e + 1) ^ A * L ^ κ := by gcongr

theorem kappaBound_of_table' (M : IntMul.MultitapeTM)
    (hcorr : ∀ n : ℕ, 1 ≤ n → ∃ T : ℝ, IntMul.MultipliesAt M n T)
    (n₀ A : ℕ) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (V d K ℓ α : ℕ → ℝ)
    (hV : ∀ n, n₀ ≤ n → V n ≤ 48 * n) (hV0 : ∀ n, n₀ ≤ n → 0 ≤ V n)
    (hd1 : ∀ n, n₀ ≤ n → (6 * (IntMul.lg n : ℝ)) ^ ε / 12 ≤ d n)
    (hd2 : ∀ n, n₀ ≤ n → d n ≤ (6 * (IntMul.lg n : ℝ)) ^ ε)
    (hK1 : ∀ n, n₀ ≤ n → (6 * (IntMul.lg n : ℝ)) ^ (ε * c) / 24 ≤ K n)
    (hK2 : ∀ n, n₀ ≤ n → K n ≤ (6 * (IntMul.lg n : ℝ)) ^ (ε * c))
    (hℓ0 : ∀ n, n₀ ≤ n → 0 ≤ ℓ n) (hℓ : ∀ n, n₀ ≤ n → ℓ n ≤ 6 * (IntMul.lg n : ℝ) / (3 * d n))
    (hα0 : ∀ n, n₀ ≤ n → 0 ≤ α n)
    (hα : ∀ n, n₀ ≤ n → α n ≤ 4 * (6 * (IntMul.lg n : ℝ)) ^ (1 / 4 + ε / 2))
    (htime : ∀ n, n₀ ≤ n → IntMul.MultipliesAt M n
      (C₀ * (V n * Ncost (6 * (IntMul.lg n : ℝ)) (d n) (K n) (ℓ n) (α n) *
        (Real.log (IntMul.lg n) + 1) ^ A + n))) :
    IntMul.KappaBound (1 / 2 ^ 129) := by
  obtain ⟨C, hC, hpoly⟩ := polylog_le A
  refine ⟨M, hcorr, C₀ * (48 * 50 * 6 * C + 1) + 1, by positivity, n₀, fun n hn _ => ?_⟩
  apply multipliesAt_mono' (htime n hn)
  have hL : (1 : ℝ) ≤ (IntMul.lg n : ℝ) := by
    have : 1 ≤ IntMul.lg n := le_max_right _ _
    exact_mod_cast this
  set L : ℝ := (IntMul.lg n : ℝ)
  have hp : (1 : ℝ) ≤ 6 * L := by linarith
  have hN := Ncost_le' (6 * L) (d n) (K n) (ℓ n) (α n) hp (hd1 n hn) (hd2 n hn) (hK1 n hn)
    (hK2 n hn) (hℓ0 n hn) (hℓ n hn) (hα0 n hn) (hα n hn)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL0 : (0 : ℝ) ≤ L := by linarith
  -- (6L)^{es} ≤ 6 L^{1-2κ}
  have hes : (6 * L) ^ es ≤ 6 * L ^ es := by
    rw [Real.mul_rpow (by norm_num) hL0]
    have h6 : (6 : ℝ) ^ es ≤ 6 := by
      calc (6 : ℝ) ^ es ≤ 6 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by unfold es κ; norm_num)
        _ = 6 := Real.rpow_one 6
    have : 0 ≤ L ^ es := Real.rpow_nonneg hL0 _
    nlinarith
  -- L^{es} L^κ = L^{1-κ}
  have hsplit : L ^ es * L ^ κ = L ^ (1 - 1 / 2 ^ 129 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]; congr 1; unfold es κ; ring
  have hP0 : 0 ≤ (Real.log L + 1) ^ A := pow_nonneg (by linarith [Real.log_nonneg hL]) A
  have hP := hpoly L hL
  have hLk : 1 ≤ L ^ (1 - 1 / 2 ^ 129 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hesn : 0 ≤ L ^ es := Real.rpow_nonneg hL0 _
  have hκn : 0 ≤ L ^ κ := Real.rpow_nonneg hL0 _
  have hVNP : V n * Ncost (6 * L) (d n) (K n) (ℓ n) (α n) * (Real.log L + 1) ^ A ≤
      48 * 50 * 6 * C * (n * L ^ (1 - 1 / 2 ^ 129 : ℝ)) := by
    have hpos : 0 ≤ 50 * (6 * L) ^ es := by
      have := Real.rpow_nonneg (show (0 : ℝ) ≤ 6 * L by linarith) es; positivity
    calc V n * Ncost (6 * L) (d n) (K n) (ℓ n) (α n) * (Real.log L + 1) ^ A
        ≤ V n * (50 * (6 * L) ^ es) * (Real.log L + 1) ^ A := by
          gcongr; exact hV0 n hn
      _ ≤ 48 * n * (50 * (6 * L ^ es)) * (C * L ^ κ) := by
          gcongr
          · exact hV n hn
      _ = 48 * 50 * 6 * C * (n * (L ^ es * L ^ κ)) := by ring
      _ = 48 * 50 * 6 * C * (n * L ^ (1 - 1 / 2 ^ 129 : ℝ)) := by rw [hsplit]
  have hX : 0 ≤ (n : ℝ) * L ^ (1 - 1 / 2 ^ 129 : ℝ) := by positivity
  have hnL : (n : ℝ) ≤ n * L ^ (1 - 1 / 2 ^ 129 : ℝ) := by nlinarith
  calc C₀ * (V n * Ncost (6 * L) (d n) (K n) (ℓ n) (α n) * (Real.log L + 1) ^ A + n)
      ≤ C₀ * (48 * 50 * 6 * C * (n * L ^ (1 - 1 / 2 ^ 129 : ℝ)) +
          n * L ^ (1 - 1 / 2 ^ 129 : ℝ)) := by gcongr
    _ = C₀ * (48 * 50 * 6 * C + 1) * (n * L ^ (1 - 1 / 2 ^ 129 : ℝ)) := by ring
    _ ≤ (C₀ * (48 * 50 * 6 * C + 1) + 1) * (n * L ^ (1 - 1 / 2 ^ 129 : ℝ)) := by nlinarith

end IntMul.OpenAI.R129.Pf

section
open IntMul.OpenAI.R129

theorem solution (M : IntMul.MultitapeTM)
    (hcorr : ∀ n : ℕ, 1 ≤ n → ∃ T : ℝ, IntMul.MultipliesAt M n T)
    (n₀ A : ℕ) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (V d K ℓ α : ℕ → ℝ)
    (hV : ∀ n, n₀ ≤ n → V n ≤ 48 * n) (hV0 : ∀ n, n₀ ≤ n → 0 ≤ V n)
    (hd1 : ∀ n, n₀ ≤ n → (6 * (IntMul.lg n : ℝ)) ^ ε / 12 ≤ d n)
    (hd2 : ∀ n, n₀ ≤ n → d n ≤ (6 * (IntMul.lg n : ℝ)) ^ ε)
    (hK1 : ∀ n, n₀ ≤ n → (6 * (IntMul.lg n : ℝ)) ^ (ε * c) / 24 ≤ K n)
    (hK2 : ∀ n, n₀ ≤ n → K n ≤ (6 * (IntMul.lg n : ℝ)) ^ (ε * c))
    (hℓ0 : ∀ n, n₀ ≤ n → 0 ≤ ℓ n) (hℓ : ∀ n, n₀ ≤ n → ℓ n ≤ 6 * (IntMul.lg n : ℝ) / (3 * d n))
    (hα0 : ∀ n, n₀ ≤ n → 0 ≤ α n)
    (hα : ∀ n, n₀ ≤ n → α n ≤ 4 * (6 * (IntMul.lg n : ℝ)) ^ (1 / 4 + ε / 2))
    (htime : ∀ n, n₀ ≤ n → IntMul.MultipliesAt M n
      (C₀ * (V n * Ncost (6 * (IntMul.lg n : ℝ)) (d n) (K n) (ℓ n) (α n) *
        (Real.log (IntMul.lg n) + 1) ^ A + n))) :
    IntMul.KappaBound (1 / 2 ^ 129) :=
  IntMul.OpenAI.R129.Pf.kappaBound_of_table' M hcorr n₀ A C₀ hC₀ V d K ℓ α hV hV0 hd1 hd2 hK1 hK2
    hℓ0 hℓ hα0 hα htime

end

