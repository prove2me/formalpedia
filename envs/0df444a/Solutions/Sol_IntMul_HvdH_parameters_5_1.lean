-- Prove2me | solution 1 for IntMul.HvdH.parameters_5_1
-- status  : ACCEPTED   (prove)
-- author  : @avi
-- created : 2026-10-09T12:50:27.889149+00:00
-- url     : https://prove2.me/submissions/a435b020-1ade-4b13-8aa9-022b40c47a87

import Mathlib

set_option maxHeartbeats 2000000 in
theorem solution (d : ℕ) (hd : 2 ≤ d) (n : ℕ) (hn : 2 ^ (d ^ 12) ≤ n)
    (b p α γ T r : ℕ) (hb : b = Nat.clog 2 n) (hp : p = 6 * b)
    (hα : α = ⌈((12 * d ^ 2 * b : ℕ) : ℝ) ^ ((1 : ℝ) / 4)⌉₊) (hγ : γ = 2 * d * α ^ 2)
    (hTpow : ∃ k : ℕ, T = 2 ^ k) (hT1 : 4 * (n : ℝ) / b ≤ T) (hT2 : (T : ℝ) < 8 * (n : ℝ) / b)
    (hrpow : ∃ j : ℕ, r = 2 ^ j) (hr1 : (T : ℝ) ^ ((1 : ℝ) / d) ≤ r)
    (hr2 : (r : ℝ) < 2 * (T : ℝ) ^ ((1 : ℝ) / d)) :
    -- (5.1), (5.2)
    (d ^ 12 ≤ b ∧ 4096 ≤ b ∧ 100 ≤ p) ∧
    -- (5.4)
    (2 ≤ α ∧ (α : ℝ) < 2 * (b : ℝ) ^ ((7 : ℝ) / 24) ∧
      2 * (b : ℝ) ^ ((7 : ℝ) / 24) < Real.sqrt p) ∧
    -- (5.5)
    (γ : ℝ) < 8 * (b : ℝ) ^ ((2 : ℝ) / 3) ∧
    -- (5.8)
    2 ^ (d ^ 10) ≤ r ∧
    -- (5.9)
    (T < n ∧ n ≤ 2 ^ b ∧ T < 2 ^ p) ∧
    -- the factorisation `T = t₁ ⋯ t_d` with `t₁ = ⋯ = t_{d'} = r/2`, `t_{d'+1} = ⋯ = t_d = r`
    (∃ d' : ℕ, d' < d ∧ (r / 2) ^ d' * r ^ (d - d') = T) ∧ 4 ≤ r := by
  /- (5.1), (5.2) -/
  have hd12 : 4096 ≤ d ^ 12 := by
    have := Nat.pow_le_pow_left hd 12; norm_num at this; omega
  have hbd : d ^ 12 ≤ b := by
    rw [hb, ← Nat.clog_pow 2 (d ^ 12) (by norm_num)]
    exact Nat.clog_mono_right 2 hn
  have hb4096 : 4096 ≤ b := hd12.trans hbd
  have hn2 : 2 ≤ n :=
    le_trans (Nat.succ_le_of_lt (Nat.one_lt_two_pow (by positivity) : 1 < 2 ^ (d ^ 12))) hn
  have hnb : n ≤ 2 ^ b := by rw [hb]; exact Nat.le_pow_clog (by norm_num) n
  have hpow : 2 ^ (b - 1) < n := by
    have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hn2
    rw [← hb, Nat.pred_eq_sub_one] at this; exact this
  /- u = b^{1/24} -/
  have hbR : (4096 : ℝ) ≤ b := by exact_mod_cast hb4096
  have hb0 : (0 : ℝ) ≤ b := by linarith
  set u : ℝ := (b : ℝ) ^ (((24 : ℕ) : ℝ)⁻¹) with hu
  have hu0 : 0 ≤ u := Real.rpow_nonneg hb0 _
  have hu24 : u ^ 24 = b := Real.rpow_inv_natCast_pow hb0 (by norm_num)
  have hdu : (d : ℝ) ≤ u ^ 2 := by
    have h : ((d : ℝ)) ^ 12 ≤ (u ^ 2) ^ 12 := by
      rw [← pow_mul, hu24]; exact_mod_cast hbd
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h
  have hu14 : (1.4 : ℝ) ≤ u := by
    by_contra h
    rw [not_le] at h
    have := pow_lt_pow_left₀ h hu0 (by norm_num : (24 : ℕ) ≠ 0)
    rw [hu24] at this; norm_num at this; linarith
  have hu7 : (10 : ℝ) ≤ u ^ 7 := by
    have := pow_le_pow_left₀ (by norm_num) hu14 7; norm_num at this; linarith
  have hb724 : (b : ℝ) ^ ((7 : ℝ) / 24) = u ^ 7 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hb0]; norm_num
  have hb23 : (b : ℝ) ^ ((2 : ℝ) / 3) = u ^ 16 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hb0]; norm_num
  /- (5.4): α -/
  set X : ℝ := ((12 * d ^ 2 * b : ℕ) : ℝ) with hX
  have hX0 : 0 ≤ X := by positivity
  have hXup : X ≤ (1.87 * u ^ 7) ^ 4 := by
    have h1 : X = 12 * (d : ℝ) ^ 2 * b := by rw [hX]; push_cast; ring
    have h2 : (d : ℝ) ^ 2 ≤ (u ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hdu 2
    rw [h1, ← hu24]
    have h3 : (0 : ℝ) ≤ u ^ 24 := by positivity
    nlinarith [h2, h3, pow_nonneg hu0 28]
  have hq : ((1 : ℝ) / 4) = ((4 : ℕ) : ℝ)⁻¹ := by norm_num
  have hXq : X ^ ((1 : ℝ) / 4) ≤ 1.87 * u ^ 7 := by
    have := Real.rpow_le_rpow hX0 hXup (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [hq] at this ⊢
    rwa [Real.pow_rpow_inv_natCast (by positivity) (by norm_num)] at this
  have hXlo : (2 : ℝ) ≤ X ^ ((1 : ℝ) / 4) := by
    have h16 : (16 : ℝ) ≤ X := by
      have : 16 ≤ 12 * d ^ 2 * b := by nlinarith
      rw [hX]; exact_mod_cast this
    have := Real.rpow_le_rpow (by norm_num) h16 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, hq] at this
    rw [hq]
    rwa [Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)] at this
  have hαlt : (α : ℝ) < 2 * u ^ 7 := by
    have := Nat.ceil_lt_add_one (Real.rpow_nonneg hX0 ((1 : ℝ) / 4))
    rw [← hα] at this; linarith
  have hα2 : 2 ≤ α := by
    have := hXlo.trans (Nat.le_ceil _)
    rw [← hα] at this; exact_mod_cast this
  have hsq : 2 * u ^ 7 < Real.sqrt p := by
    rw [Real.lt_sqrt (by positivity)]
    have hpR : (p : ℝ) = 6 * u ^ 24 := by rw [hu24, hp]; push_cast; ring
    rw [hpR]
    have h1 : (1 : ℝ) ≤ u ^ 10 := one_le_pow₀ (by linarith)
    have h2 : (0 : ℝ) < u ^ 14 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 h2.le]
  /- (5.5): γ -/
  have hγlt : (γ : ℝ) < 8 * u ^ 16 := by
    have hαR : (0 : ℝ) ≤ α := by positivity
    have h1 : (α : ℝ) ^ 2 < (2 * u ^ 7) ^ 2 := pow_lt_pow_left₀ hαlt hαR (by norm_num)
    have h2 : (γ : ℝ) = 2 * d * (α : ℝ) ^ 2 := by rw [hγ]; push_cast; ring
    have hdpos : (0 : ℝ) < d := by have : (2 : ℝ) ≤ d := by exact_mod_cast hd
                                   linarith
    rw [h2]
    calc 2 * (d : ℝ) * (α : ℝ) ^ 2 ≤ 2 * u ^ 2 * (α : ℝ) ^ 2 := by gcongr
      _ < 2 * u ^ 2 * (2 * u ^ 7) ^ 2 :=
          mul_lt_mul_of_pos_left h1 (by have : (0 : ℝ) < u := by linarith
                                        positivity)
      _ = 8 * u ^ 16 := by ring
  /- (5.9) -/
  obtain ⟨k, hk⟩ := hTpow
  obtain ⟨j, hj⟩ := hrpow
  have hbpos : (0 : ℝ) < b := by linarith
  have hTb : (T : ℝ) * b < 8 * n := by rwa [lt_div_iff₀ hbpos] at hT2
  have hTn : T < n := by
    have : (T : ℝ) < n := by nlinarith
    exact_mod_cast this
  have hTp : T < 2 ^ p := by
    have : 2 ^ b ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  /- (5.8): T ≥ 2^{d^11}, so r ≥ T^{1/d} ≥ 2^{d^10} -/
  have h2d : 2 * d ^ 11 ≤ d ^ 12 := by
    have : d ^ 12 = d * d ^ 11 := by ring
    rw [this]; exact Nat.mul_le_mul_right _ hd
  have hbig : b * 2 ^ (d ^ 11) < 4 * n := by
    set m := b - d ^ 11 with hm
    have hbm : b ≤ 2 ^ (m + 1) := by
      have := Nat.lt_two_pow_self (n := m)
      rw [pow_succ]; omega
    have he : m + 1 + d ^ 11 = (b - 1) + 2 := by omega
    calc b * 2 ^ (d ^ 11) ≤ 2 ^ (m + 1) * 2 ^ (d ^ 11) := Nat.mul_le_mul_right _ hbm
      _ = 2 ^ (b - 1) * 4 := by rw [← pow_add, he, pow_add]; norm_num
      _ < n * 4 := Nat.mul_lt_mul_of_pos_right hpow (by norm_num)
      _ = 4 * n := by ring
  have hT11 : (2 : ℝ) ^ (d ^ 11) ≤ T := by
    have h1 : 4 * (n : ℝ) ≤ T * b := by rwa [div_le_iff₀ hbpos] at hT1
    have h2 : (b : ℝ) * 2 ^ (d ^ 11) < 4 * n := by exact_mod_cast hbig
    nlinarith
  have hdR : (0 : ℝ) < d := by have : (2 : ℝ) ≤ d := by exact_mod_cast hd
                               linarith
  have hr10 : (2 : ℝ) ^ (d ^ 10) ≤ r := by
    have h1 := Real.rpow_le_rpow (by positivity) hT11 (by positivity : (0 : ℝ) ≤ 1 / d)
    have h2 : ((2 : ℝ) ^ (d ^ 11)) ^ ((1 : ℝ) / d) = (2 : ℝ) ^ (d ^ 10) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
      congr 1; push_cast; field_simp
    rw [h2] at h1; exact h1.trans hr1
  have hr10' : 2 ^ (d ^ 10) ≤ r := by exact_mod_cast hr10
  have hr4 : 4 ≤ r := by
    have : 2 ≤ d ^ 10 := by
      have := Nat.pow_le_pow_left hd 10; norm_num at this; omega
    have h4 : 2 ^ 2 ≤ 2 ^ (d ^ 10) := Nat.pow_le_pow_right (by norm_num) this
    omega
  /- the factorisation: T ≤ r^d < 2^d T -/
  have hd0 : d ≠ 0 := by omega
  have hinv : (1 : ℝ) / d = ((d : ℕ) : ℝ)⁻¹ := by rw [one_div]
  have hTd : ((T : ℝ) ^ ((1 : ℝ) / d)) ^ d = T := by
    rw [hinv]; exact Real.rpow_inv_natCast_pow (by positivity) hd0
  have hle : T ≤ r ^ d := by
    have this : ((T : ℝ) ^ ((1 : ℝ) / d)) ^ d ≤ (r : ℝ) ^ d :=
      pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg T) _) hr1 d
    rw [hTd] at this
    exact_mod_cast this
  have hlt : r ^ d < 2 ^ d * T := by
    have this : (r : ℝ) ^ d < (2 * (T : ℝ) ^ ((1 : ℝ) / d)) ^ d :=
      pow_lt_pow_left₀ hr2 (Nat.cast_nonneg r) hd0
    rw [mul_pow, hTd] at this
    exact_mod_cast this
  rw [hk, hj, ← pow_mul] at hle
  rw [hk, hj, ← pow_mul, ← pow_add] at hlt
  have hk1 : k ≤ j * d := (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
  have hk2 : j * d < d + k := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
  have hj2 : 2 ≤ j := by
    by_contra h
    have : j ≤ 1 := by omega
    have : 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  refine ⟨⟨hbd, hb4096, by omega⟩, ⟨hα2, by rw [hb724]; exact hαlt, by rw [hb724]; exact hsq⟩,
    by rw [hb23]; exact hγlt, hr10', ⟨hTn, hnb, hTp⟩, ⟨j * d - k, by omega, ?_⟩, hr4⟩
  -- (2^{j-1})^{d'} · (2^j)^{d-d'} = 2^{jd - d'} = 2^k
  set e := j * d - k with he
  have hr2' : r / 2 = 2 ^ (j - 1) := by
    rw [hj, show j = (j - 1) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    simp
  rw [hr2', hj, hk, ← pow_mul, ← pow_mul, ← pow_add]
  congr 1
  have hed : e ≤ d := by omega
  have h1 : (j - 1) * e + e = j * e := by
    rw [show j = (j - 1) + 1 by omega]; simp; ring
  have h2 : j * (d - e) + j * e = j * d := by rw [← Nat.mul_add, Nat.sub_add_cancel hed]
  omega
