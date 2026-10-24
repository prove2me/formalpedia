-- Prove2me | solution 1 for ModernConvex.LPDuality.bernshtein_theorem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T21:52:36.395699+00:00
-- url     : https://prove2.me/submissions/c40a78be-b953-46ab-a11d-5bc51c217425

import Mathlib

namespace BN97

open Complex Finset

lemma H_step (n : ℕ) (z : ℕ → ℂ) (p : ℕ) (hz1 : ∀ j ∈ range n, z j ≠ 1) (m : ℕ) :
    ∑ j ∈ range n, z j ^ (m + 1) / (z j - 1) ^ (p + 1) =
      ∑ j ∈ range n, z j ^ m / (z j - 1) ^ (p + 1) + ∑ j ∈ range n, z j ^ m / (z j - 1) ^ p := by
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j hj => ?_
  have h : z j - 1 ≠ 0 := sub_ne_zero.mpr (hz1 j hj)
  field_simp
  ring

lemma H_anti (n : ℕ) (z : ℕ → ℂ) (p : ℕ) (hzn : ∀ j ∈ range n, z j ^ n = -1) (m : ℕ) :
    ∑ j ∈ range n, z j ^ (m + n) / (z j - 1) ^ p = - ∑ j ∈ range n, z j ^ m / (z j - 1) ^ p := by
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun j hj => ?_
  rw [pow_add, hzn j hj]; ring

lemma key (n : ℕ) (hn : 0 < n) (z : ℕ → ℂ) (hz1 : ∀ j ∈ range n, z j ≠ 1)
    (hzn : ∀ j ∈ range n, z j ^ n = -1)
    (hR : ∀ i, 0 < i → i < n → ∑ j ∈ range n, z j ^ i = 0) (m : ℕ) (hm : m ≤ n) :
    ∑ j ∈ range n, z j ^ (m + 1) / (z j - 1) ^ 2 = - (n : ℂ) ^ 2 / 4 + m * n / 2 := by
  set H : ℕ → ℂ := fun m => ∑ j ∈ range n, z j ^ m / (z j - 1) ^ 1 with hH
  set G : ℕ → ℂ := fun m => ∑ j ∈ range n, z j ^ m / (z j - 1) ^ 2 with hG
  have hR' : ∀ i, ∑ j ∈ range n, z j ^ i / (z j - 1) ^ 0 = ∑ j ∈ range n, z j ^ i := by
    intro i; simp
  have hR0 : ∑ j ∈ range n, z j ^ 0 = n := by simp
  have hH1 : ∀ m, 1 ≤ m → m ≤ n → H m = H 0 + n := by
    intro m h1 h2
    induction m, h1 using Nat.le_induction with
    | base =>
      have := H_step n z 0 hz1 0
      simp only [hH]; rw [this, hR', hR0]
    | succ m hm1 ih =>
      have := H_step n z 0 hz1 m
      simp only [hH] at ih ⊢; rw [this, hR', hR m (by omega) (by omega), ih (by omega)]; ring
  have hH0 : H 0 = - (n : ℂ) / 2 := by
    have h1 := hH1 n hn le_rfl
    have h2 := H_anti n z 1 hzn 0
    simp only [hH, zero_add] at h1 h2 ⊢
    rw [h2] at h1
    linear_combination -h1 / 2
  have hHm : ∀ m, 1 ≤ m → m ≤ n → H m = n / 2 := by
    intro m h1 h2; rw [hH1 m h1 h2, hH0]; ring
  have hG1 : ∀ m, m ≤ n → G (m + 1) = G 1 + m * n / 2 := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      have := H_step n z 1 hz1 (m + 1)
      have h3 := hHm (m + 1) (by omega) (by omega)
      simp only [hG, hH] at ih h3 ⊢
      rw [this, ih (by omega), h3]; push_cast; ring
  have hGn : G 1 = - (n : ℂ) ^ 2 / 4 := by
    have h1 := hG1 n le_rfl
    have h2 := H_anti n z 2 hzn 1
    simp only [hG] at h1 h2 ⊢
    rw [add_comm n 1, h2] at h1
    linear_combination -h1 / 2
  have := hG1 m hm
  simp only [hG] at this hGn
  rw [this, hGn]

end BN97

namespace BN97

open Complex Finset

noncomputable def tau (k j : ℕ) : ℝ := (2 * j + 1) * Real.pi / (2 * k)
noncomputable def zeta (k j : ℕ) : ℂ := Complex.exp ((tau k j : ℂ) * I)

lemma zeta_pow (k j m : ℕ) : zeta k j ^ m = Complex.exp (((m * tau k j : ℝ) : ℂ) * I) := by
  rw [zeta, ← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma zeta_pow_n {k : ℕ} (hk : k ≠ 0) (j : ℕ) : zeta k j ^ (2 * k) = -1 := by
  rw [zeta, ← Complex.exp_nat_mul]
  have : ((2 * k : ℕ) : ℂ) * ((tau k j : ℂ) * I) = (j : ℂ) * (2 * Real.pi * I) + Real.pi * I := by
    unfold tau; push_cast; field_simp
  rw [this, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, Complex.exp_pi_mul_I]; ring

lemma zeta_pow_k {k : ℕ} (hk : k ≠ 0) (j : ℕ) : zeta k j ^ k = I * (-1) ^ j := by
  rw [zeta, ← Complex.exp_nat_mul]
  have : ((k : ℕ) : ℂ) * ((tau k j : ℂ) * I) = Real.pi / 2 * I + j * (Real.pi * I) := by
    unfold tau; push_cast; field_simp; ring
  rw [this, Complex.exp_add, Complex.exp_pi_div_two_mul_I, Complex.exp_nat_mul,
    Complex.exp_pi_mul_I]

lemma sin_pos {k j : ℕ} (hk : k ≠ 0) (hj : j < 2 * k) : 0 < Real.sin (tau k j / 2) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · unfold tau; have : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    positivity
  · unfold tau
    have hk' : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hj' : (j : ℝ) + 1 ≤ 2 * k := by exact_mod_cast hj
    rw [div_div, div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]

lemma zeta_sq (k j : ℕ) :
    (zeta k j - 1) ^ 2 = -4 * zeta k j * ((Real.sin (tau k j / 2) : ℝ) : ℂ) ^ 2 := by
  have hz : zeta k j = Complex.exp (((tau k j / 2 : ℝ) : ℂ) * I) ^ 2 := by
    rw [zeta, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [hz, Complex.ofReal_sin, Complex.sin]
  set s : ℂ := ((tau k j / 2 : ℝ) : ℂ)
  have h1 : Complex.exp (-s * I) = (Complex.exp (s * I))⁻¹ := by
    rw [← Complex.exp_neg]; ring_nf
  rw [h1]
  have h0 : Complex.exp (s * I) ≠ 0 := Complex.exp_ne_zero _
  field_simp
  ring_nf
  rw [Complex.I_sq]; ring

lemma zeta_ne_one {k j : ℕ} (hk : k ≠ 0) (hj : j < 2 * k) : zeta k j ≠ 1 := by
  intro h
  have := zeta_sq k j
  rw [h] at this
  have hs := sin_pos hk hj
  have : ((Real.sin (tau k j / 2) : ℝ) : ℂ) ^ 2 = 0 := by
    have : (-4 : ℂ) * ((Real.sin (tau k j / 2) : ℝ) : ℂ) ^ 2 = 0 := by linear_combination -this
    simpa using this
  have : Real.sin (tau k j / 2) = 0 := by exact_mod_cast pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  linarith

lemma root_sum {k : ℕ} (hk : k ≠ 0) (i : ℕ) (hi0 : 0 < i) (hi : i < 2 * k) :
    ∑ j ∈ range (2 * k), zeta k j ^ i = 0 := by
  set ω := Complex.exp (2 * Real.pi * I / ((2 * k : ℕ) : ℂ))
  have hω : IsPrimitiveRoot ω (2 * k) := Complex.isPrimitiveRoot_exp _ (by omega)
  have hzj : ∀ j, zeta k j = zeta k 0 * ω ^ j := by
    intro j
    rw [zeta, zeta, ← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1
    unfold tau; push_cast; field_simp; ring
  have : ∀ j, zeta k j ^ i = zeta k 0 ^ i * (ω ^ i) ^ j := by
    intro j; rw [hzj, mul_pow, ← pow_mul, ← pow_mul, mul_comm i j]
  rw [sum_congr rfl (fun j _ => this j), ← mul_sum]
  rw [geom_sum_eq (hω.pow_ne_one_of_pos_of_lt (by omega) hi), ← pow_mul, mul_comm i (2 * k), pow_mul,
    hω.pow_eq_one]
  simp

/-- `Σ ζ^(m+1)/(ζ-1)^2 = -k^2 + m k` for `m ≤ 2k`. -/
lemma key_zeta {k : ℕ} (hk : k ≠ 0) (m : ℕ) (hm : m ≤ 2 * k) :
    ∑ j ∈ range (2 * k), zeta k j ^ (m + 1) / (zeta k j - 1) ^ 2 = - (k : ℂ) ^ 2 + m * k := by
  rw [key (2 * k) (by omega) (zeta k) (fun j hj => zeta_ne_one hk (mem_range.mp hj))
    (fun j _ => zeta_pow_n hk j) (fun i h1 h2 => root_sum hk i h1 h2) m hm]
  push_cast; ring

end BN97

namespace BN97

open Complex Finset

noncomputable def w (k j : ℕ) : ℝ := (-1) ^ j / Real.sin (tau k j / 2) ^ 2

lemma w_zeta {k : ℕ} (hk : k ≠ 0) {j : ℕ} (hj : j < 2 * k) (l : ℕ) :
    (w k j : ℂ) * zeta k j ^ l = 4 * I * (zeta k j ^ ((k + l) + 1) / (zeta k j - 1) ^ 2) := by
  have hs := zeta_sq k j
  have hkk := zeta_pow_k hk j
  have hz0 : zeta k j ≠ 0 := Complex.exp_ne_zero _
  have hsn : ((Real.sin (tau k j / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (sin_pos hk hj).ne'
  rw [hs, pow_add, pow_add, hkk, w]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]; ring

lemma sum_w_zeta {k : ℕ} (hk : k ≠ 0) (l : ℕ) (hl : l ≤ k) :
    ∑ j ∈ range (2 * k), (w k j : ℂ) * zeta k j ^ l = 4 * k * l * I := by
  rw [sum_congr rfl (fun j hj => w_zeta hk (mem_range.mp hj) l), ← mul_sum,
    key_zeta hk (k + l) (by omega)]
  push_cast; ring

lemma sum_w_cos {k : ℕ} (hk : k ≠ 0) (l : ℕ) (hl : l ≤ k) :
    ∑ j ∈ range (2 * k), w k j * Real.cos (l * tau k j) = 0 ∧
    ∑ j ∈ range (2 * k), w k j * Real.sin (l * tau k j) = 4 * k * l := by
  have h := sum_w_zeta hk l hl
  have : ∀ j, (w k j : ℂ) * zeta k j ^ l =
      ((w k j * Real.cos (l * tau k j) : ℝ) : ℂ) + ((w k j * Real.sin (l * tau k j) : ℝ) : ℂ) * I := by
    intro j
    rw [zeta_pow, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast; ring
  rw [sum_congr rfl (fun j _ => this j), sum_add_distrib, ← sum_mul, ← Complex.ofReal_sum,
    ← Complex.ofReal_sum] at h
  generalize ∑ j ∈ range (2 * k), w k j * Real.cos (l * tau k j) = A at h ⊢
  generalize ∑ j ∈ range (2 * k), w k j * Real.sin (l * tau k j) = B at h ⊢
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp at h1 h2
  exact ⟨h1, by rw [h2]⟩

lemma sum_abs_w {k : ℕ} (hk : k ≠ 0) :
    ∑ j ∈ range (2 * k), |w k j| = 4 * k ^ 2 := by
  have : ∀ j ∈ range (2 * k), |w k j| = 1 / Real.sin (tau k j / 2) ^ 2 := by
    intro j _; rw [w, abs_div]; simp
  rw [sum_congr rfl this]
  have h2 : ∀ j ∈ range (2 * k), ((1 / Real.sin (tau k j / 2) ^ 2 : ℝ) : ℂ) =
      -4 * (zeta k j ^ (0 + 1) / (zeta k j - 1) ^ 2) := by
    intro j hj
    have hs := zeta_sq k j
    have hz0 : zeta k j ≠ 0 := Complex.exp_ne_zero _
    have hsn : ((Real.sin (tau k j / 2) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (sin_pos hk (mem_range.mp hj)).ne'
    rw [hs]; push_cast; field_simp
  have h3 := sum_congr rfl h2
  rw [← mul_sum, key_zeta hk 0 (by omega), ← Complex.ofReal_sum] at h3
  have : ((∑ j ∈ range (2 * k), 1 / Real.sin (tau k j / 2) ^ 2 : ℝ) : ℂ) = ((4 * k ^ 2 : ℝ) : ℂ) := by
    rw [h3]; push_cast; ring
  exact_mod_cast this

lemma sum_w_trig {k : ℕ} (hk : k ≠ 0) (l : ℕ) (hl : l ≤ k) (t : ℝ) :
    ∑ j ∈ range (2 * k), w k j * Real.cos (l * (t + tau k j)) = 4 * k * (-(l * Real.sin (l * t))) ∧
    ∑ j ∈ range (2 * k), w k j * Real.sin (l * (t + tau k j)) = 4 * k * (l * Real.cos (l * t)) := by
  obtain ⟨h1, h2⟩ := sum_w_cos hk l hl
  constructor
  · have : ∀ j, w k j * Real.cos (l * (t + tau k j)) =
        Real.cos (l * t) * (w k j * Real.cos (l * tau k j)) -
          Real.sin (l * t) * (w k j * Real.sin (l * tau k j)) := by
      intro j; rw [mul_add, Real.cos_add]; ring
    rw [sum_congr rfl (fun j _ => this j), sum_sub_distrib, ← mul_sum, ← mul_sum, h1, h2]; ring
  · have : ∀ j, w k j * Real.sin (l * (t + tau k j)) =
        Real.sin (l * t) * (w k j * Real.cos (l * tau k j)) +
          Real.cos (l * t) * (w k j * Real.sin (l * tau k j)) := by
      intro j; rw [mul_add, Real.sin_add]; ring
    rw [sum_congr rfl (fun j _ => this j), sum_add_distrib, ← mul_sum, ← mul_sum, h1, h2]; ring

end BN97

namespace BN97

open Complex Finset

lemma periodic (k : ℕ) (a b : ℕ → ℂ) (f : ℝ → ℂ)
    (hf : ∀ t : ℝ, f t = a 0 + ∑ l ∈ Finset.Icc 1 k,
      (a l * (Real.cos (l * t) : ℂ) + b l * (Real.sin (l * t) : ℂ))) (u : ℝ) (m : ℤ) :
    f (u + m * (2 * Real.pi)) = f u := by
  rw [hf, hf]
  congr 1
  refine sum_congr rfl fun l _ => ?_
  have e : (l : ℝ) * (u + m * (2 * Real.pi)) = l * u + ((l * m : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast; ring
  rw [e, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

lemma bound_all (k : ℕ) (a b : ℕ → ℂ) (f : ℝ → ℂ)
    (hf : ∀ t : ℝ, f t = a 0 + ∑ l ∈ Finset.Icc 1 k,
      (a l * (Real.cos (l * t) : ℂ) + b l * (Real.sin (l * t) : ℂ)))
    (M : ℝ) (hM : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖f t‖ ≤ M) (u : ℝ) : ‖f u‖ ≤ M := by
  have h1 := toIcoMod_mem_Ico Real.two_pi_pos 0 u
  have h2 := self_sub_toIcoMod Real.two_pi_pos 0 u
  rw [zsmul_eq_mul] at h2
  have : u = toIcoMod Real.two_pi_pos 0 u + (toIcoDiv Real.two_pi_pos 0 u : ℝ) * (2 * Real.pi) := by
    linarith
  rw [this, periodic k a b f hf]
  apply hM
  rw [zero_add] at h1
  exact ⟨h1.1, h1.2.le⟩

lemma hasDeriv (k : ℕ) (a b : ℕ → ℂ) (f : ℝ → ℂ)
    (hf : ∀ t : ℝ, f t = a 0 + ∑ l ∈ Finset.Icc 1 k,
      (a l * (Real.cos (l * t) : ℂ) + b l * (Real.sin (l * t) : ℂ))) (t : ℝ) :
    HasDerivAt f (∑ l ∈ Finset.Icc 1 k, (a l * ((-(l * Real.sin (l * t)) : ℝ) : ℂ) +
      b l * ((l * Real.cos (l * t) : ℝ) : ℂ))) t := by
  rw [show f = fun t => a 0 + ∑ l ∈ Finset.Icc 1 k,
      (a l * (Real.cos (l * t) : ℂ) + b l * (Real.sin (l * t) : ℂ)) from funext hf]
  apply HasDerivAt.const_add
  apply HasDerivAt.fun_sum
  intro l _
  have hc : HasDerivAt (fun x : ℝ => Real.cos (l * x)) (-(l * Real.sin (l * t))) t := by
    have := ((hasDerivAt_id' t).const_mul (l : ℝ)).cos
    convert this using 1; ring
  have hs : HasDerivAt (fun x : ℝ => Real.sin (l * x)) (l * Real.cos (l * t)) t := by
    have := ((hasDerivAt_id' t).const_mul (l : ℝ)).sin
    convert this using 1; ring
  exact (hc.ofReal_comp.const_mul (a l)).add (hs.ofReal_comp.const_mul (b l))

lemma formula {k : ℕ} (hk : k ≠ 0) (a b : ℕ → ℂ) (f : ℝ → ℂ)
    (hf : ∀ t : ℝ, f t = a 0 + ∑ l ∈ Finset.Icc 1 k,
      (a l * (Real.cos (l * t) : ℂ) + b l * (Real.sin (l * t) : ℂ))) (t : ℝ) :
    (4 * k : ℂ) * (∑ l ∈ Finset.Icc 1 k, (a l * ((-(l * Real.sin (l * t)) : ℝ) : ℂ) +
      b l * ((l * Real.cos (l * t) : ℝ) : ℂ))) =
      ∑ j ∈ range (2 * k), (w k j : ℂ) * f (t + tau k j) := by
  have hE : ∀ j, (w k j : ℂ) * f (t + tau k j) = (w k j : ℂ) * a 0 + ∑ l ∈ Finset.Icc 1 k,
      ((w k j : ℂ) * (a l * (Real.cos (l * (t + tau k j)) : ℂ)) +
        (w k j : ℂ) * (b l * (Real.sin (l * (t + tau k j)) : ℂ))) := by
    intro j
    rw [hf, mul_add, mul_sum]
    exact congrArg _ (sum_congr rfl fun l _ => mul_add _ _ _)
  rw [sum_congr rfl (fun j _ => hE j)]
  have h0 : ∑ j ∈ range (2 * k), (w k j : ℂ) * a 0 = 0 := by
    have := (sum_w_cos hk 0 (Nat.zero_le _)).1
    simp at this
    rw [← sum_mul, ← Complex.ofReal_sum, this]; simp
  conv_rhs => rw [sum_add_distrib, h0, zero_add, sum_comm]
  rw [mul_sum]
  refine sum_congr rfl fun l hl => ?_
  conv_rhs => rw [sum_add_distrib]
  have hlk : l ≤ k := (mem_Icc.mp hl).2
  obtain ⟨h1, h2⟩ := sum_w_trig hk l hlk t
  have e1 : ∑ j ∈ range (2 * k), (w k j : ℂ) * (a l * (Real.cos (l * (t + tau k j)) : ℂ)) =
      a l * ((∑ j ∈ range (2 * k), w k j * Real.cos (l * (t + tau k j)) : ℝ) : ℂ) := by
    push_cast; rw [mul_sum]; refine sum_congr rfl fun j _ => ?_; ring
  have e2 : ∑ j ∈ range (2 * k), (w k j : ℂ) * (b l * (Real.sin (l * (t + tau k j)) : ℂ)) =
      b l * ((∑ j ∈ range (2 * k), w k j * Real.sin (l * (t + tau k j)) : ℝ) : ℂ) := by
    push_cast; rw [mul_sum]; refine sum_congr rfl fun j _ => ?_; ring
  rw [e1, e2, h1, h2]
  push_cast; ring

end BN97

theorem solution (k : ℕ) (a b : ℕ → ℂ) (f : ℝ → ℂ)
    (hf : ∀ t : ℝ, f t = a 0 + ∑ l ∈ Finset.Icc 1 k,
      (a l * (Real.cos (l * t) : ℂ) + b l * (Real.sin (l * t) : ℂ)))
    (M : ℝ) (hM : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖f t‖ ≤ M) :
    ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖deriv f t‖ ≤ k * M := by
  intro t _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : f = fun _ => a 0 := funext fun t => by rw [hf]; simp
    rw [this]; simp
  have hk0 : k ≠ 0 := hk.ne'
  rw [(BN97.hasDeriv k a b f hf t).deriv]
  set D := ∑ l ∈ Finset.Icc 1 k, (a l * ((-(l * Real.sin (l * t)) : ℝ) : ℂ) +
      b l * ((l * Real.cos (l * t) : ℝ) : ℂ))
  have hF := BN97.formula hk0 a b f hf t
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : 4 * k * ‖D‖ ≤ 4 * k ^ 2 * M := by
    have : ‖(4 * k : ℂ) * D‖ = 4 * k * ‖D‖ := by
      rw [norm_mul]; congr 1
      rw [show ((4 : ℂ) * k) = ((4 * k : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    rw [← this, hF, ← BN97.sum_abs_w hk0, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (BN97.bound_all k a b f hf M hM _) (abs_nonneg _)
  have : 4 * k * ‖D‖ ≤ 4 * k * (k * M) := by nlinarith
  exact le_of_mul_le_mul_left this (by positivity)
