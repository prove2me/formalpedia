-- Prove2me | solution 1 for LpSubspaceCoreset.SmallP.lemma_A_6
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T01:15:12.643703+00:00
-- url     : https://prove2.me/submissions/a544a531-f07d-49e6-8116-ccada86708f6

import Mathlib

lemma lpA6_pw {x p : ℝ} (hx : 0 ≤ x) (hp : 1 ≤ p) : x ^ p = x ^ (p - 1) * x := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h
    simp [Real.zero_rpow (by linarith : p ≠ 0)]
  · rw [Real.rpow_sub_one h.ne']; field_simp

lemma lpA6_L1 {r : ℝ} (hr : 1 ≤ r) {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) :
    x ^ r - y ^ r ≤ r * x ^ (r - 1) * (x - y) := by
  rcases eq_or_lt_of_le (hy.trans hxy) with h0 | hx
  · have hx0 : x = 0 := h0.symm
    have hy0 : y = 0 := le_antisymm (hx0 ▸ hxy) hy
    subst hx0; subst hy0; simp
  · have hxr : x ^ r = x ^ (r - 1) * x := lpA6_pw hx.le hr
    have hs : -1 ≤ y / x - 1 := by
      have : 0 ≤ y / x := div_nonneg hy hx.le
      linarith
    have key := one_add_mul_self_le_rpow_one_add hs hr
    have e1 : 1 + (y / x - 1) = y / x := by ring
    rw [e1, Real.div_rpow hy hx.le, le_div_iff₀ (Real.rpow_pos_of_pos hx r)] at key
    have e2 : (1 + r * (y / x - 1)) * x ^ r = x ^ r + r * (x ^ (r - 1) * (y - x)) := by
      rw [hxr]; field_simp
    nlinarith [key, e2]

lemma lpA6_lip_ord {r M : ℝ} (hr : 1 ≤ r) {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) (hxM : x ≤ M) :
    x ^ r - y ^ r ≤ r * M ^ (r - 1) * (x - y) := by
  have h1 := lpA6_L1 hr hy hxy
  have hx : 0 ≤ x := hy.trans hxy
  have h2 : x ^ (r - 1) ≤ M ^ (r - 1) := Real.rpow_le_rpow hx hxM (by linarith)
  have h3 : 0 ≤ x - y := by linarith
  calc _ ≤ _ := h1
    _ ≤ r * M ^ (r - 1) * (x - y) := by
      apply mul_le_mul_of_nonneg_right _ h3
      exact mul_le_mul_of_nonneg_left h2 (by linarith)

lemma lpA6_lip {r M : ℝ} (hr : 1 ≤ r) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxM : x ≤ M)
    (hyM : y ≤ M) : |x ^ r - y ^ r| ≤ r * M ^ (r - 1) * |x - y| := by
  rcases le_total y x with h | h
  · have h1 := lpA6_lip_ord hr hy h hxM
    have h2 : y ^ r ≤ x ^ r := Real.rpow_le_rpow hy h (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact h1
  · have h1 := lpA6_lip_ord hr hx h hyM
    have h2 : x ^ r ≤ y ^ r := Real.rpow_le_rpow hx h (by linarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

lemma lpA6_gLip {p : ℝ} (hp : 1 ≤ p) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {x y : ℝ}
    (hx : 0 ≤ x) (hxM : x ≤ 2) (hy : 0 ≤ y) (hyM : y ≤ 2) :
    |(|1 + σ * x|) ^ p - (|1 + σ * y|) ^ p| ≤ p * 3 ^ (p - 1) * |x - y| := by
  have h1 : |1 + σ * x| ≤ 3 := by
    rcases hσ with rfl | rfl <;> rw [abs_le] <;> constructor <;> linarith
  have h2 : |1 + σ * y| ≤ 3 := by
    rcases hσ with rfl | rfl <;> rw [abs_le] <;> constructor <;> linarith
  have h3 := lpA6_lip hp (abs_nonneg (1 + σ * x)) (abs_nonneg (1 + σ * y)) h1 h2
  have h4 : |(|1 + σ * x| - |1 + σ * y|)| ≤ |x - y| := by
    refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
    have : 1 + σ * x - (1 + σ * y) = σ * (x - y) := by ring
    rw [this, abs_mul]
    rcases hσ with rfl | rfl <;> simp
  refine h3.trans ?_
  exact mul_le_mul_of_nonneg_left h4 (mul_nonneg (by linarith) (Real.rpow_nonneg (by norm_num) _))

lemma lpA6_gB {p : ℝ} (hp : 1 ≤ p) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {x : ℝ}
    (hx : 0 ≤ x) (hxM : x ≤ 2) : |(|1 + σ * x|) ^ p| ≤ 3 ^ p := by
  have h1 : |1 + σ * x| ≤ 3 := by
    rcases hσ with rfl | rfl <;> rw [abs_le] <;> constructor <;> linarith
  rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Real.rpow_le_rpow (abs_nonneg _) h1 (by linarith)

lemma lpA6_persp (G : ℝ → ℝ) {Y L B : ℝ} (hY : 0 ≤ Y) (hL : 0 ≤ L)
    (hG : ∀ x y, 0 ≤ x → x ≤ Y → 0 ≤ y → y ≤ Y → |G x - G y| ≤ L * |x - y|)
    (hB : ∀ x, 0 ≤ x → x ≤ Y → |G x| ≤ B)
    {v v' h h' : ℝ} (hv : 0 < v) (hv' : 0 < v') (hh : 0 ≤ h) (hh' : 0 ≤ h')
    (hhY : h ≤ Y * v) (hhY' : h' ≤ Y * v') :
    |v * G (h / v) - v' * G (h' / v')| ≤ B * |v - v'| + L * (Y * |v - v'| + |h - h'|) := by
  have hx0 : 0 ≤ h / v := div_nonneg hh hv.le
  have hy0 : 0 ≤ h' / v' := div_nonneg hh' hv'.le
  have hxY : h / v ≤ Y := by rw [div_le_iff₀ hv]; exact hhY
  have hyY : h' / v' ≤ Y := by rw [div_le_iff₀ hv']; exact hhY'
  have hxv : v * (h / v) = h := by field_simp
  have hyv : v' * (h' / v') = h' := by field_simp
  have e : v' * (h / v - h' / v') = (v' - v) * (h / v) + (h - h') := by
    linear_combination hxv - hyv
  have h1 : v' * |h / v - h' / v'| ≤ |v - v'| * Y + |h - h'| := by
    rw [← abs_of_pos hv', ← abs_mul, abs_of_pos hv', e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hx0, abs_sub_comm v' v]
    exact add_le_add (mul_le_mul_of_nonneg_left hxY (abs_nonneg _)) le_rfl
  have e2 : v * G (h / v) - v' * G (h' / v') =
      (v - v') * G (h / v) + v' * (G (h / v) - G (h' / v')) := by ring
  rw [e2]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos hv']
  have h2 := hB _ hx0 hxY
  have h3 := hG _ _ hx0 hxY hy0 hyY
  have h4 : v' * |G (h / v) - G (h' / v')| ≤ L * (v' * |h / v - h' / v'|) := by
    calc v' * |G (h / v) - G (h' / v')| ≤ v' * (L * |h / v - h' / v'|) :=
          mul_le_mul_of_nonneg_left h3 hv'.le
      _ = L * (v' * |h / v - h' / v'|) := by ring
  have h5 : |v - v'| * |G (h / v)| ≤ |v - v'| * B := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have h6 : L * (v' * |h / v - h' / v'|) ≤ L * (|v - v'| * Y + |h - h'|) :=
    mul_le_mul_of_nonneg_left h1 hL
  nlinarith [h4, h5, h6]

lemma lpA6_M0 {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) {x e σ : ℝ} (he : 0 ≤ e) (hex : e ≤ x)
    (hσ : σ = 1 ∨ σ = -1) :
    |(|x + σ * e|) ^ p - x ^ p - e ^ p| ≤ 2 * p * (x ^ (p - 1) * e) := by
  have hx : 0 ≤ x := he.trans hex
  have hR : 0 ≤ x ^ (p - 1) * e := mul_nonneg (Real.rpow_nonneg hx _) he
  have hep : e ^ p ≤ x ^ (p - 1) * e := by
    rw [lpA6_pw he hp1]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow he hex (by linarith)) he
  have hxp : 0 ≤ x ^ p := Real.rpow_nonneg hx _
  have hp0 : 0 ≤ p := by linarith
  rcases hσ with rfl | rfl
  · have h1 : |x + 1 * e| = x + e := by rw [abs_of_nonneg (by linarith)]; ring
    rw [h1]
    have hL := lpA6_L1 hp1 hx (by linarith : x ≤ x + e)
    have h2 : (x + e) ^ (p - 1) ≤ 2 * x ^ (p - 1) := by
      have a1 : (x + e) ^ (p - 1) ≤ (2 * x) ^ (p - 1) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
      rw [Real.mul_rpow (by norm_num) hx] at a1
      have a2 : (2:ℝ) ^ (p - 1) ≤ 2 := by
        calc (2:ℝ) ^ (p - 1) ≤ 2 ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 := by simp
      calc _ ≤ _ := a1
        _ ≤ 2 * x ^ (p - 1) := mul_le_mul_of_nonneg_right a2 (Real.rpow_nonneg hx _)
    have h3 : x ^ p ≤ (x + e) ^ p := Real.rpow_le_rpow hx (by linarith) (by linarith)
    have h4 : p * (x + e) ^ (p - 1) * (x + e - x) ≤ p * (2 * x ^ (p - 1)) * e := by
      have : x + e - x = e := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hp0) he
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg hp0 hR]
    · nlinarith [mul_nonneg hp0 hR, Real.rpow_nonneg he p]
  · have h1 : |x + -1 * e| = x - e := by rw [abs_of_nonneg (by linarith)]; ring
    rw [h1]
    have hL := lpA6_L1 hp1 (by linarith : 0 ≤ x - e) (by linarith : x - e ≤ x)
    have h3 : (x - e) ^ p ≤ x ^ p := Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    have h5 : x - (x - e) = e := by ring
    rw [h5] at hL
    rw [abs_le]
    have hep0 := Real.rpow_nonneg he p
    constructor
    · nlinarith [mul_nonneg hp0 hR]
    · nlinarith [mul_nonneg hp0 hR]

lemma lpA6_swap {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    d ^ (p - 1) * c ≤ c ^ (p - 1) * d := by
  have h1 : 1 ≤ d / c := by rw [le_div_iff₀ hc]; linarith
  have h2 : (d / c) ^ (p - 1) ≤ d / c := by
    calc (d / c) ^ (p - 1) ≤ (d / c) ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
      _ = d / c := by simp
  have h3 : d ^ (p - 1) = (d / c) ^ (p - 1) * c ^ (p - 1) := by
    rw [← Real.mul_rpow (by positivity) hc.le]; congr 1; field_simp
  have h4 : 0 ≤ c ^ (p - 1) := Real.rpow_nonneg hc.le _
  rw [h3]
  have : (d / c) ^ (p - 1) * c ^ (p - 1) * c ≤ d / c * c ^ (p - 1) * c :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 h4) hc.le
  refine this.trans (le_of_eq ?_)
  field_simp

lemma lpA6_M {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) {c d σ : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hσ : σ = 1 ∨ σ = -1) :
    |(|c + σ * d|) ^ p - c ^ p - d ^ p| ≤ 2 * p * (c ^ (p - 1) * d) := by
  rcases le_total d c with h | h
  · exact lpA6_M0 hp1 hp2 hd h hσ
  · rcases eq_or_lt_of_le hc with h0 | hpos
    · subst h0
      have : |(0:ℝ) + σ * d| = d := by
        rcases hσ with rfl | rfl <;> simp [abs_of_nonneg hd]
      rw [this]
      have : (0:ℝ) ^ p = 0 := Real.zero_rpow (by linarith)
      rw [this]; simp
      have : 0 ≤ (0:ℝ) ^ (p - 1) * d := mul_nonneg (Real.rpow_nonneg le_rfl _) hd
      nlinarith
    · have hcd : c = d ∨ c < d := eq_or_lt_of_le h
      have key : |(|c + σ * d|) ^ p - c ^ p - d ^ p| ≤ 2 * p * (d ^ (p - 1) * c) := by
        have e : |c + σ * d| = |d + σ * c| := by
          rcases hσ with rfl | rfl
          · rw [one_mul, one_mul, add_comm]
          · rw [show c + -1 * d = -(d + -1 * c) by ring, abs_neg]
        rw [e]
        have := lpA6_M0 hp1 hp2 hc h hσ
        rw [show (|d + σ * c|) ^ p - c ^ p - d ^ p = (|d + σ * c|) ^ p - d ^ p - c ^ p by ring]
        exact this
      rcases hcd with hcd | hcd
      · subst hcd; exact key
      · refine key.trans ?_
        exact mul_le_mul_of_nonneg_left (lpA6_swap hp1 hp2 hpos hcd) (by linarith)

lemma lpA6_deg {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) {a b a' b' σ σ' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hσ : σ = 1 ∨ σ = -1) (hσ' : σ' = 1 ∨ σ' = -1)
    (hd : a = 0 ∨ b = 0) :
    |(|a + σ * b|) ^ p - (|a' + σ' * b'|) ^ p| ≤ 2 *
      (|a ^ p - a' ^ p| + |b ^ p - b' ^ p| +
        |p * σ * a ^ (p - 1) * b - p * σ' * a' ^ (p - 1) * b'|) := by
  have hp0 : (0:ℝ) < p := by linarith
  have hz : (0:ℝ) ^ (p - 1) = 0 := Real.zero_rpow (by linarith)
  have hz' : (0:ℝ) ^ p = 0 := Real.zero_rpow (by linarith)
  have hU : (|a + σ * b|) ^ p = a ^ p + b ^ p ∧ p * σ * a ^ (p - 1) * b = 0 := by
    rcases hd with rfl | rfl
    · refine ⟨?_, by simp [hz]⟩
      have : |(0:ℝ) + σ * b| = b := by rcases hσ with rfl | rfl <;> simp [abs_of_nonneg hb]
      rw [this, hz']; ring
    · refine ⟨?_, by simp⟩
      have : |a + σ * (0:ℝ)| = a := by simp [abs_of_nonneg ha]
      rw [this, hz']; ring
  obtain ⟨hU, hH⟩ := hU
  have hM := lpA6_M hp1.le hp2 ha' hb' hσ'
  have hHa : |p * σ * a ^ (p - 1) * b - p * σ' * a' ^ (p - 1) * b'| = p * (a' ^ (p - 1) * b') := by
    rw [hH, zero_sub, abs_neg, show p * σ' * a' ^ (p - 1) * b' = σ' * (p * (a' ^ (p - 1) * b')) by ring,
      abs_mul, abs_of_nonneg (mul_nonneg hp0.le (mul_nonneg (Real.rpow_nonneg ha' _) hb'))]
    rcases hσ' with rfl | rfl <;> simp
  rw [hU, hHa]
  have hR := mul_nonneg (Real.rpow_nonneg ha' (p - 1)) hb'
  rw [abs_le] at hM ⊢
  have s1 := le_abs_self (a ^ p - a' ^ p)
  have s2 := neg_abs_le (a ^ p - a' ^ p)
  have s3 := le_abs_self (b ^ p - b' ^ p)
  have s4 := neg_abs_le (b ^ p - b' ^ p)
  have s5 := abs_nonneg (a ^ p - a' ^ p)
  have s6 := abs_nonneg (b ^ p - b' ^ p)
  have : 0 ≤ p * (a' ^ (p - 1) * b') := mul_nonneg hp0.le hR
  constructor <;> nlinarith [hM.1, hM.2]

lemma lpA6_triv {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) {a b a' b' σ σ' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hσ : σ = 1 ∨ σ = -1) (hσ' : σ' = 1 ∨ σ' = -1)
    (h1 : 2 * b < a) (h2 : 2 * a' < b') :
    |(|a + σ * b|) ^ p - (|a' + σ' * b'|) ^ p| ≤ 8 * (|a ^ p - a' ^ p| + |b ^ p - b' ^ p|) := by
  have two : (2:ℝ) ≤ 2 ^ p := by
    calc (2:ℝ) = 2 ^ (1:ℝ) := by simp
      _ ≤ 2 ^ p := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp1
  have two' : (2:ℝ) ^ p ≤ 4 := by
    calc (2:ℝ) ^ p ≤ 2 ^ (2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp2
      _ = 4 := by norm_num
  have half : ∀ x y : ℝ, 0 ≤ x → 2 * x < y → x ^ p ≤ y ^ p / 2 := by
    intro x y hx hxy
    have : x ^ p ≤ (y / 2) ^ p := Real.rpow_le_rpow hx (by linarith) (by linarith)
    rw [Real.div_rpow (by linarith) (by norm_num)] at this
    have hy : 0 ≤ y ^ p := Real.rpow_nonneg (by linarith) _
    calc x ^ p ≤ y ^ p / 2 ^ p := this
      _ ≤ y ^ p / 2 := div_le_div_of_nonneg_left hy (by norm_num) two
  have four : ∀ x y s : ℝ, 0 ≤ x → 0 ≤ y → 2 * y < x → (s = 1 ∨ s = -1) →
      (|x + s * y|) ^ p ≤ 4 * x ^ p := by
    intro x y s hx hy hxy hs
    have : |x + s * y| ≤ 2 * x := by
      rcases hs with rfl | rfl <;> rw [abs_le] <;> constructor <;> linarith
    calc (|x + s * y|) ^ p ≤ (2 * x) ^ p := Real.rpow_le_rpow (abs_nonneg _) this (by linarith)
      _ = 2 ^ p * x ^ p := Real.mul_rpow (by norm_num) hx
      _ ≤ 4 * x ^ p := mul_le_mul_of_nonneg_right two' (Real.rpow_nonneg hx _)
  have hU := four a b σ ha hb h1 hσ
  have hU' := four b' a' σ' hb' ha' h2 hσ'
  have e' : |a' + σ' * b'| = |b' + σ' * a'| := by
    rcases hσ' with rfl | rfl
    · rw [one_mul, one_mul, add_comm]
    · rw [show a' + -1 * b' = -(b' + -1 * a') by ring, abs_neg]
  have hV := half b a hb h1
  have hT' := half a' b' ha' h2
  have p1 := Real.rpow_nonneg (abs_nonneg (a + σ * b)) p
  have p2 := Real.rpow_nonneg (abs_nonneg (a' + σ' * b')) p
  rw [e'] at p2 ⊢
  have s1 := le_abs_self (a ^ p - a' ^ p)
  have s3' := le_abs_self (b ^ p - b' ^ p)
  have s4 := neg_abs_le (b ^ p - b' ^ p)
  have s5 := abs_nonneg (a ^ p - a' ^ p)
  rw [abs_le]
  constructor <;> nlinarith

lemma lpA6_regA {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b a' b' σ : ℝ, 0 < a → 0 ≤ b → b ≤ 2 * a → 0 < a' → 0 ≤ b' →
      b' ≤ 2 * a' → (σ = 1 ∨ σ = -1) →
      |(|a + σ * b|) ^ p - (|a' + σ * b'|) ^ p| ≤ C *
        (|a ^ p - a' ^ p| + |b ^ p - b' ^ p| +
          |p * σ * a ^ (p - 1) * b - p * σ * a' ^ (p - 1) * b'|) := by
  have hp0 : (0:ℝ) < p := by linarith
  set L := p * 3 ^ (p - 1) with hLdef
  have hL : 0 ≤ L := mul_nonneg hp0.le (Real.rpow_nonneg (by norm_num) _)
  have hB0 : (0:ℝ) ≤ 3 ^ p := Real.rpow_nonneg (by norm_num) _
  refine ⟨3 ^ p + 3 * L, by positivity, ?_⟩
  intro a b a' b' σ ha hb hba ha' hb' hba' hσ
  have rep : ∀ a b : ℝ, 0 < a → (|a + σ * b|) ^ p =
      a ^ p * (|1 + σ * (a ^ (p - 1) * b / a ^ p)|) ^ p := by
    intro a b ha
    have e1 : a ^ (p - 1) * b / a ^ p = b / a := by
      rw [lpA6_pw ha.le hp1.le]; field_simp
    rw [e1, ← Real.mul_rpow ha.le (abs_nonneg _)]
    congr 1
    have : a + σ * b = a * (1 + σ * (b / a)) := by field_simp
    rw [this, abs_mul, abs_of_pos ha]
  have hper := lpA6_persp (fun z => (|1 + σ * z|) ^ p) (Y := 2) (L := L) (B := 3 ^ p)
    (by norm_num) hL (fun x y hx hxY hy hyY => lpA6_gLip hp1.le hσ hx hxY hy hyY)
    (fun x hx hxY => lpA6_gB hp1.le hσ hx hxY)
    (v := a ^ p) (v' := a' ^ p) (h := a ^ (p - 1) * b) (h' := a' ^ (p - 1) * b')
    (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos ha' _)
    (mul_nonneg (Real.rpow_nonneg ha.le _) hb) (mul_nonneg (Real.rpow_nonneg ha'.le _) hb')
    (by rw [lpA6_pw ha.le hp1.le]; nlinarith [Real.rpow_nonneg ha.le (p - 1)])
    (by rw [lpA6_pw ha'.le hp1.le]; nlinarith [Real.rpow_nonneg ha'.le (p - 1)])
  try simp only at hper
  rw [← rep a b ha, ← rep a' b' ha'] at hper
  have hHH : p * |a ^ (p - 1) * b - a' ^ (p - 1) * b'| =
      |p * σ * a ^ (p - 1) * b - p * σ * a' ^ (p - 1) * b'| := by
    have : p * σ * a ^ (p - 1) * b - p * σ * a' ^ (p - 1) * b' =
        (p * σ) * (a ^ (p - 1) * b - a' ^ (p - 1) * b') := by ring
    rw [this, abs_mul, abs_mul, abs_of_pos hp0]
    rcases hσ with rfl | rfl <;> simp
  have hh : |a ^ (p - 1) * b - a' ^ (p - 1) * b'| ≤
      |p * σ * a ^ (p - 1) * b - p * σ * a' ^ (p - 1) * b'| := by
    rw [← hHH]; nlinarith [abs_nonneg (a ^ (p - 1) * b - a' ^ (p - 1) * b')]
  have hvv : |a ^ p - a' ^ p| ≥ 0 := abs_nonneg _
  have h0 := abs_nonneg (b ^ p - b' ^ p)
  have h1 := mul_le_mul_of_nonneg_left hh hL
  have h2 := abs_nonneg (p * σ * a ^ (p - 1) * b - p * σ * a' ^ (p - 1) * b')
  refine hper.trans ?_
  nlinarith [mul_nonneg hB0 h0, mul_nonneg hL h0, mul_nonneg hL hvv, mul_nonneg hB0 h2,
    mul_nonneg hL h2]

lemma lpA6_regB {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b a' b' σ : ℝ, 0 ≤ a → 0 < b → a ≤ 2 * b → 0 ≤ a' → 0 < b' →
      a' ≤ 2 * b' → (σ = 1 ∨ σ = -1) →
      |(|a + σ * b|) ^ p - (|a' + σ * b'|) ^ p| ≤ C *
        (|a ^ p - a' ^ p| + |b ^ p - b' ^ p| +
          |p * σ * a ^ (p - 1) * b - p * σ * a' ^ (p - 1) * b'|) := by
  have hp0 : (0:ℝ) < p := by linarith
  have hq : 1 ≤ (p - 1)⁻¹ := (one_le_inv₀ (by linarith)).2 (by linarith)
  set q := (p - 1)⁻¹ with hqdef
  set Y : ℝ := 2 ^ (p - 1) with hYdef
  have hY0 : 0 ≤ Y := Real.rpow_nonneg (by norm_num) _
  have hYq : Y ^ q = 2 := by
    rw [hYdef, hqdef]; exact Real.rpow_rpow_inv (by norm_num) (by linarith)
  have hxq : ∀ x : ℝ, 0 ≤ x → x ≤ Y → 0 ≤ x ^ q ∧ x ^ q ≤ 2 := by
    intro x hx hxY
    refine ⟨Real.rpow_nonneg hx _, ?_⟩
    rw [← hYq]; exact Real.rpow_le_rpow hx hxY (by linarith)
  set L := p * 3 ^ (p - 1) * (q * Y ^ (q - 1)) with hLdef
  have hL : 0 ≤ L := by positivity
  have hB0 : (0:ℝ) ≤ 3 ^ p := Real.rpow_nonneg (by norm_num) _
  refine ⟨3 ^ p + L * Y + L + L, by positivity, ?_⟩
  intro a b a' b' σ ha hb hab ha' hb' hab' hσ
  have rep : ∀ a b : ℝ, 0 ≤ a → 0 < b → (|a + σ * b|) ^ p =
      b ^ p * (|1 + σ * ((a ^ (p - 1) * b / b ^ p) ^ q)|) ^ p := by
    intro a b ha hb
    have e1 : a ^ (p - 1) * b / b ^ p = (a / b) ^ (p - 1) := by
      rw [lpA6_pw hb.le hp1.le, Real.div_rpow ha hb.le]; field_simp
    have e2 : ((a / b) ^ (p - 1)) ^ q = a / b := by
      rw [hqdef]; exact Real.rpow_rpow_inv (div_nonneg ha hb.le) (by linarith)
    rw [e1, e2, ← Real.mul_rpow hb.le (abs_nonneg _)]
    congr 1
    have : b + σ * a = b * (1 + σ * (a / b)) := by field_simp
    have e3 : |a + σ * b| = |b + σ * a| := by
      rcases hσ with rfl | rfl
      · rw [one_mul, one_mul, add_comm]
      · rw [show a + -1 * b = -(b + -1 * a) by ring, abs_neg]
    rw [e3, this, abs_mul, abs_of_pos hb]
  have hhY : ∀ a b : ℝ, 0 ≤ a → 0 < b → a ≤ 2 * b → a ^ (p - 1) * b ≤ Y * b ^ p := by
    intro a b ha hb hab
    rw [lpA6_pw hb.le hp1.le, hYdef]
    have : a ^ (p - 1) ≤ (2 * b) ^ (p - 1) := Real.rpow_le_rpow ha hab (by linarith)
    rw [Real.mul_rpow (by norm_num) hb.le] at this
    nlinarith [Real.rpow_nonneg hb.le (p - 1)]
  have hper := lpA6_persp (fun z => (|1 + σ * (z ^ q)|) ^ p) (Y := Y) (L := L) (B := 3 ^ p)
    hY0 hL (by
      intro x y hx hxY hy hyY
      obtain ⟨h1, h2⟩ := hxq x hx hxY
      obtain ⟨h3, h4⟩ := hxq y hy hyY
      have g := lpA6_gLip hp1.le hσ h1 h2 h3 h4
      have l := lpA6_lip hq hx hy hxY hyY
      calc _ ≤ _ := g
        _ ≤ p * 3 ^ (p - 1) * (q * Y ^ (q - 1) * |x - y|) :=
          mul_le_mul_of_nonneg_left l (mul_nonneg hp0.le (Real.rpow_nonneg (by norm_num) _))
        _ = L * |x - y| := by rw [hLdef]; ring)
    (fun x hx hxY => by
      obtain ⟨h1, h2⟩ := hxq x hx hxY
      exact lpA6_gB hp1.le hσ h1 h2)
    (v := b ^ p) (v' := b' ^ p) (h := a ^ (p - 1) * b) (h' := a' ^ (p - 1) * b')
    (Real.rpow_pos_of_pos hb _) (Real.rpow_pos_of_pos hb' _)
    (mul_nonneg (Real.rpow_nonneg ha _) hb.le) (mul_nonneg (Real.rpow_nonneg ha' _) hb'.le)
    (hhY a b ha hb hab) (hhY a' b' ha' hb' hab')
  try simp only at hper
  rw [← rep a b ha hb, ← rep a' b' ha' hb'] at hper
  have hHH : p * |a ^ (p - 1) * b - a' ^ (p - 1) * b'| =
      |p * σ * a ^ (p - 1) * b - p * σ * a' ^ (p - 1) * b'| := by
    have : p * σ * a ^ (p - 1) * b - p * σ * a' ^ (p - 1) * b' =
        (p * σ) * (a ^ (p - 1) * b - a' ^ (p - 1) * b') := by ring
    rw [this, abs_mul, abs_mul, abs_of_pos hp0]
    rcases hσ with rfl | rfl <;> simp
  have hh : |a ^ (p - 1) * b - a' ^ (p - 1) * b'| ≤
      |p * σ * a ^ (p - 1) * b - p * σ * a' ^ (p - 1) * b'| := by
    rw [← hHH]; nlinarith [abs_nonneg (a ^ (p - 1) * b - a' ^ (p - 1) * b')]
  have hvv := abs_nonneg (a ^ p - a' ^ p)
  have h0 := abs_nonneg (b ^ p - b' ^ p)
  have h1 := mul_le_mul_of_nonneg_left hh hL
  have h2 := abs_nonneg (p * σ * a ^ (p - 1) * b - p * σ * a' ^ (p - 1) * b')
  refine hper.trans ?_
  nlinarith [mul_nonneg hB0 h0, mul_nonneg hL h0, mul_nonneg hL hvv, mul_nonneg hB0 h2,
    mul_nonneg hL h2, mul_nonneg (mul_nonneg hL hY0) h0, mul_nonneg (mul_nonneg hL hY0) hvv,
    mul_nonneg (mul_nonneg hL hY0) h2]

lemma lpA6_same {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b a' b' σ : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ a' → 0 ≤ b' → (σ = 1 ∨ σ = -1) →
      |(|a + σ * b|) ^ p - (|a' + σ * b'|) ^ p| ≤ C *
        (|a ^ p - a' ^ p| + |b ^ p - b' ^ p| +
          |p * σ * a ^ (p - 1) * b - p * σ * a' ^ (p - 1) * b'|) := by
  obtain ⟨CA, hCA0, hCA⟩ := lpA6_regA hp1 hp2
  obtain ⟨CB, hCB0, hCB⟩ := lpA6_regB hp1 hp2
  refine ⟨CA + CB + 8 + 2, by positivity, ?_⟩
  intro a b a' b' σ ha hb ha' hb' hσ
  set D := |a ^ p - a' ^ p| + |b ^ p - b' ^ p| +
          |p * σ * a ^ (p - 1) * b - p * σ * a' ^ (p - 1) * b'| with hD
  have hD0 : 0 ≤ D := by positivity
  have hD1 : |a ^ p - a' ^ p| + |b ^ p - b' ^ p| ≤ D := by
    rw [hD]; linarith [abs_nonneg (p * σ * a ^ (p - 1) * b - p * σ * a' ^ (p - 1) * b')]
  have fin : ∀ C' : ℝ, 0 ≤ C' → C' ≤ CA + CB + 8 + 2 → ∀ X : ℝ, X ≤ C' * D →
      X ≤ (CA + CB + 8 + 2) * D := by
    intro C' h0 h1 X hX
    exact hX.trans (mul_le_mul_of_nonneg_right h1 hD0)
  by_cases hd : a = 0 ∨ b = 0
  · exact fin 2 (by norm_num) (by linarith) _ (lpA6_deg hp1 hp2 ha hb ha' hb' hσ hσ hd)
  by_cases hd' : a' = 0 ∨ b' = 0
  · have := lpA6_deg hp1 hp2 ha' hb' ha hb hσ hσ hd'
    rw [abs_sub_comm, abs_sub_comm (a' ^ p), abs_sub_comm (b' ^ p),
      abs_sub_comm (p * σ * a' ^ (p - 1) * b')] at this
    exact fin 2 (by norm_num) (by linarith) _ this
  push Not at hd hd'
  have ha0 : 0 < a := lt_of_le_of_ne ha (Ne.symm hd.1)
  have hb0 : 0 < b := lt_of_le_of_ne hb (Ne.symm hd.2)
  have ha0' : 0 < a' := lt_of_le_of_ne ha' (Ne.symm hd'.1)
  have hb0' : 0 < b' := lt_of_le_of_ne hb' (Ne.symm hd'.2)
  have triv1 : 2 * b < a → 2 * a' < b' →
      |(|a + σ * b|) ^ p - (|a' + σ * b'|) ^ p| ≤ (CA + CB + 8 + 2) * D := by
    intro h1 h2
    have := lpA6_triv hp1.le hp2 ha hb ha' hb' hσ hσ h1 h2
    exact fin 8 (by norm_num) (by linarith) _ (this.trans (mul_le_mul_of_nonneg_left hD1 (by norm_num)))
  have triv2 : 2 * b' < a' → 2 * a < b →
      |(|a + σ * b|) ^ p - (|a' + σ * b'|) ^ p| ≤ (CA + CB + 8 + 2) * D := by
    intro h1 h2
    have := lpA6_triv hp1.le hp2 ha' hb' ha hb hσ hσ h1 h2
    rw [abs_sub_comm, abs_sub_comm (a' ^ p), abs_sub_comm (b' ^ p)] at this
    exact fin 8 (by norm_num) (by linarith) _ (this.trans (mul_le_mul_of_nonneg_left hD1 (by norm_num)))
  have regB' : a ≤ 2 * b → a' ≤ 2 * b' →
      |(|a + σ * b|) ^ p - (|a' + σ * b'|) ^ p| ≤ (CA + CB + 8 + 2) * D := fun hB hB' =>
    fin CB hCB0 (by linarith) _ (hCB a b a' b' σ ha hb0 hB ha' hb0' hB' hσ)
  rcases le_or_gt b (2 * a) with hA | hA
  · rcases le_or_gt b' (2 * a') with hA' | hA'
    · exact fin CA hCA0 (by linarith) _ (hCA a b a' b' σ ha0 hb hA ha0' hb' hA' hσ)
    · rcases le_or_gt a (2 * b) with hB | hB
      · exact regB' hB (by linarith)
      · exact triv1 hB hA'
  · rcases le_or_gt b' (2 * a') with hA' | hA'
    · rcases le_or_gt a' (2 * b') with hB' | hB'
      · exact regB' (by linarith) hB'
      · exact triv2 hB' hA
    · exact regB' (by linarith) (by linarith)

lemma lpA6_opp {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b a' b' σ σ' : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ a' → 0 ≤ b' →
      (σ = 1 ∨ σ = -1) → σ' = -σ →
      |(|a + σ * b|) ^ p - (|a' + σ' * b'|) ^ p| ≤ C *
        (|a ^ p - a' ^ p| + |b ^ p - b' ^ p| +
          |p * σ * a ^ (p - 1) * b - p * σ' * a' ^ (p - 1) * b'|) := by
  obtain ⟨C0, hC0, hC⟩ := lpA6_same hp1 hp2
  refine ⟨C0 + 4, by positivity, ?_⟩
  intro a b a' b' σ σ' ha hb ha' hb' hσ hσ'
  subst hσ'
  have hp0 : (0:ℝ) < p := by linarith
  have h1 := hC a b a' b' σ ha hb ha' hb' hσ
  have hA := mul_nonneg (Real.rpow_nonneg ha (p - 1)) hb
  have hA' := mul_nonneg (Real.rpow_nonneg ha' (p - 1)) hb'
  set A := a ^ (p - 1) * b with hAd
  set A' := a' ^ (p - 1) * b' with hA'd
  have habs : |p * σ| = p := by
    rw [abs_mul, abs_of_pos hp0]; rcases hσ with rfl | rfl <;> simp
  have e1 : |p * σ * a ^ (p - 1) * b - p * σ * a' ^ (p - 1) * b'| = p * |A - A'| := by
    rw [show p * σ * a ^ (p - 1) * b - p * σ * a' ^ (p - 1) * b' = (p * σ) * (A - A') by
      rw [hAd, hA'd]; ring, abs_mul, habs]
  have e2 : |p * σ * a ^ (p - 1) * b - p * -σ * a' ^ (p - 1) * b'| = p * (A + A') := by
    rw [show p * σ * a ^ (p - 1) * b - p * -σ * a' ^ (p - 1) * b' = (p * σ) * (A + A') by
      rw [hAd, hA'd]; ring, abs_mul, habs, abs_of_nonneg (by linarith)]
  have e3 : |A - A'| ≤ A + A' := by rw [abs_le]; constructor <;> linarith
  have hM1 := lpA6_M hp1.le hp2 ha' hb' hσ
  have hM2 := lpA6_M hp1.le hp2 ha' hb' (show -σ = 1 ∨ -σ = -1 by
    rcases hσ with rfl | rfl <;> simp)
  have e4 : -σ * b' = -σ * b' := rfl
  rw [← hA'd] at hM1 hM2
  have hdiff : |(|a' + σ * b'|) ^ p - (|a' + -σ * b'|) ^ p| ≤ 4 * p * A' := by
    rw [abs_le] at hM1 hM2 ⊢; constructor <;> linarith [hM1.1, hM1.2, hM2.1, hM2.2]
  have hpA' : p * A' ≤ p * (A + A') := mul_le_mul_of_nonneg_left (by linarith) hp0.le
  have hfin : |(|a + σ * b|) ^ p - (|a' + -σ * b'|) ^ p| ≤
      |(|a + σ * b|) ^ p - (|a' + σ * b'|) ^ p| + |(|a' + σ * b'|) ^ p - (|a' + -σ * b'|) ^ p| :=
    abs_sub_le _ _ _
  rw [e1] at h1
  rw [e2]
  have hpe : p * |A - A'| ≤ p * (A + A') := mul_le_mul_of_nonneg_left e3 hp0.le
  have hs0 := abs_nonneg (a ^ p - a' ^ p)
  have hs1 := abs_nonneg (b ^ p - b' ^ p)
  have hD : |a ^ p - a' ^ p| + |b ^ p - b' ^ p| + p * |A - A'| ≤
      |a ^ p - a' ^ p| + |b ^ p - b' ^ p| + p * (A + A') := by linarith
  have h2 := mul_le_mul_of_nonneg_left hD hC0
  nlinarith [hfin, hdiff, hpA', h1, h2]

lemma lpA6_one {a b σ a' b' σ' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hσ : σ = 1 ∨ σ = -1)
    (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hσ' : σ' = 1 ∨ σ' = -1) :
    |(|a + σ * b|) ^ (1:ℝ) - (|a' + σ' * b'|) ^ (1:ℝ)| ≤
      3 * (|a ^ (1:ℝ) - a' ^ (1:ℝ)| + |b ^ (1:ℝ) - b' ^ (1:ℝ)| +
        |(if a = 0 then 0 else 1 * σ * a ^ ((1:ℝ) - 1) * b) -
          (if a' = 0 then 0 else 1 * σ' * a' ^ ((1:ℝ) - 1) * b')|) := by
  simp only [Real.rpow_one, sub_self, Real.rpow_zero, mul_one, one_mul]
  have hs : |σ * b| = b := by
    rw [abs_mul]; rcases hσ with rfl | rfl <;> simp [abs_of_nonneg hb]
  have hs' : |σ' * b'| = b' := by
    rw [abs_mul]; rcases hσ' with rfl | rfl <;> simp [abs_of_nonneg hb']
  have t1 := abs_nonneg (a - a')
  have t2 := abs_nonneg (b - b')
  by_cases h1 : a = 0
  · by_cases h2 : a' = 0
    · subst h1; subst h2
      rw [if_pos rfl, if_pos rfl, zero_add, zero_add, hs, hs', sub_self, abs_zero]
      linarith
    · subst h1
      rw [if_pos rfl, if_neg h2, zero_add, hs, zero_sub, zero_sub, abs_neg, abs_neg, hs']
      have h3 : |(b' - |a' + σ' * b'|)| ≤ a' := by
        have k := abs_abs_sub_abs_le_abs_sub (σ' * b') (a' + σ' * b')
        rw [hs', show σ' * b' - (a' + σ' * b') = -a' by ring, abs_neg, abs_of_nonneg ha'] at k
        exact k
      have h4 : |(b - |a' + σ' * b'|)| ≤ |b - b'| + |(b' - |a' + σ' * b'|)| := abs_sub_le _ _ _
      rw [zero_sub, abs_neg, abs_of_nonneg ha'] at t1
      rw [abs_of_nonneg ha']
      nlinarith
  · by_cases h2 : a' = 0
    · subst h2
      rw [if_neg h1, if_pos rfl]
      simp only [zero_add, sub_zero, hs, hs']
      have h3 : |(b - |a + σ * b|)| ≤ a := by
        have k := abs_abs_sub_abs_le_abs_sub (σ * b) (a + σ * b)
        rw [hs, show σ * b - (a + σ * b) = -a by ring, abs_neg, abs_of_nonneg ha] at k
        exact k
      have h4 : |((|a + σ * b|) - b')| ≤ |(|a + σ * b|) - b| + |b - b'| := abs_sub_le _ _ _
      have h5 : |(|a + σ * b|) - b| = |(b - |a + σ * b|)| := abs_sub_comm _ _
      rw [sub_zero] at t1
      rw [abs_of_nonneg ha]
      nlinarith
    · rw [if_neg h1, if_neg h2]
      have k := abs_abs_sub_abs_le_abs_sub (a + σ * b) (a' + σ' * b')
      have k2 : |a + σ * b - (a' + σ' * b')| ≤ |a - a'| + |σ * b - σ' * b'| := by
        rw [show a + σ * b - (a' + σ' * b') = (a - a') + (σ * b - σ' * b') by ring]
        exact abs_add_le _ _
      nlinarith [abs_nonneg (σ * b - σ' * b')]

theorem solution :
    ∀ p : ℝ, 1 ≤ p → p ≤ 2 → ∃ C : ℝ,
    ∀ a b σ a' b' σ' : ℝ, 0 ≤ a → 0 ≤ b → (σ = 1 ∨ σ = -1) →
      0 ≤ a' → 0 ≤ b' → (σ' = 1 ∨ σ' = -1) →
      |(|a + σ * b|) ^ p - (|a' + σ' * b'|) ^ p| ≤
        C * (|a ^ p - a' ^ p| + |b ^ p - b' ^ p| +
          |(if a = 0 then 0 else p * σ * a ^ (p - 1) * b) -
            (if a' = 0 then 0 else p * σ' * a' ^ (p - 1) * b')|) := by
  intro p hp1 hp2
  rcases eq_or_lt_of_le hp1 with h | h
  · subst h
    refine ⟨3, ?_⟩
    intro a b σ a' b' σ' ha hb hσ ha' hb' hσ'
    exact lpA6_one ha hb hσ ha' hb' hσ'
  · obtain ⟨C0, hC0, hC⟩ := lpA6_same h hp2
    obtain ⟨C1, hC1, hC'⟩ := lpA6_opp h hp2
    refine ⟨C0 + C1, ?_⟩
    intro a b σ a' b' σ' ha hb hσ ha' hb' hσ'
    have e : ∀ (s x y : ℝ), (if x = 0 then (0:ℝ) else p * s * x ^ (p - 1) * y) =
        p * s * x ^ (p - 1) * y := by
      intro s x y
      split_ifs with hx
      · subst hx; simp [Real.zero_rpow (by linarith : p - 1 ≠ 0)]
      · rfl
    rw [e, e]
    have hD0 : 0 ≤ |a ^ p - a' ^ p| + |b ^ p - b' ^ p| +
        |p * σ * a ^ (p - 1) * b - p * σ' * a' ^ (p - 1) * b'| := by positivity
    have hs : σ' = σ ∨ σ' = -σ := by
      rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl <;> simp
    rcases hs with rfl | hs
    · exact (hC a b a' b' σ' ha hb ha' hb' hσ).trans
        (mul_le_mul_of_nonneg_right (by linarith) hD0)
    · exact (hC' a b a' b' σ σ' ha hb ha' hb' hσ hs).trans
        (mul_le_mul_of_nonneg_right (by linarith) hD0)
