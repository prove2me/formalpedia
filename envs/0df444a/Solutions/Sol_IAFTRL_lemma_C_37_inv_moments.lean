-- Prove2me | solution 1 for IAFTRL.lemma_C_37_inv_moments
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T15:54:05.625208+00:00
-- url     : https://prove2.me/submissions/e31da283-a1e4-4d4c-b30f-1a2e0f9c8e8b

import Mathlib
import Definitions.Def_IAFTRL_beta
import Definitions.Def_IAFTRL_Bc
import Definitions.Def_IAFTRL_cR
import Definitions.Def_IAFTRL_C37_scalar

/-! ===== module Base ===== -/

/-! # Elementary inequalities for the scalar moment analysis (v1 Appendix I.5 and helpers) -/

namespace C37

/-! ## Second-order remainders of powers -/

/-- `(y+z)^{m+2} − y^{m+2} − (m+2) y^{m+1} z` is at most `(m+2)(m+1)/2 (|y|+|z|)^m z²` in absolute
value (v1 (I.8), by induction on the exponent). -/
lemma binom_rem (y z : ℝ) (m : ℕ) :
    |(y + z) ^ (m + 2) - y ^ (m + 2) - (m + 2) * y ^ (m + 1) * z| ≤
      ((m + 2) * (m + 1) / 2 : ℝ) * (|y| + |z|) ^ m * z ^ 2 := by
  induction m with
  | zero =>
    have e : (y + z) ^ (0 + 2) - y ^ (0 + 2) - ((0 : ℕ) + 2 : ℝ) * y ^ (0 + 1) * z = z ^ 2 := by
      push_cast; ring
    rw [e]; simp [abs_of_nonneg (sq_nonneg z)]
  | succ m ih =>
    have e : (y + z) ^ (m + 1 + 2) - y ^ (m + 1 + 2) - ((m + 1 : ℕ) + 2 : ℝ) * y ^ (m + 1 + 1) * z =
        (y + z) * ((y + z) ^ (m + 2) - y ^ (m + 2) - (m + 2) * y ^ (m + 1) * z) +
          (m + 2) * y ^ (m + 1) * z ^ 2 := by
      push_cast; ring
    rw [e]
    have hyz : |y + z| ≤ |y| + |z| := abs_add_le y z
    have hs0 : 0 ≤ |y| + |z| := by positivity
    have hy : |y| ^ (m + 1) ≤ (|y| + |z|) ^ (m + 1) :=
      pow_le_pow_left₀ (abs_nonneg y) (by linarith [abs_nonneg z]) _
    have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
    calc |(y + z) * ((y + z) ^ (m + 2) - y ^ (m + 2) - (m + 2) * y ^ (m + 1) * z) +
          (m + 2) * y ^ (m + 1) * z ^ 2|
        ≤ |y + z| * |(y + z) ^ (m + 2) - y ^ (m + 2) - (m + 2) * y ^ (m + 1) * z| +
            (m + 2) * |y| ^ (m + 1) * z ^ 2 := by
          refine (abs_add_le _ _).trans (add_le_add (le_of_eq (abs_mul _ _)) (le_of_eq ?_))
          rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hz2, abs_of_nonneg (by positivity : (0:ℝ) ≤ m + 2)]
      _ ≤ (|y| + |z|) * (((m + 2) * (m + 1) / 2 : ℝ) * (|y| + |z|) ^ m * z ^ 2) +
            (m + 2) * (|y| + |z|) ^ (m + 1) * z ^ 2 := by
          gcongr
      _ = (((m + 1 : ℕ) + 2) * ((m + 1 : ℕ) + 1) / 2 : ℝ) * (|y| + |z|) ^ (m + 1) * z ^ 2 := by
          push_cast; ring

/-- the upper Taylor bound for an arbitrary power `P ≥ 2` -/
lemma pow_taylor (y z : ℝ) (P : ℕ) (hP : 2 ≤ P) :
    (y + z) ^ P ≤ y ^ P + P * y ^ (P - 1) * z +
      ((P : ℝ) * (P - 1) / 2) * (|y| + |z|) ^ (P - 2) * z ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, P = m + 2 := ⟨P - 2, by omega⟩
  have h := le_abs_self ((y + z) ^ (m + 2) - y ^ (m + 2) - (m + 2) * y ^ (m + 1) * z)
  have h2 := binom_rem y z m
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 - 2 = m := by omega
  rw [e1, e2]
  push_cast
  have e3 : ((m : ℝ) + 2) * ((m : ℝ) + 2 - 1) / 2 = ((m + 2) * (m + 1) / 2 : ℝ) := by ring
  rw [e3]
  linarith

/-- (I.7): the positive-part Taylor bound for an even power -/
lemma pos_taylor (y z : ℝ) (P : ℕ) (hP : 2 ≤ P) (hev : Even P) :
    (max (y + z) 0) ^ P ≤ (max y 0) ^ P + P * (max y 0) ^ (P - 1) * z +
      ((P : ℝ) * (P - 1) / 2) * (max (y + |z|) 0) ^ (P - 2) * z ^ 2 := by
  have hc : (1 : ℝ) ≤ (P : ℝ) * (P - 1) / 2 := by
    have : (2 : ℝ) ≤ P := by exact_mod_cast hP
    nlinarith
  have hc0 : (0 : ℝ) ≤ (P : ℝ) * (P - 1) / 2 := by linarith
  have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
  rcases le_or_gt y 0 with hy | hy
  · rw [max_eq_right hy]
    simp only [zero_pow (by omega : P ≠ 0), zero_pow (by omega : P - 1 ≠ 0), mul_zero, zero_mul,
      add_zero, zero_add]
    rcases le_or_gt (y + z) 0 with hyz | hyz
    · rw [max_eq_right hyz, zero_pow (by omega)]
      positivity
    · rw [max_eq_left hyz.le]
      have hz : 0 < z := by linarith
      have h1 : y + z ≤ y + |z| := by rw [abs_of_pos hz]
      rw [max_eq_left (by linarith : (0:ℝ) ≤ y + |z|)]
      obtain ⟨m, rfl⟩ : ∃ m, P = m + 2 := ⟨P - 2, by omega⟩
      have e : m + 2 - 2 = m := by omega
      rw [e, pow_add]
      have h2 : (y + z) ^ m ≤ (y + |z|) ^ m := pow_le_pow_left₀ hyz.le h1 m
      have h3 : (y + z) ^ 2 ≤ z ^ 2 := by nlinarith
      have h4 : 0 ≤ (y + z) ^ m := pow_nonneg hyz.le m
      calc (y + z) ^ m * (y + z) ^ 2 ≤ (y + |z|) ^ m * z ^ 2 :=
            mul_le_mul h2 h3 (sq_nonneg _) (pow_nonneg (by linarith) m)
        _ = 1 * (y + |z|) ^ m * z ^ 2 := by ring
        _ ≤ ((↑(m + 2) : ℝ) * (↑(m + 2) - 1) / 2) * (y + |z|) ^ m * z ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hc (pow_nonneg (by linarith) m)) hz2
  · rw [max_eq_left hy.le]
    have hT := pow_taylor y z P hP
    rw [abs_of_pos hy] at hT
    rw [max_eq_left (by positivity : (0:ℝ) ≤ y + |z|)]
    rcases le_or_gt (y + z) 0 with hyz | hyz
    · rw [max_eq_right hyz, zero_pow (by omega)]
      have hpow : 0 ≤ (y + z) ^ P := hev.pow_nonneg _
      -- the remainder identity gives `RHS ≥ (y+z)^P ≥ 0`
      obtain ⟨m, rfl⟩ : ∃ m, P = m + 2 := ⟨P - 2, by omega⟩
      have hb := binom_rem y z m
      rw [abs_of_pos hy] at hb
      have hl := le_abs_self ((y + z) ^ (m + 2) - y ^ (m + 2) - (m + 2) * y ^ (m + 1) * z)
      have e1 : m + 2 - 1 = m + 1 := by omega
      have e2 : m + 2 - 2 = m := by omega
      rw [e1, e2]
      push_cast
      have e3 : ((m : ℝ) + 2) * ((m : ℝ) + 2 - 1) / 2 = ((m + 2) * (m + 1) / 2 : ℝ) := by ring
      rw [e3]
      linarith
    · rw [max_eq_left hyz.le]
      exact hT

/-- (C.202a): the inverse-power bound for small relative increments, `Pε ≤ 1/2` -/
lemma inv_pow_taylor (y z ε : ℝ) (P : ℕ) (hP : 2 ≤ P) (hy : 0 < y) (hε : 0 ≤ ε)
    (hz : |z| ≤ ε * y) (hεP : (P : ℝ) * ε ≤ 1 / 2) :
    1 / (y + z) ^ P ≤ 1 / y ^ P - P * z / y ^ (P + 1) + (P : ℝ) * (P + 1) * z ^ 2 / y ^ (P + 2) := by
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hε1 : ε ≤ 1 / 4 := by nlinarith
  have hzy : z ≥ -(ε * y) := by have := neg_abs_le z; linarith
  have hyz : 0 < y + z := by nlinarith
  set x := z / y with hx
  have hxa : |x| ≤ ε := by rw [hx, abs_div, abs_of_pos hy, div_le_iff₀ hy]; exact hz
  have hx1 : 0 < 1 + x := by
    have := neg_abs_le x; linarith
  set w := -x / (1 + x) with hw
  -- `(y/(y+z))^P = (1 + w)^P`
  have hq : y / (y + z) = 1 + w := by
    rw [hw, hx]; field_simp; ring
  have hT := pow_taylor 1 w P hP
  simp only [one_pow, mul_one, abs_one] at hT
  -- bounds on `w`
  have hxle : 1 - ε ≤ 1 + x := by have := neg_abs_le x; linarith
  have h1ε : 0 < 1 - ε := by linarith
  have hw_abs : |w| ≤ ε / (1 - ε) := by
    rw [hw, abs_div, abs_neg, abs_of_pos hx1]
    exact div_le_div₀ hε hxa h1ε hxle
  have hwlin : (P : ℝ) * w ≤ -(P * x) + P * (2 * x ^ 2) := by
    have e : w = -x + x ^ 2 / (1 + x) := by rw [hw]; field_simp; ring
    rw [e]
    have : x ^ 2 / (1 + x) ≤ 2 * x ^ 2 := by
      rw [div_le_iff₀ hx1]; nlinarith [sq_nonneg x]
    nlinarith
  have hw2 : w ^ 2 ≤ x ^ 2 / (1 - ε) ^ 2 := by
    rw [hw, div_pow, neg_sq]
    exact div_le_div_of_nonneg_left (sq_nonneg x) (by positivity) (pow_le_pow_left₀ h1ε.le hxle 2)
  have hgeo : (1 + |w|) ^ (P - 2) / (1 - ε) ^ 2 ≤ 2 := by
    have hb : 1 + |w| ≤ 1 / (1 - ε) := by
      have : 1 + ε / (1 - ε) = 1 / (1 - ε) := by field_simp; ring
      linarith
    have hpe : (1 - ε) ^ P ≥ 1 / 2 := by
      have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ -ε by linarith) P
      have e : (1 + -ε) = 1 - ε := by ring
      rw [e] at h
      linarith
    have e : (1 / (1 - ε)) ^ (P - 2) / (1 - ε) ^ 2 = 1 / (1 - ε) ^ P := by
      obtain ⟨m, rfl⟩ : ∃ m, P = m + 2 := ⟨P - 2, by omega⟩
      have : m + 2 - 2 = m := by omega
      rw [this, one_div_pow, div_div, ← pow_add]
    calc (1 + |w|) ^ (P - 2) / (1 - ε) ^ 2 ≤ (1 / (1 - ε)) ^ (P - 2) / (1 - ε) ^ 2 := by
          gcongr
      _ = 1 / (1 - ε) ^ P := e
      _ ≤ 2 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hcoef : ((P : ℝ) * (P - 1) / 2) * (1 + |w|) ^ (P - 2) * w ^ 2 ≤
      ((P : ℝ) * (P - 1)) * x ^ 2 := by
    have hc0 : (0 : ℝ) ≤ (P : ℝ) * (P - 1) / 2 := by nlinarith
    calc ((P : ℝ) * (P - 1) / 2) * (1 + |w|) ^ (P - 2) * w ^ 2
        ≤ ((P : ℝ) * (P - 1) / 2) * (1 + |w|) ^ (P - 2) * (x ^ 2 / (1 - ε) ^ 2) := by gcongr
      _ = ((P : ℝ) * (P - 1) / 2) * ((1 + |w|) ^ (P - 2) / (1 - ε) ^ 2) * x ^ 2 := by ring
      _ ≤ ((P : ℝ) * (P - 1) / 2) * 2 * x ^ 2 := by gcongr
      _ = ((P : ℝ) * (P - 1)) * x ^ 2 := by ring
  have hmain : (1 + w) ^ P ≤ 1 - P * x + (P : ℝ) * (P + 1) * x ^ 2 := by
    have e : (P : ℝ) * (P + 1) * x ^ 2 = P * (2 * x ^ 2) + ((P : ℝ) * (P - 1)) * x ^ 2 := by ring
    rw [e]
    linarith
  -- rescale by `y^{-P}`
  have hfrac : 1 / (y + z) ^ P = (y / (y + z)) ^ P / y ^ P := by
    rw [div_pow]; field_simp
  rw [hfrac, hq]
  have hyP : 0 < y ^ P := pow_pos hy P
  calc (1 + w) ^ P / y ^ P ≤ (1 - P * x + (P : ℝ) * (P + 1) * x ^ 2) / y ^ P :=
        div_le_div_of_nonneg_right hmain hyP.le
    _ = 1 / y ^ P - P * z / y ^ (P + 1) + (P : ℝ) * (P + 1) * z ^ 2 / y ^ (P + 2) := by
        rw [hx]; field_simp; ring

end C37

/-! ===== module Base2 ===== -/

/-! # Finite Hölder/Minkowski, scalar linearization and Bernoulli tangents -/

namespace C37

open Finset

/-- power-mean (finite Hölder): `Σ v^q ≤ n^{1−q/P} (Σ v^P)^{q/P}` for `1 ≤ q ≤ P` -/
lemma pow_mean {ι : Type*} (s : Finset ι) (v : ι → ℝ) (hv : ∀ i ∈ s, 0 ≤ v i) (q P : ℕ)
    (hq : 1 ≤ q) (hqP : q ≤ P) :
    ∑ i ∈ s, v i ^ q ≤ (s.card : ℝ) ^ (1 - (q : ℝ) / P) * (∑ i ∈ s, v i ^ P) ^ ((q : ℝ) / P) := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst hs; simp only [sum_empty, card_empty, Nat.cast_zero]
    positivity
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hPR : (q : ℝ) ≤ P := by exact_mod_cast hqP
  have hPpos : (0 : ℝ) < P := by linarith
  have hp1 : (1 : ℝ) ≤ (P : ℝ) / q := by rw [le_div_iff₀ (by linarith)]; linarith
  -- Jensen with uniform weights
  have hJ := Real.rpow_arith_mean_le_arith_mean_rpow s (fun _ => 1 / (s.card : ℝ))
    (fun i => v i ^ q) (fun i _ => by positivity) (by rw [sum_const, nsmul_eq_mul]; field_simp)
    (fun i hi => pow_nonneg (hv i hi) q) hp1
  have hpow : ∀ i ∈ s, (v i ^ q) ^ ((P : ℝ) / q) = v i ^ P := by
    intro i hi
    rw [← Real.rpow_natCast (v i) q, ← Real.rpow_mul (hv i hi), mul_div_cancel₀ _ (by linarith),
      Real.rpow_natCast]
  have hJ' : (∑ i ∈ s, 1 / (s.card : ℝ) * v i ^ q) ^ ((P : ℝ) / q) ≤
      ∑ i ∈ s, 1 / (s.card : ℝ) * v i ^ P :=
    hJ.trans_eq (sum_congr rfl fun i hi => by rw [hpow i hi])
  rw [← mul_sum, ← mul_sum] at hJ'
  clear hJ
  have hS0 : 0 ≤ ∑ i ∈ s, v i ^ q := sum_nonneg fun i hi => pow_nonneg (hv i hi) q
  have hT0 : 0 ≤ ∑ i ∈ s, v i ^ P := sum_nonneg fun i hi => pow_nonneg (hv i hi) P
  -- take the `q/P` power
  have h2 := Real.rpow_le_rpow (by positivity) hJ' (show (0 : ℝ) ≤ q / P by positivity)
  rw [← Real.rpow_mul (by positivity), div_mul_div_cancel₀ (by linarith : (q : ℝ) ≠ 0),
    div_self (by linarith), Real.rpow_one, Real.mul_rpow (by positivity) hT0] at h2
  have hn' : (1 / (s.card : ℝ)) ^ ((q : ℝ) / P) = (s.card : ℝ) ^ (-((q : ℝ) / P)) := by
    rw [one_div, Real.inv_rpow hn.le, Real.rpow_neg hn.le]
  rw [hn'] at h2
  have e : (s.card : ℝ) ^ (1 - (q : ℝ) / P) = s.card * (s.card : ℝ) ^ (-((q : ℝ) / P)) := by
    rw [sub_eq_add_neg, Real.rpow_add hn, Real.rpow_one]
  rw [e]
  calc ∑ i ∈ s, v i ^ q = s.card * (1 / s.card * ∑ i ∈ s, v i ^ q) := by field_simp
    _ ≤ s.card * ((s.card : ℝ) ^ (-((q : ℝ) / P)) * (∑ i ∈ s, v i ^ P) ^ ((q : ℝ) / P)) :=
        mul_le_mul_of_nonneg_left h2 hn.le
    _ = _ := by ring

/-- Minkowski with a constant shift: `(Σ (v+c)^P)^{1/P} ≤ (Σ v^P)^{1/P} + n^{1/P} c` -/
lemma mink_const {ι : Type*} (s : Finset ι) (v : ι → ℝ) (hv : ∀ i ∈ s, 0 ≤ v i) (c : ℝ)
    (hc : 0 ≤ c) (P : ℕ) (hP : 1 ≤ P) :
    (∑ i ∈ s, (v i + c) ^ P) ^ ((1 : ℝ) / P) ≤
      (∑ i ∈ s, v i ^ P) ^ ((1 : ℝ) / P) + (s.card : ℝ) ^ ((1 : ℝ) / P) * c := by
  have hPR : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have h := Real.Lp_add_le_of_nonneg (s := s) (f := v) (g := fun _ => c) hPR hv (fun _ _ => hc)
  simp only [Real.rpow_natCast] at h
  have e : (∑ _i ∈ s, c ^ P) ^ ((1 : ℝ) / P) = (s.card : ℝ) ^ ((1 : ℝ) / P) * c := by
    rw [sum_const, nsmul_eq_mul, Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc, mul_one_div_cancel (by linarith), Real.rpow_one]
  rw [e] at h
  exact h

/-- (I.5, last display): `Σ (v + c)^{P−2} ≤ n^{2/P} ((Σ v^P)^{1/P} + n^{1/P} c)^{P−2}` -/
lemma curv_sum {ι : Type*} (s : Finset ι) (v : ι → ℝ) (hv : ∀ i ∈ s, 0 ≤ v i) (c : ℝ)
    (hc : 0 ≤ c) (P : ℕ) (hP : 3 ≤ P) :
    ∑ i ∈ s, (v i + c) ^ (P - 2) ≤ (s.card : ℝ) ^ ((2 : ℝ) / P) *
      ((∑ i ∈ s, v i ^ P) ^ ((1 : ℝ) / P) + (s.card : ℝ) ^ ((1 : ℝ) / P) * c) ^ (P - 2) := by
  have hu : ∀ i ∈ s, 0 ≤ v i + c := fun i hi => by linarith [hv i hi]
  have h1 := pow_mean s (fun i => v i + c) hu (P - 2) P (by omega) (by omega)
  have hP3 : (3 : ℝ) ≤ P := by exact_mod_cast hP
  have hPR : (0 : ℝ) < P := by linarith
  have e1 : (1 : ℝ) - ((P - 2 : ℕ) : ℝ) / P = 2 / P := by
    rw [Nat.cast_sub (by omega)]; field_simp; ring
  rw [e1] at h1
  have hS0 : 0 ≤ ∑ i ∈ s, (v i + c) ^ P := sum_nonneg fun i hi => pow_nonneg (hu i hi) P
  have e2 : (∑ i ∈ s, (v i + c) ^ P) ^ (((P - 2 : ℕ) : ℝ) / P) =
      ((∑ i ∈ s, (v i + c) ^ P) ^ ((1 : ℝ) / P)) ^ (P - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hS0]; congr 1; field_simp
  rw [e2] at h1
  have hm := mink_const s v hv c hc P (by omega)
  refine h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hm _) (by positivity))

/-- scalar linearization (C.219), (C.231)–(C.232): `c x^{1−θ} ≤ λ x + c R^{1−θ}` when `c R^{−θ} ≤ λ` -/
lemma linearize (c lam R x θ : ℝ) (hc : 0 ≤ c) (hR : 0 < R) (hx : 0 ≤ x) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hcl : c * R ^ (-θ) ≤ lam) :
    c * x ^ (1 - θ) ≤ lam * x + c * R ^ (1 - θ) := by
  have hlam : 0 ≤ lam := le_trans (by positivity) hcl
  rcases le_or_gt R x with hRx | hxR
  · have hx0 : 0 < x := lt_of_lt_of_le hR hRx
    have e : x ^ (1 - θ) = x * x ^ (-θ) := by
      rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]
    have h1 : x ^ (-θ) ≤ R ^ (-θ) := Real.rpow_le_rpow_of_nonpos hR hRx (by linarith)
    have h2 : c * x ^ (1 - θ) ≤ lam * x := by
      rw [e]
      calc c * (x * x ^ (-θ)) = x * (c * x ^ (-θ)) := by ring
        _ ≤ x * (c * R ^ (-θ)) := by gcongr
        _ ≤ x * lam := mul_le_mul_of_nonneg_left hcl hx
        _ = lam * x := by ring
    have h3 : 0 ≤ c * R ^ (1 - θ) := by positivity
    linarith
  · have h1 : x ^ (1 - θ) ≤ R ^ (1 - θ) := Real.rpow_le_rpow hx hxR.le (by linarith)
    have h2 : 0 ≤ lam * x := by positivity
    nlinarith

/-- Bernoulli tangent for real powers: `(n+1)^ν ≥ n^ν + ν n^{ν−1}` (`ν ≥ 1`, `n > 0`) -/
lemma rpow_succ_ge (n ν : ℝ) (hn : 0 < n) (hν : 1 ≤ ν) :
    n ^ ν + ν * n ^ (ν - 1) ≤ (n + 1) ^ ν := by
  have h := one_add_mul_self_le_rpow_one_add (show (-1 : ℝ) ≤ 1 / n by
    have : 0 < 1 / n := by positivity
    linarith) hν
  have e1 : (n + 1) ^ ν = n ^ ν * (1 + 1 / n) ^ ν := by
    rw [← Real.mul_rpow hn.le (by positivity)]; congr 1; field_simp
  have e2 : n ^ (ν - 1) = n ^ ν / n := by rw [Real.rpow_sub_one hn.ne']
  rw [e1, e2]
  have hnν : 0 < n ^ ν := Real.rpow_pos_of_pos hn ν
  calc n ^ ν + ν * (n ^ ν / n) = n ^ ν * (1 + ν * (1 / n)) := by field_simp
    _ ≤ n ^ ν * (1 + 1 / n) ^ ν := mul_le_mul_of_nonneg_left h hnν.le

/-- the natural-power tangent `(n+1)^P ≥ n^P + P n^{P−1}` -/
lemma pow_succ_ge' (n : ℝ) (hn : 0 ≤ n) (m : ℕ) :
    n ^ (m + 1) + (m + 1 : ℕ) * n ^ m ≤ (n + 1) ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : (n + 1) ^ (m + 1 + 1) = (n + 1) * (n + 1) ^ (m + 1) := by ring
    rw [h1]
    have h2 := mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℝ) ≤ n + 1)
    have h3 : 0 ≤ (m + 1 : ℕ) * n ^ m := by positivity
    push_cast at h2 h3 ⊢
    have e : (n + 1) * (n ^ (m + 1) + ((m : ℝ) + 1) * n ^ m) =
        n ^ (m + 1 + 1) + ((m : ℝ) + 1 + 1) * n ^ (m + 1) + ((m : ℝ) + 1) * n ^ m := by ring
    linarith

lemma pow_succ_ge (n : ℝ) (hn : 0 ≤ n) (P : ℕ) (hP : 1 ≤ P) :
    n ^ P + P * n ^ (P - 1) ≤ (n + 1) ^ P := by
  obtain ⟨m, rfl⟩ : ∃ m, P = m + 1 := ⟨P - 1, by omega⟩
  have e : m + 1 - 1 = m := by omega
  rw [e]
  exact_mod_cast pow_succ_ge' n hn m

end C37

/-! ===== module Setup ===== -/

/-! # The scalar difference interface (v1 (C.226)–(C.228)) and its basic consequences -/

namespace C37

open MeasureTheory Finset

/-! ## Parameters -/

lemma log2K_nonneg (K : ℕ) (hK : 1 ≤ K) : 0 ≤ Real.log (2 * (K : ℝ)) :=
  Real.log_nonneg (by have : (1 : ℝ) ≤ K := by exact_mod_cast hK
                      linarith)

lemma Pord_ge (K : ℕ) (hK : 1 ≤ K) : 512 ≤ Pord K := by
  unfold Pord
  have h := log2K_nonneg K hK
  have : (256 : ℝ) ≤ ⌈256 + Real.log (2 * (K : ℝ))⌉₊ :=
    le_trans (by linarith) (Nat.le_ceil _)
  have : 256 ≤ ⌈256 + Real.log (2 * (K : ℝ))⌉₊ := by exact_mod_cast this
  omega

lemma Pord_even (K : ℕ) : Even (Pord K) := ⟨_, (two_mul _)⟩

/-- `B = 2^24 P` -/
lemma Bc_eq (K : ℕ) (hK : 1 ≤ K) : IAFTRL.Bc K = 2 ^ 24 * (Pord K : ℝ) := by
  unfold IAFTRL.Bc Pord
  have h := log2K_nonneg K hK
  rw [Nat.cast_mul, natCast_ceil_eq_intCast_ceil (by linarith)]
  push_cast; ring

lemma Pord_log (K : ℕ) (hK : 1 ≤ K) : Real.log K ≤ (Pord K : ℝ) / 2 := by
  unfold Pord
  have h := log2K_nonneg K hK
  have h1 := Nat.le_ceil (256 + Real.log (2 * (K : ℝ)))
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have h2 : Real.log (2 * (K : ℝ)) = Real.log 2 + Real.log K := Real.log_mul (by norm_num) hK0.ne'
  have h3 := Real.log_two_gt_d9
  push_cast
  linarith

/-- `k = K^{1/P} ≤ e^{1/2}` -/
lemma kfac_le (K : ℕ) (hK : 1 ≤ K) : (K : ℝ) ^ ((1 : ℝ) / Pord K) ≤ Real.exp (1 / 2) := by
  have hP : (0 : ℝ) < Pord K := by have := Pord_ge K hK; exact_mod_cast (by omega : 0 < Pord K)
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  rw [Real.rpow_def_of_pos hK0]
  apply Real.exp_le_exp.mpr
  have := Pord_log K hK
  rw [mul_one_div, div_le_iff₀ hP]
  linarith

lemma exp_half_lt : Real.exp (1 / 2) < 1.65 := by
  have := Real.exp_one_lt_d9
  have h : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  nlinarith [Real.exp_pos (1 / 2)]

lemma kfac_lt (K : ℕ) (hK : 1 ≤ K) : (K : ℝ) ^ ((1 : ℝ) / Pord K) < 1.65 :=
  lt_of_le_of_lt (kfac_le K hK) exp_half_lt

lemma kfac_ge (K : ℕ) (hK : 1 ≤ K) : 1 ≤ (K : ℝ) ^ ((1 : ℝ) / Pord K) :=
  Real.one_le_rpow (by exact_mod_cast hK) (by positivity)

/-- `K ≤ 2^P` -/
lemma K_le_two_pow (K : ℕ) (hK : 1 ≤ K) : (K : ℝ) ≤ 2 ^ Pord K := by
  have hP : (0 : ℝ) < Pord K := by have := Pord_ge K hK; exact_mod_cast (by omega : 0 < Pord K)
  have hk := kfac_lt K hK
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have e : (K : ℝ) = ((K : ℝ) ^ ((1 : ℝ) / Pord K)) ^ Pord K := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK0, one_div_mul_cancel hP.ne', Real.rpow_one]
  rw [e]
  exact pow_le_pow_left₀ (by positivity) (by linarith) _

/-! ## β bounds -/

lemma beta_ge16 (d K n : ℕ) (hd : 1 ≤ d) : 16 ≤ IAFTRL.beta d K n := by
  unfold IAFTRL.beta
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have := Real.sqrt_nonneg ((d : ℝ) * n / (1 + Real.log K))
  linarith

lemma beta_le_Cb (d K n : ℕ) (hK : 1 ≤ K) (hn : 1 ≤ n) :
    IAFTRL.beta d K n ≤ Cb d K * Real.sqrt n := by
  have hlogK := Real.log_nonneg (show (1 : ℝ) ≤ K by exact_mod_cast hK)
  have hnn : (0 : ℝ) ≤ d / (1 + Real.log K) := by positivity
  unfold IAFTRL.beta Cb
  rw [show (d : ℝ) * n / (1 + Real.log K) = d / (1 + Real.log K) * n by ring,
    Real.sqrt_mul hnn]
  have h1 : 1 ≤ Real.sqrt (n : ℝ) := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast hn)
    simpa using this
  have : (0 : ℝ) ≤ 16 * d := by positivity
  nlinarith [Real.sqrt_nonneg (d / (1 + Real.log K))]

lemma Cb_ge16 (d K : ℕ) (hd : 1 ≤ d) : 16 ≤ Cb d K := by
  unfold Cb
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have := Real.sqrt_nonneg ((d : ℝ) / (1 + Real.log K))
  linarith

lemma beta_mono (d K : ℕ) {n m : ℕ} (hnm : n ≤ m) (hK : 1 ≤ K) :
    IAFTRL.beta d K n ≤ IAFTRL.beta d K m := by
  have hlogK := Real.log_nonneg (show (1 : ℝ) ≤ K by exact_mod_cast hK)
  unfold IAFTRL.beta
  have : (d : ℝ) * n / (1 + Real.log K) ≤ d * m / (1 + Real.log K) := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hnm) (by positivity)
  linarith [Real.sqrt_le_sqrt this]

/-! ## The interface -/

section Basic

variable {d K : ℕ} {jstar : Fin K} {Δ : Fin K → ℝ} {Δ₀ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω} {T : ℕ} {C : ℝ} {X D e : ℕ → Fin K → Ω → ℝ}
  {κ : ℕ → Ω → ℝ}

lemma Iface.hK (_ : Iface d K jstar Δ Δ₀ μ F T C X D e κ) : 1 ≤ K :=
  Nat.one_le_iff_ne_zero.mpr (fun h => (h ▸ jstar).elim0)

lemma Iface.Xj (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) : ∀ t ω, X t jstar ω = 0 := by
  intro t ω
  induction t with
  | zero => exact I.X0 jstar ω
  | succ t ih => rw [I.Xs, ih, I.Dj, add_zero]

lemma Iface.Xsum (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) :
    ∀ t a ω, X t a ω = ∑ s ∈ range t, D s a ω := by
  intro t a ω
  induction t with
  | zero => rw [I.X0, sum_range_zero]
  | succ t ih => rw [I.Xs, ih, sum_range_succ]

/-- the filtration is monotone up to time `T` -/
lemma Iface.Fmono (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) :
    ∀ {s t : ℕ}, s ≤ t → t ≤ T → F s ≤ F t := by
  intro s t hst htT
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t hst ih => exact (ih (by omega)).trans (I.filt t (by omega)).2

lemma Iface.Xmeas (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) :
    ∀ t ≤ T, ∀ a, Measurable[F t] (X t a) ∧ Measurable (X t a) := by
  intro t ht a
  have hfun : X t a = fun ω => ∑ s ∈ range t, D s a ω := funext fun ω => I.Xsum t a ω
  rw [hfun]
  refine ⟨Finset.measurable_sum _ fun s hs => ?_, Finset.measurable_sum _ fun s hs => ?_⟩
  · have hs' := Finset.mem_range.mp hs
    exact (I.Dm s (by omega) a).1.mono (I.Fmono (by omega) ht) le_rfl
  · have hs' := Finset.mem_range.mp hs
    exact (I.Dm s (by omega) a).2

lemma Iface.Zxmeas (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) :
    ∀ t ≤ T, ∀ a, Measurable[F t] (Zx X t a) ∧ Measurable (Zx X t a) := by
  intro t ht a
  unfold Zx
  refine ⟨(I.Xmeas t ht a).1.sub (Measurable.iInf fun b => (I.Xmeas t ht b).1),
    (I.Xmeas t ht a).2.sub (Measurable.iInf fun b => (I.Xmeas t ht b).2)⟩

/-! ## Reference gaps and the deterministic envelope -/

lemma iInf_le_X (x : Fin K → ℝ) (b : Fin K) : ⨅ c, x c ≤ x b :=
  ciInf_le (Set.finite_range _).bddBelow b

lemma Zx_nonneg (X : ℕ → Fin K → Ω → ℝ) (t : ℕ) (a : Fin K) (ω : Ω) : 0 ≤ Zx X t a ω := by
  unfold Zx; linarith [iInf_le_X (fun b => X t b ω) a]

/-- if every coordinate is at most `r` in absolute value then `Z ≤ 2r` -/
lemma Zx_le (X : ℕ → Fin K → Ω → ℝ) (t : ℕ) (a : Fin K) (ω : Ω) (r : ℝ)
    (hr : ∀ b, |X t b ω| ≤ r) : Zx X t a ω ≤ 2 * r := by
  have hne : Nonempty (Fin K) := ⟨a⟩
  unfold Zx
  have h1 : -r ≤ ⨅ b, X t b ω := le_ciInf fun b => by have := hr b; linarith [neg_abs_le (X t b ω)]
  have h2 := le_abs_self (X t a ω)
  linarith [hr a]

/-- deterministic envelope `r_{t+1} = (1 + 4/B) r_t + 2β_{t+1}` -/
noncomputable def renv (d K : ℕ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => (1 + 4 / IAFTRL.Bc K) * renv d K t + 2 * IAFTRL.beta d K (t + 1)

lemma Bc_pos (K : ℕ) (hK : 1 ≤ K) : 0 < IAFTRL.Bc K := by
  rw [Bc_eq K hK]; have := Pord_ge K hK; positivity

lemma renv_nonneg (d K : ℕ) (hK : 1 ≤ K) (hd : 1 ≤ d) : ∀ t, 0 ≤ renv d K t := by
  intro t
  induction t with
  | zero => simp [renv]
  | succ t ih =>
    simp only [renv]
    have := Bc_pos K hK
    have := beta_ge16 d K (t + 1) hd
    positivity

lemma Iface.env (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) :
    ∀ t ≤ T, ∀ ω a, |X t a ω| ≤ renv d K t := by
  intro t
  induction t with
  | zero => intro _ ω a; rw [I.X0]; simp [renv]
  | succ t ih =>
    intro ht ω a
    have ih' := ih (by omega) ω
    have hB := Bc_pos K I.hK
    rw [I.Xs]
    have hm := I.mag t (by omega) a ω
    have hz1 := Zx_le X t a ω _ ih'
    have hz2 := Zx_le X t jstar ω _ ih'
    have h4 : (Zx X t a ω + Zx X t jstar ω) / IAFTRL.Bc K ≤ 4 * renv d K t / IAFTRL.Bc K :=
      div_le_div_of_nonneg_right (by linarith) hB.le
    have e : (1 + 4 / IAFTRL.Bc K) * renv d K t = renv d K t + 4 * renv d K t / IAFTRL.Bc K := by
      field_simp
    simp only [renv]
    rw [e]
    have := abs_add_le (X t a ω) (D t a ω)
    linarith [ih' a]

lemma Iface.Dbound (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) :
    ∀ t < T, ∀ ω a, |D t a ω| ≤ 2 * IAFTRL.beta d K (t + 1) + 4 * renv d K t / IAFTRL.Bc K := by
  intro t ht ω a
  have hB := Bc_pos K I.hK
  have ih' := I.env t ht.le ω
  have hm := I.mag t ht a ω
  have hz1 := Zx_le X t a ω _ ih'
  have hz2 := Zx_le X t jstar ω _ ih'
  have h4 : (Zx X t a ω + Zx X t jstar ω) / IAFTRL.Bc K ≤ 4 * renv d K t / IAFTRL.Bc K :=
    div_le_div_of_nonneg_right (by linarith) hB.le
  linarith

lemma Iface.Venv_bound (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) :
    ∀ t ≤ T, ∀ ω a, |Venv d K X jstar t a ω| ≤
      4 * IAFTRL.beta d K (t + 1) + 2 * ((2 * renv d K t) ^ 2 + (2 * renv d K t) ^ 2) /
        (IAFTRL.Bc K * ((t : ℝ) + 1)) := by
  intro t ht ω a
  have hB := Bc_pos K I.hK
  have ih' := I.env t ht ω
  have hz1 := Zx_le X t a ω _ ih'
  have hz2 := Zx_le X t jstar ω _ ih'
  have h0a := Zx_nonneg X t a ω
  have h0j := Zx_nonneg X t jstar ω
  have hβ := beta_ge16 d K (t + 1) I.hd
  unfold Venv
  rw [abs_of_nonneg (by positivity)]
  have hden : 0 < IAFTRL.Bc K * ((t : ℝ) + 1) := by positivity
  gcongr

end Basic

/-! ## Integrability of bounded functions -/

lemma int_of_bdd {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (c : ℝ) (h : ∀ ω, |f ω| ≤ c) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable c
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact h ω)

end C37

/-! ===== module Step ===== -/

/-! # The one-step expectation tool -/

namespace C37

open MeasureTheory Finset

variable {d K : ℕ} {jstar : Fin K} {Δ : Fin K → ℝ} {Δ₀ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω} {T : ℕ} {C : ℝ} {X D e : ℕ → Fin K → Ω → ℝ}
  {κ : ℕ → Ω → ℝ}

lemma Iface.Dint [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ)
    (ht : t < T) (a : Fin K) : Integrable (D t a) μ :=
  int_of_bdd μ _ (I.Dm t ht a).2 _ fun ω => I.Dbound t ht ω a

lemma Iface.Vmeas (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ) (ht : t ≤ T) (a : Fin K) :
    Measurable (Venv d K X jstar t a) := by
  unfold Venv
  exact measurable_const.add ((measurable_const.mul
    (((I.Zxmeas t ht a).2.pow_const 2).add ((I.Zxmeas t ht jstar).2.pow_const 2))).div_const _)

/-- first-order step: `E[g D] = E[g (Δ + e)]` for bounded `F_t`-measurable `g` -/
lemma Iface.step1 [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ)
    (ht : t < T) (a : Fin K) (g : Ω → ℝ) (hg : StronglyMeasurable[F t] g) (c : ℝ)
    (hgb : ∀ ω, |g ω| ≤ c) :
    ∫ ω, g ω * D t a ω ∂μ = ∫ ω, g ω * (Δ a + e t a ω) ∂μ := by
  have hm := (I.filt t ht).1
  have hD := I.Dint t ht a
  have hg0 : AEStronglyMeasurable g μ := (hg.mono hm).aestronglyMeasurable
  have hgD : Integrable (g * D t a) μ :=
    hD.bdd_mul hg0 (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgb ω)
  have h1 : μ[g * D t a | F t] =ᵐ[μ] g * fun ω => Δ a + e t a ω :=
    (condExp_mul_of_stronglyMeasurable_left hg hgD hD).trans
      ((Filter.EventuallyEq.rfl).mul (I.mean t ht a))
  have h2 := integral_condExp (μ := μ) (f := g * D t a) hm
  calc ∫ ω, g ω * D t a ω ∂μ = ∫ ω, (g * D t a) ω ∂μ := rfl
    _ = ∫ ω, (μ[g * D t a | F t]) ω ∂μ := h2.symm
    _ = ∫ ω, (g * fun ω => Δ a + e t a ω) ω ∂μ := integral_congr_ae h1
    _ = _ := rfl

/-- second-order step: `E[g D²] ≤ E[g V]` for bounded nonnegative `F_t`-measurable `g` -/
lemma Iface.step2 [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ)
    (ht : t < T) (a : Fin K) (g : Ω → ℝ) (hg : StronglyMeasurable[F t] g) (c : ℝ)
    (hgb : ∀ ω, |g ω| ≤ c) (hg0 : ∀ ω, 0 ≤ g ω) :
    ∫ ω, g ω * D t a ω ^ 2 ∂μ ≤ ∫ ω, g ω * Venv d K X jstar t a ω ∂μ := by
  have hm := (I.filt t ht).1
  have hD2 : Integrable (fun ω => D t a ω ^ 2) μ :=
    int_of_bdd μ _ ((I.Dm t ht a).2.pow_const 2) _ fun ω => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (I.Dbound t ht ω a) 2
  have hga : AEStronglyMeasurable g μ := (hg.mono hm).aestronglyMeasurable
  have hbd : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ c := Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hgb ω
  have hgD : Integrable (g * fun ω => D t a ω ^ 2) μ := hD2.bdd_mul hga hbd
  have h1 : μ[g * (fun ω => D t a ω ^ 2) | F t] =ᵐ[μ] g * μ[fun ω => D t a ω ^ 2 | F t] :=
    condExp_mul_of_stronglyMeasurable_left hg hgD hD2
  have h2 := integral_condExp (μ := μ) (f := g * fun ω => D t a ω ^ 2) hm
  have hV : Integrable (Venv d K X jstar t a) μ :=
    int_of_bdd μ _ (I.Vmeas t ht.le a) _ fun ω => I.Venv_bound t ht.le ω a
  have hgV : Integrable (fun ω => g ω * Venv d K X jstar t a ω) μ := hV.bdd_mul hga hbd
  have hgC : Integrable (fun ω => g ω * (μ[fun ω => D t a ω ^ 2 | F t]) ω) μ :=
    (integrable_condExp).bdd_mul hga hbd
  calc ∫ ω, g ω * D t a ω ^ 2 ∂μ = ∫ ω, (g * fun ω => D t a ω ^ 2) ω ∂μ := rfl
    _ = ∫ ω, (μ[g * (fun ω => D t a ω ^ 2) | F t]) ω ∂μ := h2.symm
    _ = ∫ ω, g ω * (μ[fun ω => D t a ω ^ 2 | F t]) ω ∂μ := integral_congr_ae h1
    _ ≤ ∫ ω, g ω * Venv d K X jstar t a ω ∂μ := by
        refine integral_mono_ae hgC hgV ?_
        filter_upwards [I.sec t ht a] with ω hω
        exact mul_le_mul_of_nonneg_left hω (hg0 ω)

/-- the integrated Taylor step: a pointwise second-order bound with `F_t`-measurable bounded
coefficients becomes a bound with the conditional mean and second-moment envelope substituted -/
lemma Iface.step [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ)
    (ht : t < T) (H g0 : Ω → ℝ) (g1 g2 : Fin K → Ω → ℝ) (hH : Integrable H μ)
    (hg0 : Integrable g0 μ)
    (hg1 : ∀ a, StronglyMeasurable[F t] (g1 a)) (c1 : Fin K → ℝ) (hg1b : ∀ a ω, |g1 a ω| ≤ c1 a)
    (hg2 : ∀ a, StronglyMeasurable[F t] (g2 a)) (c2 : Fin K → ℝ) (hg2b : ∀ a ω, |g2 a ω| ≤ c2 a)
    (hg2n : ∀ a ω, 0 ≤ g2 a ω)
    (hpt : ∀ᵐ ω ∂μ, H ω ≤ g0 ω + ∑ a, (g1 a ω * D t a ω + g2 a ω * D t a ω ^ 2)) :
    ∫ ω, H ω ∂μ ≤ ∫ ω, (g0 ω + ∑ a, (g1 a ω * (Δ a + e t a ω) +
      g2 a ω * Venv d K X jstar t a ω)) ∂μ := by
  have hm := (I.filt t ht).1
  have hbd1 : ∀ a, ∀ᵐ ω ∂μ, ‖g1 a ω‖ ≤ c1 a := fun a => Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hg1b a ω
  have hbd2 : ∀ a, ∀ᵐ ω ∂μ, ‖g2 a ω‖ ≤ c2 a := fun a => Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hg2b a ω
  have hga1 : ∀ a, AEStronglyMeasurable (g1 a) μ := fun a => ((hg1 a).mono hm).aestronglyMeasurable
  have hga2 : ∀ a, AEStronglyMeasurable (g2 a) μ := fun a => ((hg2 a).mono hm).aestronglyMeasurable
  have hD2 : ∀ a, Integrable (fun ω => D t a ω ^ 2) μ := fun a =>
    int_of_bdd μ _ ((I.Dm t ht a).2.pow_const 2) _ fun ω => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (I.Dbound t ht ω a) 2
  have i1 : ∀ a, Integrable (fun ω => g1 a ω * D t a ω) μ := fun a =>
    (I.Dint t ht a).bdd_mul (hga1 a) (hbd1 a)
  have i2 : ∀ a, Integrable (fun ω => g2 a ω * D t a ω ^ 2) μ := fun a =>
    (hD2 a).bdd_mul (hga2 a) (hbd2 a)
  have hE : ∀ a, Integrable (fun ω => Δ a + e t a ω) μ := fun a =>
    int_of_bdd μ _ (measurable_const.add (((I.κm t ht).2 a).mono hm le_rfl)) 2 fun ω =>
      ((I.κb t ht ω).2.2 a).2
  have j1 : ∀ a, Integrable (fun ω => g1 a ω * (Δ a + e t a ω)) μ := fun a =>
    (hE a).bdd_mul (hga1 a) (hbd1 a)
  have hV : ∀ a, Integrable (Venv d K X jstar t a) μ := fun a =>
    int_of_bdd μ _ (I.Vmeas t ht.le a) _ fun ω => I.Venv_bound t ht.le ω a
  have j2 : ∀ a, Integrable (fun ω => g2 a ω * Venv d K X jstar t a ω) μ := fun a =>
    (hV a).bdd_mul (hga2 a) (hbd2 a)
  have iS : Integrable (fun ω => ∑ a, (g1 a ω * D t a ω + g2 a ω * D t a ω ^ 2)) μ :=
    integrable_finsetSum _ fun a _ => (i1 a).add (i2 a)
  have jS : Integrable (fun ω => ∑ a, (g1 a ω * (Δ a + e t a ω) +
      g2 a ω * Venv d K X jstar t a ω)) μ :=
    integrable_finsetSum _ fun a _ => (j1 a).add (j2 a)
  have iR : Integrable (fun ω => g0 ω + ∑ a, (g1 a ω * D t a ω + g2 a ω * D t a ω ^ 2)) μ :=
    hg0.add iS
  calc ∫ ω, H ω ∂μ ≤ ∫ ω, (g0 ω + ∑ a, (g1 a ω * D t a ω + g2 a ω * D t a ω ^ 2)) ∂μ :=
        integral_mono_ae hH iR hpt
    _ = ∫ ω, g0 ω ∂μ + ∑ a, (∫ ω, g1 a ω * D t a ω ∂μ + ∫ ω, g2 a ω * D t a ω ^ 2 ∂μ) := by
        rw [integral_add hg0 iS, integral_finsetSum
          (f := fun a ω => g1 a ω * D t a ω + g2 a ω * D t a ω ^ 2) _ fun a _ => (i1 a).add (i2 a)]
        congr 1
        exact Finset.sum_congr rfl fun a _ => integral_add (i1 a) (i2 a)
    _ ≤ ∫ ω, g0 ω ∂μ + ∑ a, (∫ ω, g1 a ω * (Δ a + e t a ω) ∂μ +
          ∫ ω, g2 a ω * Venv d K X jstar t a ω ∂μ) :=
        add_le_add le_rfl (Finset.sum_le_sum fun a _ => add_le_add
          (le_of_eq (I.step1 t ht a (g1 a) (hg1 a) (c1 a) (hg1b a)))
          (I.step2 t ht a (g2 a) (hg2 a) (c2 a) (hg2b a) (hg2n a)))
    _ = _ := by
        rw [integral_add hg0 jS, integral_finsetSum
          (f := fun a ω => g1 a ω * (Δ a + e t a ω) + g2 a ω * Venv d K X jstar t a ω) _
          fun a _ => (j1 a).add (j2 a)]
        congr 1
        exact (Finset.sum_congr rfl fun a _ => integral_add (j1 a) (j2 a)).symm

end C37

/-! ===== module AbsAlg ===== -/

/-! # The deterministic one-step inequality for absolute moments (v1 (C.236)–(C.240), (C.231)–(C.233)) -/

namespace C37

open Finset

/-- nat-power linearization: `c A^m ≤ (c/R^{P−m}) A^P + c R^m` -/
lemma lin_pow (c A R : ℝ) (m P : ℕ) (hc : 0 ≤ c) (hA : 0 ≤ A) (hR : 0 < R) (hmP : m ≤ P) :
    c * A ^ m ≤ c / R ^ (P - m) * A ^ P + c * R ^ m := by
  rcases le_or_gt R A with hRA | hAR
  · have hAm : A ^ P = A ^ m * A ^ (P - m) := by rw [← pow_add]; congr 1; omega
    have h1 : R ^ (P - m) ≤ A ^ (P - m) := pow_le_pow_left₀ hR.le hRA _
    have hRp : 0 < R ^ (P - m) := pow_pos hR _
    have h2 : c * A ^ m ≤ c / R ^ (P - m) * A ^ P := by
      rw [hAm, div_mul_eq_mul_div, le_div_iff₀ hRp]
      have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hc (pow_nonneg hA m))
      linarith
    have : 0 ≤ c * R ^ m := by positivity
    linarith
  · have h1 : A ^ m ≤ R ^ m := pow_le_pow_left₀ hA hAR.le m
    have h2 : 0 ≤ c / R ^ (P - m) * A ^ P := by positivity
    nlinarith

/-- `(1 + x)^n ≤ e^{nx}` style: `(1 + 1/(2P))^{P−2} ≤ 2` -/
lemma one_add_half_pow (P : ℕ) (hP : 1 ≤ P) : (1 + 1 / (2 * (P : ℝ))) ^ (P - 2) ≤ 2 := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have h1 : (1 + 1 / (2 * (P : ℝ))) ^ (P - 2) ≤ (1 + 1 / (2 * (P : ℝ))) ^ P :=
    pow_le_pow_right₀ (by have : 0 ≤ 1 / (2 * (P : ℝ)) := by positivity
                          linarith) (by omega)
  have h2 : (1 + 1 / (2 * (P : ℝ))) ^ P ≤ Real.exp (1 / 2) := by
    have := Real.add_one_le_exp (1 / (2 * (P : ℝ)))
    calc (1 + 1 / (2 * (P : ℝ))) ^ P ≤ (Real.exp (1 / (2 * (P : ℝ)))) ^ P :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = Real.exp (1 / 2) := by
          rw [← Real.exp_nat_mul]; congr 1; field_simp
  have h3 := exp_half_lt
  linarith

/-- `|x| ≤ (Σ x^P)^{1/P}` for even `P` -/
lemma abs_le_root {K : ℕ} (x : Fin K → ℝ) (P : ℕ) (hP : 1 ≤ P) (hev : Even P) (a : Fin K) :
    |x a| ≤ (∑ b, x b ^ P) ^ ((1 : ℝ) / P) := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hS : x a ^ P ≤ ∑ b, x b ^ P :=
    single_le_sum (f := fun b => x b ^ P) (fun b _ => hev.pow_nonneg _) (mem_univ a)
  have h1 : |x a| = (|x a| ^ P) ^ ((1 : ℝ) / P) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel hPr.ne',
      Real.rpow_one]
  rw [h1, hev.pow_abs]
  exact Real.rpow_le_rpow (hev.pow_nonneg _) hS (by positivity)

lemma root_pow {K : ℕ} (x : Fin K → ℝ) (P : ℕ) (hP : 1 ≤ P) (hev : Even P) :
    ((∑ b, x b ^ P) ^ ((1 : ℝ) / P)) ^ P = ∑ b, x b ^ P := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hS : 0 ≤ ∑ b, x b ^ P := sum_nonneg fun b _ => hev.pow_nonneg _
  rw [← Real.rpow_natCast, ← Real.rpow_mul hS, one_div_mul_cancel hPr.ne', Real.rpow_one]

end C37

namespace C37

open Finset

lemma Pord_eq (K : ℕ) : Pord K = 2 * hP K := rfl

lemma hP_ge (K : ℕ) (hK : 1 ≤ K) : 256 ≤ hP K := by
  have := Pord_ge K hK; rw [Pord_eq] at this; omega

lemma kK_pos (K : ℕ) (hK : 1 ≤ K) : 0 < kK K := lt_of_lt_of_le one_pos (kfac_ge K hK)

lemma kK_pow (K : ℕ) (hK : 1 ≤ K) (q : ℕ) (hq : q ≤ Pord K) :
    (K : ℝ) ^ (1 - (q : ℝ) / Pord K) = kK K ^ (Pord K - q) := by
  have hP : (0 : ℝ) < Pord K := by have := Pord_ge K hK; exact_mod_cast (by omega : 0 < Pord K)
  unfold kK
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  rw [Nat.cast_sub hq]; field_simp

/-- constants of the absolute-moment recursion -/
noncomputable def Astar (K : ℕ) : ℝ := (16 * kK K) ^ Pord K
/-- drift part (C.237a–b): `Σ P x^{P−1} E ≤ 2 P k A^{P−1}` -/
lemma abs_drift (K : ℕ) (hK : 1 ≤ K) (x E : Fin K → ℝ) (hE : ∀ a, |E a| ≤ 2) :
    ∑ a, (Pord K : ℝ) * x a ^ (Pord K - 1) * E a ≤
      2 * Pord K * kK K * ((∑ b, x b ^ Pord K) ^ ((1 : ℝ) / Pord K)) ^ (Pord K - 1) := by
  set P := Pord K with hPdef
  have hP512 := Pord_ge K hK
  have hev := Pord_even K
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have h1 : ∀ a, (P : ℝ) * x a ^ (P - 1) * E a ≤ 2 * P * |x a| ^ (P - 1) := by
    intro a
    have : x a ^ (P - 1) * E a ≤ |x a ^ (P - 1) * E a| := le_abs_self _
    rw [abs_mul, abs_pow] at this
    have h2 : |x a| ^ (P - 1) * |E a| ≤ |x a| ^ (P - 1) * 2 :=
      mul_le_mul_of_nonneg_left (hE a) (by positivity)
    nlinarith
  have hpm := pow_mean univ (fun a => |x a|) (fun a _ => abs_nonneg _) (P - 1) P (by omega) (by omega)
  simp only [card_univ, Fintype.card_fin] at hpm
  rw [kK_pow K hK (P - 1) (by omega)] at hpm
  have e1 : P - (P - 1) = 1 := by omega
  rw [e1, pow_one] at hpm
  have hS : ∑ b, |x b| ^ P = ∑ b, x b ^ P := sum_congr rfl fun b _ => hev.pow_abs _
  rw [hS] at hpm
  have hS0 : 0 ≤ ∑ b, x b ^ P := sum_nonneg fun b _ => hev.pow_nonneg _
  have e2 : (∑ b, x b ^ P) ^ (((P - 1 : ℕ) : ℝ) / P) = ((∑ b, x b ^ P) ^ ((1 : ℝ) / P)) ^ (P - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hS0]; congr 1; field_simp
  rw [e2] at hpm
  calc ∑ a, (P : ℝ) * x a ^ (P - 1) * E a ≤ ∑ a, 2 * P * |x a| ^ (P - 1) := sum_le_sum fun a _ => h1 a
    _ = 2 * P * ∑ a, |x a| ^ (P - 1) := by rw [mul_sum]
    _ ≤ 2 * P * (kK K * ((∑ b, x b ^ P) ^ ((1 : ℝ) / P)) ^ (P - 1)) :=
        mul_le_mul_of_nonneg_left hpm (by positivity)
    _ = _ := by ring

/-- curvature sum (C.237c–d): `Σ (|x| + δ)^{P−2} ≤ k² (A + k δ)^{P−2}` -/
lemma abs_curv (K : ℕ) (hK : 1 ≤ K) (x : Fin K → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∑ a, (|x a| + δ) ^ (Pord K - 2) ≤ kK K ^ 2 *
      ((∑ b, x b ^ Pord K) ^ ((1 : ℝ) / Pord K) + kK K * δ) ^ (Pord K - 2) := by
  set P := Pord K with hPdef
  have hP512 := Pord_ge K hK
  have hev := Pord_even K
  have hc := curv_sum univ (fun a => |x a|) (fun a _ => abs_nonneg _) δ hδ P (by omega)
  simp only [card_univ, Fintype.card_fin] at hc
  have hS : ∑ b, |x b| ^ P = ∑ b, x b ^ P := sum_congr rfl fun b _ => hev.pow_abs _
  rw [hS] at hc
  have hk2 : (K : ℝ) ^ ((2 : ℝ) / P) = kK K ^ 2 := by
    unfold kK; rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; congr 1; ring
  rw [hk2] at hc
  exact hc

end C37

namespace C37

open Finset

lemma kK_lt (K : ℕ) (hK : 1 ≤ K) : kK K < 1.65 := kfac_lt K hK

lemma Bc_big (K : ℕ) (hK : 1 ≤ K) : 12 * kK K * Pord K ≤ IAFTRL.Bc K := by
  rw [Bc_eq K hK]
  have := kK_lt K hK
  have hP : (0 : ℝ) ≤ Pord K := by positivity
  nlinarith

end C37

namespace C37

open Finset

/-- `A = (Σ x^P)^{1/P}` -/
noncomputable def Aroot {K : ℕ} (x : Fin K → ℝ) : ℝ := (∑ b, x b ^ Pord K) ^ ((1 : ℝ) / Pord K)

lemma Aroot_nonneg {K : ℕ} (x : Fin K → ℝ) : 0 ≤ Aroot x := by
  unfold Aroot; exact Real.rpow_nonneg (sum_nonneg fun b _ => (Pord_even K).pow_nonneg _) _

/-- `√n (n √n)^{h−1} = n^{ν−1}` -/
lemma nu_pow (K : ℕ) (hK : 1 ≤ K) (n : ℝ) (hn : 0 < n) :
    Real.sqrt n * (n * Real.sqrt n) ^ (hP K - 1) = n ^ (nuP K - 1) := by
  have h1 := hP_ge K hK
  have hs : Real.sqrt n = n ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow n
  have hns : n * Real.sqrt n = n ^ ((3 : ℝ) / 2) := by
    rw [hs, ← Real.rpow_one_add' hn.le (by norm_num)]; norm_num
  rw [hns, ← Real.rpow_natCast, ← Real.rpow_mul hn.le, hs, ← Real.rpow_add hn]
  congr 1
  unfold nuP
  rw [Pord_eq, Nat.cast_sub (by omega)]
  push_cast; ring

/-- `n^{h−1} √n ≤ n^{ν−1}` for `n ≥ 1` -/
lemma nu_pow_le (K : ℕ) (hK : 1 ≤ K) (n : ℝ) (hn : 1 ≤ n) :
    n ^ (hP K - 1) * Real.sqrt n ≤ n ^ (nuP K - 1) := by
  have h1 := hP_ge K hK
  have hn0 : 0 < n := by linarith
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hn0]
  apply Real.rpow_le_rpow_of_exponent_le hn
  unfold nuP
  rw [Pord_eq, Nat.cast_sub (by omega)]
  have : (256 : ℝ) ≤ hP K := by exact_mod_cast h1
  push_cast; linarith

end C37

/-! ===== module Abs ===== -/

/-! # Absolute moments (v1 Lemmas C.36–C.37) -/

namespace C37

open MeasureTheory Finset

variable {d K : ℕ} {jstar : Fin K} {Δ : Fin K → ℝ} {Δ₀ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω} {T : ℕ} {C : ℝ} {X D e : ℕ → Fin K → Ω → ℝ}
  {κ : ℕ → Ω → ℝ}

lemma Zx_le_root (X : ℕ → Fin K → Ω → ℝ) (t : ℕ) (a : Fin K) (ω : Ω) :
    Zx X t a ω ≤ 2 * Aroot (fun b => X t b ω) := by
  have hK : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (fun h => (h ▸ a).elim0)
  exact Zx_le X t a ω _ fun b => abs_le_root (fun b => X t b ω) (Pord K)
    (by have := Pord_ge K hK; omega) (Pord_even K) b

lemma Zx_star_le_root (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ) (ω : Ω) :
    Zx X t jstar ω ≤ Aroot (fun b => X t b ω) := by
  have hK := I.hK
  have hne : Nonempty (Fin K) := ⟨jstar⟩
  unfold Zx
  rw [I.Xj t ω, zero_sub]
  have h : -Aroot (fun b => X t b ω) ≤ ⨅ b, X t b ω := le_ciInf fun b => by
    have : |X t b ω| ≤ Aroot (fun b => X t b ω) :=
      abs_le_root (fun b => X t b ω) (Pord K) (by have := Pord_ge K hK; omega) (Pord_even K) b
    linarith [neg_abs_le (X t b ω)]
  linarith

lemma Aroot_le (x : Fin K → ℝ) (r : ℝ) (hr : 0 ≤ r) (hx : ∀ b, |x b| ≤ r) (hK : 1 ≤ K) :
    Aroot x ≤ K * r := by
  have hP := Pord_ge K hK
  have hev := Pord_even K
  have hPr : (0 : ℝ) < Pord K := by exact_mod_cast (show 0 < Pord K by omega)
  have h1 : ∑ b, x b ^ Pord K ≤ ((K : ℝ) * r) ^ Pord K := by
    calc ∑ b, x b ^ Pord K ≤ ∑ _b : Fin K, r ^ Pord K := sum_le_sum fun b _ => by
          rw [← hev.pow_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hx b) _
      _ = K * r ^ Pord K := by simp
      _ ≤ (K : ℝ) ^ Pord K * r ^ Pord K := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : (1 : ℝ) ≤ K := by exact_mod_cast hK
          calc (K : ℝ) = K ^ 1 := (pow_one _).symm
            _ ≤ K ^ Pord K := pow_le_pow_right₀ this (by omega)
      _ = ((K : ℝ) * r) ^ Pord K := (mul_pow _ _ _).symm
  unfold Aroot
  calc (∑ b, x b ^ Pord K) ^ ((1 : ℝ) / Pord K) ≤ (((K : ℝ) * r) ^ Pord K) ^ ((1 : ℝ) / Pord K) :=
        Real.rpow_le_rpow (sum_nonneg fun b _ => hev.pow_nonneg _) h1 (by positivity)
    _ = K * r := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_one_div_cancel hPr.ne',
          Real.rpow_one]

lemma Aroot_meas {m : MeasurableSpace Ω} (X : ℕ → Fin K → Ω → ℝ) (t : ℕ)
    (h : ∀ a, Measurable[m] (X t a)) : Measurable[m] (fun ω => Aroot (fun b => X t b ω)) := by
  unfold Aroot
  exact (Finset.measurable_sum _ fun b _ => (h b).pow_const _).pow_const _

end C37

namespace C37

open MeasureTheory Finset

lemma aplus_le (K : ℕ) (hK : 1 ≤ K) : aplus K ≤ (Pord K : ℝ) / 8 := by
  unfold aplus
  rw [Bc_eq K hK]
  have hk : kK K < 1.65 := kK_lt K hK
  have hk1 : 1 ≤ kK K := kfac_ge K hK
  have hP : (0 : ℝ) < Pord K := by have := Pord_ge K hK; exact_mod_cast (by omega : 0 < Pord K)
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : kK K ^ 2 ≤ 3 := by nlinarith
  nlinarith

lemma vG_le (K : ℕ) (hK : 1 ≤ K) : vG K ≤ 3 * (Pord K : ℝ) / 8 := by
  unfold vG; have := aplus_le K hK; linarith

lemma nu_sub_vG (K : ℕ) (hK : 1 ≤ K) : 3 * (Pord K : ℝ) / 8 ≤ nuP K - vG K := by
  unfold nuP; have := vG_le K hK; linarith

variable {d K : ℕ} {jstar : Fin K} {Δ : Fin K → ℝ} {Δ₀ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω} {T : ℕ} {C : ℝ} {X D e : ℕ → Fin K → Ω → ℝ}
  {κ : ℕ → Ω → ℝ}

end C37

/-! ===== module NegAlg ===== -/

/-! # The deterministic one-step inequality for negative-part moments (v1 (C.212)–(C.220)) -/

namespace C37

open Finset

lemma kK_lt2 (K : ℕ) (hK : 1 ≤ K) : kK K < 2 := lt_trans (kK_lt K hK) (by norm_num)

lemma Bc_ge (K : ℕ) (hK : 1 ≤ K) : 2 ^ 24 * (Pord K : ℝ) ≤ IAFTRL.Bc K := (Bc_eq K hK).ge

end C37

/-! ===== module Neg ===== -/

/-! # Remaining-budget shift and negative moments (v1 Lemmas C.31, C.33) -/

namespace C37

open MeasureTheory Finset

section Defs

variable {K : ℕ} {Ω : Type*}

/-- `N_t = 2 b_t − min_b X_{t,b} = max_a y_{t,a}` -/
noncomputable def Nn (C : ℝ) (κ : ℕ → Ω → ℝ) (X : ℕ → Fin K → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  2 * bR C κ t ω - ⨅ b, X t b ω

lemma bR_succ (C : ℝ) (κ : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    bR C κ (t + 1) ω = bR C κ t ω - κ t ω := by
  unfold bR; rw [sum_range_succ]; ring

lemma Fneg_nonneg (C : ℝ) (κ : ℕ → Ω → ℝ) (X : ℕ → Fin K → Ω → ℝ) (t : ℕ) (ω : Ω) :
    0 ≤ Fneg C κ X t ω :=
  sum_nonneg fun a _ => pow_nonneg (le_max_right _ _) _

lemma yN_le_Nn (C : ℝ) (κ : ℕ → Ω → ℝ) (X : ℕ → Fin K → Ω → ℝ) (t : ℕ) (a : Fin K) (ω : Ω) :
    yN C κ X t a ω ≤ Nn C κ X t ω := by
  unfold yN Nn; linarith [iInf_le_X (fun b => X t b ω) a]

lemma Zx_eq_Nn (C : ℝ) (κ : ℕ → Ω → ℝ) (X : ℕ → Fin K → Ω → ℝ) (t : ℕ) (a : Fin K) (ω : Ω) :
    Zx X t a ω = Nn C κ X t ω - yN C κ X t a ω := by
  unfold Zx Nn yN; ring

lemma Nn_le_root (C : ℝ) (κ : ℕ → Ω → ℝ) (X : ℕ → Fin K → Ω → ℝ) (t : ℕ) (ω : Ω) (hK : 1 ≤ K) :
    Nn C κ X t ω ≤ Aroot (vpos (fun b => yN C κ X t b ω)) := by
  have hne : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
  obtain ⟨a0, ha0⟩ := exists_eq_ciInf_of_finite (f := fun b => X t b ω)
  have h1 : Nn C κ X t ω = yN C κ X t a0 ω := by unfold Nn yN; rw [← ha0]
  rw [h1]
  have h2 : yN C κ X t a0 ω ≤ |vpos (fun b => yN C κ X t b ω) a0| := by
    unfold vpos; rw [abs_of_nonneg (le_max_right _ _)]; exact le_max_left _ _
  exact h2.trans (abs_le_root _ (Pord K) (by have := Pord_ge K hK; omega) (Pord_even K) a0)

/-- `N_t^P ≤ F_t` when `N_t ≥ 0` -/
lemma Nn_pow_le_Fneg (C : ℝ) (κ : ℕ → Ω → ℝ) (X : ℕ → Fin K → Ω → ℝ) (t : ℕ) (ω : Ω) (hK : 1 ≤ K)
    (hN : 0 ≤ Nn C κ X t ω) : Nn C κ X t ω ^ Pord K ≤ Fneg C κ X t ω := by
  have h := Nn_le_root C κ X t ω hK
  have h2 := pow_le_pow_left₀ hN h (Pord K)
  unfold Fneg
  unfold Aroot at h2
  rw [root_pow _ (Pord K) (by have := Pord_ge K hK; omega) (Pord_even K)] at h2
  exact h2

end Defs

variable {d K : ℕ} {jstar : Fin K} {Δ : Fin K → ℝ} {Δ₀ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω} {T : ℕ} {C : ℝ} {X D e : ℕ → Fin K → Ω → ℝ}
  {κ : ℕ → Ω → ℝ}

lemma Iface.Nn_star (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ) (ω : Ω) :
    Zx X t jstar ω = Nn C κ X t ω - 2 * bR C κ t ω := by
  unfold Zx Nn; rw [I.Xj t ω]; ring

lemma Iface.yN_star (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ) (ω : Ω) :
    yN C κ X t jstar ω = 2 * bR C κ t ω := by
  unfold yN; rw [I.Xj t ω]; ring

lemma Iface.bR_le (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ) (ht : t ≤ T) (ω : Ω) :
    bR C κ t ω ≤ C := by
  unfold bR
  have : 0 ≤ ∑ s ∈ range t, κ s ω := sum_nonneg fun s hs => (I.κb s (by
    have := mem_range.mp hs; omega) ω).1
  linarith

lemma Iface.bR_ge (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ) (ht : t ≤ T) (ω : Ω) :
    C - 2 * t ≤ bR C κ t ω := by
  unfold bR
  have : ∑ s ∈ range t, κ s ω ≤ ∑ _s ∈ range t, (2 : ℝ) := sum_le_sum fun s hs => (I.κb s (by
    have := mem_range.mp hs; omega) ω).2.1
  simp at this
  linarith

/-- the budget is not yet exceeded at time `t` -/
lemma Iface.bR_nonneg_ae (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, 0 ≤ bR C κ t ω := by
  filter_upwards [I.κsum] with ω hω
  intro t ht
  unfold bR
  have : ∑ s ∈ range t, κ s ω ≤ ∑ s ∈ range T, κ s ω :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr ht) fun s hs _ => (I.κb s
      (mem_range.mp hs) ω).1
  linarith

lemma Iface.bR_meas (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ) (ht : t ≤ T) :
    Measurable[F t] (bR C κ t) := by
  unfold bR
  exact (Finset.measurable_sum _ fun s hs => ((I.κm s (by have := mem_range.mp hs; omega)).1.mono
    (I.Fmono (by have := mem_range.mp hs; omega) ht) le_rfl)).const_sub C

lemma Iface.yN_meas (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ) (ht : t ≤ T) (a : Fin K) :
    Measurable[F t] (yN C κ X t a) := by
  unfold yN
  exact ((I.bR_meas t ht).const_mul 2).sub (I.Xmeas t ht a).1

lemma Iface.Nn_meas (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ) (ht : t ≤ T) :
    Measurable[F t] (Nn C κ X t) := by
  unfold Nn
  exact ((I.bR_meas t ht).const_mul 2).sub (Measurable.iInf fun b => (I.Xmeas t ht b).1)

lemma Iface.Fneg_meas (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ) (ht : t ≤ T) :
    Measurable[F t] (Fneg C κ X t) := by
  unfold Fneg vpos
  exact Finset.measurable_sum _ fun a _ => ((I.yN_meas t ht a).max measurable_const).pow_const _

lemma Iface.bR_meas' (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ) (ht : t ≤ T) :
    Measurable (bR C κ t) := by
  unfold bR
  exact (Finset.measurable_sum _ fun s hs => ((I.κm s (by have := mem_range.mp hs; omega)).1.mono
    (I.filt s (by have := mem_range.mp hs; omega)).1 le_rfl)).const_sub C

lemma Iface.yN_meas' (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ) (ht : t ≤ T) (a : Fin K) :
    Measurable (yN C κ X t a) := by
  unfold yN
  exact ((I.bR_meas' t ht).const_mul 2).sub (I.Xmeas t ht a).2

lemma Iface.Nn_meas' (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ) (ht : t ≤ T) :
    Measurable (Nn C κ X t) := by
  unfold Nn
  exact ((I.bR_meas' t ht).const_mul 2).sub (Measurable.iInf fun b => (I.Xmeas t ht b).2)

lemma Iface.Fneg_meas' (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ) (ht : t ≤ T) :
    Measurable (Fneg C κ X t) := by
  unfold Fneg vpos
  exact Finset.measurable_sum _ fun a _ => ((I.yN_meas' t ht a).max measurable_const).pow_const _

/-- deterministic bound on the shifted coordinates -/
noncomputable def ry (d K : ℕ) (C : ℝ) (t : ℕ) : ℝ := 2 * (|C| + 2 * t) + renv d K t

lemma Iface.yN_abs (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ) (ht : t ≤ T) (a : Fin K)
    (ω : Ω) : |yN C κ X t a ω| ≤ ry d K C t := by
  unfold yN ry
  have h1 := I.bR_le t ht ω
  have h2 := I.bR_ge t ht ω
  have h3 := I.env t ht ω a
  have hb : |bR C κ t ω| ≤ |C| + 2 * t := by
    rw [abs_le]; constructor <;> linarith [le_abs_self C, neg_abs_le C]
  calc |2 * bR C κ t ω - X t a ω| ≤ |2 * bR C κ t ω| + |X t a ω| := abs_sub _ _
    _ = 2 * |bR C κ t ω| + |X t a ω| := by rw [abs_mul]; norm_num
    _ ≤ _ := by linarith

lemma Iface.Nn_abs (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ) (ht : t ≤ T) (ω : Ω) :
    |Nn C κ X t ω| ≤ ry d K C t := by
  have hK := I.hK
  have hne : Nonempty (Fin K) := ⟨jstar⟩
  obtain ⟨a0, ha0⟩ := exists_eq_ciInf_of_finite (f := fun b => X t b ω)
  have h1 : Nn C κ X t ω = yN C κ X t a0 ω := by unfold Nn yN; rw [← ha0]
  rw [h1]; exact I.yN_abs t ht a0 ω

lemma ry_nonneg (d K : ℕ) (C : ℝ) (t : ℕ) (hK : 1 ≤ K) (hd : 1 ≤ d) : 0 ≤ ry d K C t := by
  unfold ry; have := renv_nonneg d K hK hd t; positivity

end C37

namespace C37

open MeasureTheory Finset

variable {d K : ℕ} {jstar : Fin K} {Δ : Fin K → ℝ} {Δ₀ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω} {T : ℕ} {C : ℝ} {X D e : ℕ → Fin K → Ω → ℝ}
  {κ : ℕ → Ω → ℝ}

lemma Iface.Δnonneg (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (a : Fin K) : 0 ≤ Δ a := by
  by_cases ha : a = jstar
  · rw [ha, I.hΔj]
  · exact le_trans I.hΔ₀.le (I.hΔge a ha)

end C37

/-! ===== module Window ===== -/

/-! # Negative-moment propagation and the window failure probability (v1 (C.211), Lemma C.28) -/

namespace C37

open MeasureTheory Finset

lemma vN_le (K : ℕ) (hK : 1 ≤ K) : vN K ≤ (Pord K : ℝ) / 4000 := by
  unfold vN aminus Lam
  rw [Bc_eq K hK]
  have hk : kK K < 1.65 := kK_lt K hK
  have hk1 : 1 ≤ kK K := kfac_ge K hK
  have hP : (512 : ℝ) ≤ Pord K := by exact_mod_cast Pord_ge K hK
  have e : 6 * (Pord K : ℝ) ^ 2 * kK K ^ 2 / (2 ^ 24 * Pord K) = 6 * Pord K * kK K ^ 2 / 2 ^ 24 := by
    field_simp
  rw [e]
  have : kK K ^ 2 ≤ 3 := by nlinarith
  have h2 : 6 * (Pord K : ℝ) * kK K ^ 2 ≤ 18 * Pord K := by nlinarith
  have h3 : 6 * (Pord K : ℝ) * kK K ^ 2 / 2 ^ 24 ≤ 18 * Pord K / 2 ^ 24 :=
    div_le_div_of_nonneg_right h2 (by norm_num)
  have h4 : 18 * (Pord K : ℝ) / 2 ^ 24 + Pord K / 4096 ≤ Pord K / 4000 := by
    rw [div_add_div _ _ (by norm_num) (by norm_num), div_le_div_iff₀ (by norm_num) (by norm_num)]
    linarith
  linarith

lemma vN_nonneg (K : ℕ) (hK : 1 ≤ K) : 0 ≤ vN K := by
  unfold vN aminus Lam; have := Bc_pos K hK; positivity

lemma nu_sub_vN (K : ℕ) (hK : 1 ≤ K) : (Pord K : ℝ) / 2 ≤ nuP K - vN K := by
  have := vN_le K hK
  have hP : (512 : ℝ) ≤ Pord K := by exact_mod_cast Pord_ge K hK
  unfold nuP; linarith

lemma J0_nonneg (d K : ℕ) (hd : 1 ≤ d) (hK : 1 ≤ K) : 0 ≤ J0 d K := by
  have := Cb_ge16 d K hd
  have := kK_pos K hK
  have hP : (512 : ℝ) ≤ Pord K := by exact_mod_cast Pord_ge K hK
  have hc0 : (0 : ℝ) ≤ (Pord K : ℝ) * (Pord K - 1) / 2 := by nlinarith
  have hc : 0 ≤ cminus d K := by unfold cminus; positivity
  have hL : 0 < Lam K := by unfold Lam; positivity
  have hD : 0 ≤ Dminus d K := by
    unfold Dminus
    exact mul_nonneg (mul_nonneg (mul_nonneg hc0 (sq_nonneg _)) (pow_nonneg (by positivity) _))
      (by unfold wminus; have := Bc_pos K hK; positivity)
  unfold J0
  exact add_nonneg (mul_nonneg hc (pow_nonneg (div_nonneg hc hL.le) _)) hD

/-- one step of the supersolution (C.222) -/
lemma supersol_step (H0 J U v ν n0 n A A' : ℝ) (q : ℕ) (hn0 : 0 < n0) (hn : 1 ≤ n) (hν : 1 ≤ ν)
    (hv0 : 0 ≤ v) (hvq : v ≤ q) (hJ : J ≤ (ν - v) * H0) (hH0 : 0 ≤ H0) (hU : 0 ≤ U)
    (hA : A ≤ H0 * n ^ ν + U * (n / n0) ^ q) (hA' : A' ≤ (1 + v / n) * A + J * n ^ (ν - 1)) :
    A' ≤ H0 * (n + 1) ^ ν + U * ((n + 1) / n0) ^ q := by
  have hn0' : 0 < n := by linarith
  have h1 : (1 + v / n) * A ≤ (1 + v / n) * (H0 * n ^ ν + U * (n / n0) ^ q) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  have hpν := rpow_succ_ge n ν hn0' hν
  have eν : n ^ ν / n = n ^ (ν - 1) := by rw [Real.rpow_sub_one hn0'.ne']
  have hpart : (1 + v / n) * (H0 * n ^ ν) + J * n ^ (ν - 1) ≤ H0 * (n + 1) ^ ν := by
    have e : (1 + v / n) * (H0 * n ^ ν) = H0 * n ^ ν + v * H0 * (n ^ ν / n) := by ring
    rw [e, eν]
    have hnp : 0 ≤ n ^ (ν - 1) := by positivity
    have h3 := mul_le_mul_of_nonneg_right hJ hnp
    have h4 := mul_le_mul_of_nonneg_left hpν hH0
    linarith
  have hhom : (1 + v / n) * (U * (n / n0) ^ q) ≤ U * ((n + 1) / n0) ^ q := by
    have e : ((n + 1) / n0) ^ q = (n / n0) ^ q * (1 + 1 / n) ^ q := by
      rw [← mul_pow]; congr 1; field_simp
    rw [e]
    have hb : 1 + v / n ≤ (1 + 1 / n) ^ q := by
      have := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / n by
        have : 0 < 1 / n := by positivity
        linarith) q
      have h2 : v / n ≤ q * (1 / n) := by
        rw [mul_one_div]; exact div_le_div_of_nonneg_right hvq hn0'.le
      linarith
    have hpos : 0 ≤ U * (n / n0) ^ q := by positivity
    calc (1 + v / n) * (U * (n / n0) ^ q) ≤ (1 + 1 / n) ^ q * (U * (n / n0) ^ q) :=
          mul_le_mul_of_nonneg_right hb hpos
      _ = _ := by ring
  have e2 : (1 + v / n) * (H0 * n ^ ν + U * (n / n0) ^ q) =
      (1 + v / n) * (H0 * n ^ ν) + (1 + v / n) * (U * (n / n0) ^ q) := by ring
  linarith

lemma supersol_seq (H0 J U v ν n0 : ℝ) (q : ℕ) (hn0 : 0 < n0) (hν : 1 ≤ ν)
    (hv0 : 0 ≤ v) (hvq : v ≤ q) (hJ : J ≤ (ν - v) * H0) (hH0 : 0 ≤ H0) (hU : 0 ≤ U)
    (A : ℕ → ℝ) (s0 s1 : ℕ)
    (h0 : A s0 ≤ H0 * ((s0 : ℝ) + 1) ^ ν + U * (((s0 : ℝ) + 1) / n0) ^ q)
    (hstep : ∀ s, s0 ≤ s → s < s1 →
      A (s + 1) ≤ (1 + v / ((s : ℝ) + 1)) * A s + J * ((s : ℝ) + 1) ^ (ν - 1)) :
    ∀ s, s0 ≤ s → s ≤ s1 → A s ≤ H0 * ((s : ℝ) + 1) ^ ν + U * (((s : ℝ) + 1) / n0) ^ q := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => intro _; exact h0
  | succ s hs ih =>
    intro hs1
    have h := supersol_step H0 J U v ν n0 ((s : ℝ) + 1) (A s) (A (s + 1)) q hn0
      (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]) hν hv0 hvq hJ hH0 hU (ih (by omega))
      (hstep s hs (by omega))
    push_cast
    exact h

variable {d K : ℕ} {jstar : Fin K} {Δ : Fin K → ℝ} {Δ₀ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω} {T : ℕ} {C : ℝ} {X D e : ℕ → Fin K → Ω → ℝ}
  {κ : ℕ → Ω → ℝ}

lemma Iface.Fneg_bdd (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ) (ht : t ≤ T) (ω : Ω) :
    Fneg C κ X t ω ≤ K * ry d K C t ^ Pord K := by
  unfold Fneg vpos
  calc ∑ a, max (yN C κ X t a ω) 0 ^ Pord K ≤ ∑ _a : Fin K, ry d K C t ^ Pord K :=
        sum_le_sum fun a _ => pow_le_pow_left₀ (le_max_right _ _)
          (max_le ((le_abs_self _).trans (I.yN_abs t ht a ω))
            (ry_nonneg d K C t I.hK I.hd)) _
    _ = _ := by simp

lemma Iface.Fneg_int [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ)
    (ht : t ≤ T) : Integrable (Fneg C κ X t) μ :=
  int_of_bdd μ _ (I.Fneg_meas' t ht) _ fun ω => by
    rw [abs_of_nonneg (Fneg_nonneg _ _ _ _ _)]; exact I.Fneg_bdd t ht ω

end C37

namespace C37

open MeasureTheory Finset

section Surv

variable {K : ℕ} {Ω : Type*}

variable (C : ℝ) (κ : ℕ → Ω → ℝ) (X : ℕ → Fin K → Ω → ℝ) (m : ℕ) (L : ℝ)

lemma sv_nonneg (s : ℕ) (ω : Ω) : 0 ≤ sv C κ X m L s ω := by
  unfold sv; by_cases h : ω ∈ survSet C κ X m L s <;> simp [h]

lemma sv_le_one (s : ℕ) (ω : Ω) : sv C κ X m L s ω ≤ 1 := by
  unfold sv; by_cases h : ω ∈ survSet C κ X m L s <;> simp [h]

lemma sv_start (ω : Ω) : sv C κ X m L m ω = 1 := by
  unfold sv
  have : ω ∈ survSet C κ X m L m := by simp [survSet]
  simp [this]

lemma survSet_succ (s : ℕ) (hms : m ≤ s) :
    survSet C κ X m L (s + 1) = survSet C κ X m L s ∩ {ω | Fneg C κ X s ω ≤ L} := by
  ext ω
  simp only [survSet, Set.mem_setOf_eq, Set.mem_inter_iff, Finset.mem_Ico]
  constructor
  · intro h
    exact ⟨fun j hj => h j ⟨hj.1, by omega⟩, h s ⟨hms, by omega⟩⟩
  · rintro ⟨h1, h2⟩ j hj
    rcases Nat.lt_or_ge j s with hjs | hjs
    · exact h1 j ⟨hj.1, hjs⟩
    · have : j = s := by omega
      rw [this]; exact h2

lemma survSet_anti (s s' : ℕ) (hss : s ≤ s') : survSet C κ X m L s' ⊆ survSet C κ X m L s := by
  intro ω hω j hj
  simp only [Finset.mem_Ico] at hj
  exact hω j (Finset.mem_Ico.mpr ⟨hj.1, by omega⟩)

lemma sv_step (s : ℕ) (hms : m ≤ s) (ω : Ω) :
    sv C κ X m L (s + 1) ω * Fneg C κ X s ω + L * (1 - sv C κ X m L (s + 1) ω) ≤
      sv C κ X m L s ω * Fneg C κ X s ω + L * (1 - sv C κ X m L s ω) := by
  unfold sv
  rw [survSet_succ C κ X m L s hms]
  by_cases h1 : ω ∈ survSet C κ X m L s
  · by_cases h2 : Fneg C κ X s ω ≤ L
    · have : ω ∈ survSet C κ X m L s ∩ {ω | Fneg C κ X s ω ≤ L} := ⟨h1, h2⟩
      simp [this, h1]
    · have : ω ∉ survSet C κ X m L s ∩ {ω | Fneg C κ X s ω ≤ L} := fun h => h2 h.2
      simp [this, h1]; linarith [not_le.mp h2]
  · have : ω ∉ survSet C κ X m L s ∩ {ω | Fneg C κ X s ω ≤ L} := fun h => h1 h.1
    simp [this, h1]

end Surv

variable {d K : ℕ} {jstar : Fin K} {Δ : Fin K → ℝ} {Δ₀ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω} {T : ℕ} {C : ℝ} {X D e : ℕ → Fin K → Ω → ℝ}
  {κ : ℕ → Ω → ℝ}

lemma Iface.survSet_meas (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (m : ℕ) (L : ℝ) (s s' : ℕ)
    (hss : s ≤ s' + 1) (hs' : s' ≤ T) : MeasurableSet[F s'] (survSet C κ X m L s) := by
  have e : survSet C κ X m L s = ⋂ j ∈ Finset.Ico m s, {ω | Fneg C κ X j ω ≤ L} := by
    ext ω; simp [survSet]
  rw [e]
  refine Finset.measurableSet_biInter _ fun j hj => ?_
  have hj' := (Finset.mem_Ico.mp hj).2
  exact measurableSet_le ((I.Fneg_meas j (by omega)).mono (I.Fmono (by omega) hs') le_rfl)
    measurable_const

lemma Iface.survSet_meas' (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (m : ℕ) (L : ℝ) (s : ℕ)
    (hs : s ≤ T + 1) : MeasurableSet (survSet C κ X m L s) := by
  have e : survSet C κ X m L s = ⋂ j ∈ Finset.Ico m s, {ω | Fneg C κ X j ω ≤ L} := by
    ext ω; simp [survSet]
  rw [e]
  refine Finset.measurableSet_biInter _ fun j hj => ?_
  have hj' := (Finset.mem_Ico.mp hj).2
  exact measurableSet_le (I.Fneg_meas' j (by omega)) measurable_const

lemma Iface.sv_meas (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (m : ℕ) (L : ℝ) (s s' : ℕ)
    (hss : s ≤ s' + 1) (hs' : s' ≤ T) : Measurable[F s'] (sv C κ X m L s) := by
  have hS := I.survSet_meas m L s s' hss hs'
  have hc : Measurable[F s'] (fun _ : Ω => (1 : ℝ)) := measurable_const
  exact hc.indicator hS

lemma Iface.sv_meas' (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (m : ℕ) (L : ℝ) (s : ℕ)
    (hs : s ≤ T + 1) : Measurable (sv C κ X m L s) := by
  have hS := I.survSet_meas' m L s hs
  have hc : Measurable (fun _ : Ω => (1 : ℝ)) := measurable_const
  exact hc.indicator hS

lemma Iface.svF_int [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (m : ℕ)
    (L : ℝ) (s s' : ℕ) (hs : s ≤ T + 1) (hs' : s' ≤ T) :
    Integrable (fun ω => sv C κ X m L s ω * Fneg C κ X s' ω) μ :=
  int_of_bdd μ _ ((I.sv_meas' m L s hs).mul (I.Fneg_meas' s' hs')) (K * ry d K C s' ^ Pord K)
    fun ω => by
      rw [abs_mul, abs_of_nonneg (sv_nonneg C κ X m L s ω), abs_of_nonneg (Fneg_nonneg _ _ _ _ _)]
      calc sv C κ X m L s ω * Fneg C κ X s' ω ≤ 1 * (K * ry d K C s' ^ Pord K) :=
            mul_le_mul (sv_le_one C κ X m L s ω) (I.Fneg_bdd s' hs' ω) (Fneg_nonneg _ _ _ _ _)
              zero_le_one
        _ = _ := one_mul _

lemma Iface.sv_int [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (m : ℕ)
    (L : ℝ) (s : ℕ) (hs : s ≤ T + 1) : Integrable (sv C κ X m L s) μ :=
  int_of_bdd μ _ (I.sv_meas' m L s hs) 1 fun ω => by
    rw [abs_of_nonneg (sv_nonneg C κ X m L s ω)]; exact sv_le_one C κ X m L s ω

end C37

/-! ===== module Local ===== -/

/-! # Compensated local process on a surviving window (v1 Lemma C.29) -/

namespace C37

open MeasureTheory Finset

section LDefs

variable {K : ℕ} {Ω : Type*}

variable (C : ℝ) (κ : ℕ → Ω → ℝ) (X : ℕ → Fin K → Ω → ℝ) (m : ℕ) (θ : ℝ)

lemma Ii_mem {s : ℕ} {ω : Ω} (h : ω ∈ Iset C κ X m θ s) : Ii C κ X m θ s ω = 1 := by
  unfold Ii; simp [h]

lemma Ii_nmem {s : ℕ} {ω : Ω} (h : ω ∉ Iset C κ X m θ s) : Ii C κ X m θ s ω = 0 := by
  unfold Ii; simp [h]

lemma Ii_nonneg (s : ℕ) (ω : Ω) : 0 ≤ Ii C κ X m θ s ω := by
  by_cases h : ω ∈ Iset C κ X m θ s
  · rw [Ii_mem C κ X m θ h]; norm_num
  · rw [Ii_nmem C κ X m θ h]

lemma Ii_le_one (s : ℕ) (ω : Ω) : Ii C κ X m θ s ω ≤ 1 := by
  by_cases h : ω ∈ Iset C κ X m θ s
  · rw [Ii_mem C κ X m θ h]
  · rw [Ii_nmem C κ X m θ h]; norm_num

lemma Yc_succ (e D : ℕ → Fin K → Ω → ℝ) (hXs : ∀ t a ω, X (t + 1) a ω = X t a ω + D t a ω)
    (s : ℕ) (a : Fin K) (ω : Ω) :
    Yc C θ X e (s + 1) a ω = Yc C θ X e s a ω + (D s a ω - e s a ω) := by
  unfold Yc Ecum; rw [hXs, sum_range_succ]; ring

end LDefs

/-- bounded on a box -/
lemma bdd2 (ψ : ℝ × ℝ → ℝ) (hψ : Continuous ψ) (a2 b2 a3 b3 : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ y z, y ∈ Set.Icc a2 b2 → z ∈ Set.Icc a3 b3 → |ψ (y, z)| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Set.Icc a2 b2 ×ˢ Set.Icc a3 b3) hψ.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun y z hy hz => ?_⟩
  have := hM (y, z) ⟨hy, hz⟩
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

variable {d K : ℕ} {jstar : Fin K} {Δ : Fin K → ℝ} {Δ₀ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω} {T : ℕ} {C : ℝ} {X D e : ℕ → Fin K → Ω → ℝ}
  {κ : ℕ → Ω → ℝ}

lemma Iface.Iset_succ (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (m : ℕ) (θ : ℝ) (s : ℕ)
    (hs : s < T) : Iset C κ X m θ (s + 1) ⊆ Iset C κ X m θ s := by
  rintro ω ⟨hB, hS⟩
  refine ⟨?_, survSet_anti C κ X m _ (s + 1) (s + 1 + 1) (by omega) hS⟩
  simp only [BokSet, Set.mem_setOf_eq] at hB ⊢
  rw [sum_range_succ] at hB
  linarith [(I.κb s hs ω).1]

lemma Iface.Ii_succ_le (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (m : ℕ) (θ : ℝ) (s : ℕ)
    (hs : s < T) (ω : Ω) : Ii C κ X m θ (s + 1) ω ≤ Ii C κ X m θ s ω := by
  by_cases h : ω ∈ Iset C κ X m θ (s + 1)
  · rw [Ii_mem C κ X m θ h, Ii_mem C κ X m θ (I.Iset_succ m θ s hs h)]
  · rw [Ii_nmem C κ X m θ h]; exact Ii_nonneg C κ X m θ s ω

lemma Iface.e_abs (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (s : ℕ) (hs : s < T) (a : Fin K)
    (ω : Ω) : |e s a ω| ≤ 4 := by
  have h1 := ((I.κb s hs ω).2.2 a).1
  have h2 := (I.κb s hs ω).2.1
  linarith

/-- the deterministic facts on the surviving window (C.197), (C.199) -/
lemma Iface.Iset_facts (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (m : ℕ) (θ : ℝ) (s : ℕ)
    (hθ : 0 < θ) (hms : m ≤ s) (hsT : s ≤ T) (ω : Ω) (hω : ω ∈ Iset C κ X m θ s) (a : Fin K) :
    0 ≤ bR C κ s ω ∧ |Ecum e s a ω| ≤ 2 * C ∧ Nn C κ X s ω ≤ θ ∧ θ ≤ Yc C θ X e s a ω ∧
      Zx X s a ω + Zx X s jstar ω ≤ Yc C θ X e s a ω ∧
      Yc C θ X e s a ω ≤ renv d K s + 4 * C + 2 * θ := by
  have hK := I.hK
  obtain ⟨hB, hS⟩ := hω
  simp only [BokSet, Set.mem_setOf_eq] at hB
  have hb : 0 ≤ bR C κ s ω := by unfold bR; linarith
  have hE : |Ecum e s a ω| ≤ 2 * C := by
    unfold Ecum
    calc |∑ i ∈ range s, e i a ω| ≤ ∑ i ∈ range s, |e i a ω| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ range s, 2 * κ i ω := sum_le_sum fun i hi =>
          ((I.κb i (by have := mem_range.mp hi; omega) ω).2.2 a).1
      _ = 2 * ∑ i ∈ range s, κ i ω := by rw [mul_sum]
      _ ≤ 2 * C := by linarith
  have hN0 : 0 ≤ Nn C κ X s ω := by
    have := yN_le_Nn C κ X s jstar ω
    rw [I.yN_star s ω] at this; linarith
  have hF : Fneg C κ X s ω ≤ θ ^ Pord K := hS s (Finset.mem_Ico.mpr ⟨hms, by omega⟩)
  have hNθ : Nn C κ X s ω ≤ θ := by
    have h1 := Nn_pow_le_Fneg C κ X s ω hK hN0
    exact (pow_le_pow_iff_left₀ hN0 hθ.le (by have := Pord_ge K hK; omega)).mp (h1.trans hF)
  have hya := yN_le_Nn C κ X s a ω
  have hXa : -θ ≤ X s a ω := by unfold yN at hya; linarith
  have hEl := neg_abs_le (Ecum e s a ω)
  have hEu := le_abs_self (Ecum e s a ω)
  have hY : θ ≤ Yc C θ X e s a ω := by unfold Yc; linarith
  have hZ : Zx X s a ω + Zx X s jstar ω ≤ Yc C θ X e s a ω := by
    rw [Zx_eq_Nn C κ X s a ω, I.Nn_star s ω]
    unfold Yc yN
    linarith
  have hXu := I.env s hsT ω a
  have hYu : Yc C θ X e s a ω ≤ renv d K s + 4 * C + 2 * θ := by
    unfold Yc; linarith [le_abs_self (X s a ω)]
  exact ⟨hb, hE, hNθ, hY, hZ, hYu⟩

lemma Iface.Ecum_meas (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (s : ℕ) (hs : s ≤ T) (a : Fin K) :
    Measurable[F s] (Ecum e s a) :=
  Finset.measurable_sum _ fun i hi => ((I.κm i (by have := mem_range.mp hi; omega)).2 a).mono
    (I.Fmono (by have := mem_range.mp hi; omega) hs) le_rfl

lemma Iface.Ecum_meas' (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (s : ℕ) (hs : s ≤ T) (a : Fin K) :
    Measurable (Ecum e s a) :=
  Finset.measurable_sum _ fun i hi => ((I.κm i (by have := mem_range.mp hi; omega)).2 a).mono
    (I.filt i (by have := mem_range.mp hi; omega)).1 le_rfl

lemma Iface.Yc_meas (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (θ : ℝ) (s : ℕ) (hs : s ≤ T)
    (a : Fin K) : Measurable[F s] (Yc C θ X e s a) := by
  unfold Yc
  exact (((I.Xmeas s hs a).1.sub (I.Ecum_meas s hs a)).add_const _).add_const _

lemma Iface.Yc_meas' (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (θ : ℝ) (s : ℕ) (hs : s ≤ T)
    (a : Fin K) : Measurable (Yc C θ X e s a) := by
  unfold Yc
  exact (((I.Xmeas s hs a).2.sub (I.Ecum_meas' s hs a)).add_const _).add_const _

lemma Iface.Iset_meas (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (m : ℕ) (θ : ℝ) (s : ℕ)
    (hs : s ≤ T) : MeasurableSet[F s] (Iset C κ X m θ s) := by
  refine MeasurableSet.inter ?_ (I.survSet_meas m _ (s + 1) s le_rfl hs)
  exact measurableSet_le (Finset.measurable_sum _ fun i hi => (I.κm i (by
    have := mem_range.mp hi; omega)).1.mono (I.Fmono (by have := mem_range.mp hi; omega) hs) le_rfl)
    measurable_const

lemma Iface.Iset_meas' (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (m : ℕ) (θ : ℝ) (s : ℕ)
    (hs : s ≤ T) : MeasurableSet (Iset C κ X m θ s) := by
  refine MeasurableSet.inter ?_ (I.survSet_meas' m _ (s + 1) (by omega))
  exact measurableSet_le (Finset.measurable_sum _ fun i hi => (I.κm i (by
    have := mem_range.mp hi; omega)).1.mono (I.filt i (by have := mem_range.mp hi; omega)).1 le_rfl)
    measurable_const

lemma Iface.Ii_meas (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (m : ℕ) (θ : ℝ) (s : ℕ)
    (hs : s ≤ T) : Measurable[F s] (Ii C κ X m θ s) := by
  have hc : Measurable[F s] (fun _ : Ω => (1 : ℝ)) := measurable_const
  exact hc.indicator (I.Iset_meas m θ s hs)

lemma Iface.Ii_meas' (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (m : ℕ) (θ : ℝ) (s : ℕ)
    (hs : s ≤ T) : Measurable (Ii C κ X m θ s) := by
  have hc : Measurable (fun _ : Ω => (1 : ℝ)) := measurable_const
  exact hc.indicator (I.Iset_meas' m θ s hs)

/-- functions `I_s · f(Y_s, e_s)` with continuous `f` are predictable and bounded -/
lemma Iface.Ii_comp (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (m : ℕ) (θ : ℝ) (s : ℕ)
    (a : Fin K) (hθ : 0 < θ) (hms : m ≤ s) (hsT : s < T) (f : ℝ × ℝ → ℝ) (hf : Continuous f) :
    ∃ M, 0 ≤ M ∧ Measurable[F s] (fun ω => Ii C κ X m θ s ω * f (Yc C θ X e s a ω, e s a ω)) ∧
      ∀ ω, |Ii C κ X m θ s ω * f (Yc C θ X e s a ω, e s a ω)| ≤ M := by
  obtain ⟨M, hM0, hM⟩ := bdd2 f hf θ (renv d K s + 4 * C + 2 * θ) (-4) 4
  refine ⟨M, hM0, (I.Ii_meas m θ s hsT.le).mul (hf.measurable.comp
    ((I.Yc_meas θ s hsT.le a).prodMk ((I.κm s hsT).2 a))), fun ω => ?_⟩
  by_cases h : ω ∈ Iset C κ X m θ s
  · rw [Ii_mem C κ X m θ h, one_mul]
    have hf := I.Iset_facts m θ s hθ hms hsT.le ω h a
    exact hM _ _ ⟨hf.2.2.2.1, hf.2.2.2.2.2⟩ (abs_le.mp (I.e_abs s hsT a ω))
  · rw [Ii_nmem C κ X m θ h, zero_mul, abs_zero]; exact hM0

/-- the one-arm version of the integrated Taylor step -/
lemma Iface.step_one [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ)
    (ht : t < T) (a : Fin K) (H g0 g1 g2 : Ω → ℝ) (hH : Integrable H μ) (hg0 : Integrable g0 μ)
    (hg1 : Measurable[F t] g1) (c1 : ℝ) (hg1b : ∀ ω, |g1 ω| ≤ c1) (hc1 : 0 ≤ c1)
    (hg2 : Measurable[F t] g2) (c2 : ℝ) (hg2b : ∀ ω, |g2 ω| ≤ c2) (hc2 : 0 ≤ c2)
    (hg2n : ∀ ω, 0 ≤ g2 ω) (hpt : ∀ ω, H ω ≤ g0 ω + (g1 ω * D t a ω + g2 ω * D t a ω ^ 2)) :
    ∫ ω, H ω ∂μ ≤ ∫ ω, (g0 ω + (g1 ω * (Δ a + e t a ω) + g2 ω * Venv d K X jstar t a ω)) ∂μ := by
  have h := I.step t ht H g0 (fun b ω => if b = a then g1 ω else 0)
    (fun b ω => if b = a then g2 ω else 0) hH hg0
    (fun b => by
      by_cases hb : b = a
      · subst hb; simp only [if_true]; exact hg1.stronglyMeasurable
      · simp only [hb, if_false]; exact stronglyMeasurable_const)
    (fun _ => c1)
    (fun b ω => by by_cases hb : b = a <;> simp [hb, hg1b ω, hc1])
    (fun b => by
      by_cases hb : b = a
      · subst hb; simp only [if_true]; exact hg2.stronglyMeasurable
      · simp only [hb, if_false]; exact stronglyMeasurable_const)
    (fun _ => c2)
    (fun b ω => by by_cases hb : b = a <;> simp [hb, hg2b ω, hc2])
    (fun b ω => by by_cases hb : b = a <;> simp [hb, hg2n ω])
    (Filter.Eventually.of_forall fun ω => by
      have e1 : ∑ b, ((if b = a then g1 ω else 0) * D t b ω + (if b = a then g2 ω else 0) * D t b ω ^ 2) =
          g1 ω * D t a ω + g2 ω * D t a ω ^ 2 := by
        rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (fun h => absurd (mem_univ a) h)]
        simp
      rw [e1]; exact hpt ω)
  have e2 : ∀ ω, ∑ b, ((if b = a then g1 ω else 0) * (Δ b + e t b ω) +
      (if b = a then g2 ω else 0) * Venv d K X jstar t b ω) =
        g1 ω * (Δ a + e t a ω) + g2 ω * Venv d K X jstar t a ω := fun ω => by
    rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (fun h => absurd (mem_univ a) h)]
    simp
  simp only [e2] at h
  exact h

end C37

/-! ===== module LocalStep ===== -/

/-! # One-step inverse and positive local moments (v1 (C.202), (C.120)) -/

namespace C37

open MeasureTheory Finset

variable {d K : ℕ} {jstar : Fin K} {Δ : Fin K → ℝ} {Δ₀ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω} {T : ℕ} {C : ℝ} {X D e : ℕ → Fin K → Ω → ℝ}
  {κ : ℕ → Ω → ℝ}

/-- the relative increment on the surviving window (C.200) -/
lemma Iface.xi_rel (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (m : ℕ) (θ : ℝ) (s : ℕ) (a : Fin K)
    (hθ : 0 < θ) (hms : m ≤ s) (hsT : s < T)
    (hQ1 : 3 * IAFTRL.Bc K * IAFTRL.beta d K (s + 1) ≤ θ) (ω : Ω) (hω : ω ∈ Iset C κ X m θ s) :
    |D s a ω - e s a ω| ≤ 2 / IAFTRL.Bc K * Yc C θ X e s a ω := by
  have hK := I.hK
  have hB := Bc_pos K hK
  have hf := I.Iset_facts m θ s hθ hms hsT.le ω hω a
  have hβ := beta_ge16 d K (s + 1) I.hd
  have hm := I.mag s hsT a ω
  have he := I.e_abs s hsT a ω
  have h1 : (Zx X s a ω + Zx X s jstar ω) / IAFTRL.Bc K ≤ Yc C θ X e s a ω / IAFTRL.Bc K :=
    div_le_div_of_nonneg_right hf.2.2.2.2.1 hB.le
  have h2 : 3 * IAFTRL.beta d K (s + 1) ≤ Yc C θ X e s a ω / IAFTRL.Bc K := by
    rw [le_div_iff₀ hB]; linarith [hf.2.2.2.1]
  have h3 : |D s a ω - e s a ω| ≤ |D s a ω| + |e s a ω| := abs_sub _ _
  have e1 : 2 / IAFTRL.Bc K * Yc C θ X e s a ω = Yc C θ X e s a ω / IAFTRL.Bc K +
      Yc C θ X e s a ω / IAFTRL.Bc K := by ring
  rw [e1]
  linarith

lemma Iface.Venv_le (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (m : ℕ) (θ : ℝ) (s : ℕ) (a : Fin K)
    (hθ : 0 < θ) (hms : m ≤ s) (hsT : s < T) (ω : Ω) (hω : ω ∈ Iset C κ X m θ s) :
    Venv d K X jstar s a ω ≤ 4 * IAFTRL.beta d K (s + 1) +
      2 * Yc C θ X e s a ω ^ 2 / (IAFTRL.Bc K * ((s : ℝ) + 1)) := by
  have hB := Bc_pos K I.hK
  have hf := I.Iset_facts m θ s hθ hms hsT.le ω hω a
  have h0a := Zx_nonneg X s a ω
  have h0j := Zx_nonneg X s jstar ω
  unfold Venv
  have : Zx X s a ω ^ 2 + Zx X s jstar ω ^ 2 ≤ Yc C θ X e s a ω ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hf.2.2.2.2.1 2
    have : 0 ≤ Zx X s a ω * Zx X s jstar ω := mul_nonneg h0a h0j
    linarith
  have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 2))
    (by positivity : (0 : ℝ) ≤ IAFTRL.Bc K * ((s : ℝ) + 1))
  linarith

set_option maxHeartbeats 1000000 in
/-- (C.202): the one-step inverse-moment inequality on the surviving window -/
lemma Iface.inv_step [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ)
    (m : ℕ) (θ : ℝ) (s : ℕ) (a : Fin K) (hθ : 0 < θ) (hms : m ≤ s) (hsT : s < T)
    (hQ1 : 3 * IAFTRL.Bc K * IAFTRL.beta d K (s + 1) ≤ θ)
    (hQ2 : 20 * ((Pord K : ℝ) + 1) * IAFTRL.beta d K (s + 1) * ((s : ℝ) + 1) ≤ θ ^ 2) :
    ∫ ω, Ii C κ X m θ (s + 1) ω * (1 / max θ (Yc C θ X e (s + 1) a ω)) ^ Pord K ∂μ ≤
      ∫ ω, Ii C κ X m θ s ω * ((1 + Pord K / (2 * ((s : ℝ) + 1))) *
        (1 / max θ (Yc C θ X e s a ω)) ^ Pord K -
        Pord K * Δ a * (1 / max θ (Yc C θ X e s a ω)) ^ (Pord K + 1)) ∂μ := by
  have hK := I.hK
  have hP := Pord_ge K hK
  have hPr : (512 : ℝ) ≤ Pord K := by exact_mod_cast hP
  have hB := Bc_pos K hK
  have hBge := Bc_ge K hK
  set P := Pord K with hPdef
  set B := IAFTRL.Bc K with hBdef
  set β := IAFTRL.beta d K (s + 1) with hβdef
  set n : ℝ := (s : ℝ) + 1 with hn
  have hn1 : (1 : ℝ) ≤ n := by simp only [n]; linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
  have hβ16 : 16 ≤ β := beta_ge16 d K (s + 1) I.hd
  have hmF := (I.filt s hsT).1
  obtain ⟨qf, hqf⟩ : ∃ qf : ℝ × ℝ → ℝ, qf = fun p => 1 / max θ p.1 := ⟨_, rfl⟩
  have hq : Continuous qf := by
    rw [hqf]
    exact continuous_const.div (continuous_const.max continuous_fst)
      (fun p => ne_of_gt (lt_of_lt_of_le hθ (le_max_left _ _)))
  let f0 : ℝ × ℝ → ℝ := fun p => qf p ^ P + P * p.2 * qf p ^ (P + 1) +
    P * (P + 1) * p.2 ^ 2 * qf p ^ (P + 2)
  let f1 : ℝ × ℝ → ℝ := fun p => -(P : ℝ) * qf p ^ (P + 1) - 2 * p.2 * (P * (P + 1)) * qf p ^ (P + 2)
  let f2 : ℝ × ℝ → ℝ := fun p => P * (P + 1) * qf p ^ (P + 2)
  have hf0 : Continuous f0 := by fun_prop
  have hf1 : Continuous f1 := by fun_prop
  have hf2 : Continuous f2 := by fun_prop
  obtain ⟨M0, hM0, hm0, hb0⟩ := I.Ii_comp m θ s a hθ hms hsT f0 hf0
  obtain ⟨M1, hM1, hm1, hb1⟩ := I.Ii_comp m θ s a hθ hms hsT f1 hf1
  obtain ⟨M2, hM2, hm2, hb2⟩ := I.Ii_comp m θ s a hθ hms hsT f2 hf2
  let g0 : Ω → ℝ := fun ω => Ii C κ X m θ s ω * f0 (Yc C θ X e s a ω, e s a ω)
  let g1 : Ω → ℝ := fun ω => Ii C κ X m θ s ω * f1 (Yc C θ X e s a ω, e s a ω)
  let g2 : Ω → ℝ := fun ω => Ii C κ X m θ s ω * f2 (Yc C θ X e s a ω, e s a ω)
  have hqv : ∀ ω, qf (Yc C θ X e s a ω, e s a ω) = 1 / max θ (Yc C θ X e s a ω) := fun ω => by
    rw [hqf]
  -- the left-hand side
  let H : Ω → ℝ := fun ω => Ii C κ X m θ s ω * (1 / max θ (Yc C θ X e (s + 1) a ω)) ^ P
  have hYm' := I.Yc_meas' θ (s + 1) hsT a
  have hqb : ∀ y, 0 ≤ 1 / max θ y ∧ 1 / max θ y ≤ 1 / θ := fun y =>
    ⟨by have := lt_of_lt_of_le hθ (le_max_left θ y); positivity,
      one_div_le_one_div_of_le hθ (le_max_left _ _)⟩
  have hHmeas : Measurable H :=
    (I.Ii_meas' m θ s hsT.le).mul ((measurable_const.div (measurable_const.max hYm')).pow_const _)
  have hHb : ∀ ω, |H ω| ≤ (1 / θ) ^ P := fun ω => by
    simp only [H]
    rw [abs_mul, abs_of_nonneg (Ii_nonneg C κ X m θ s ω),
      abs_of_nonneg (pow_nonneg (hqb _).1 _)]
    calc Ii C κ X m θ s ω * (1 / max θ (Yc C θ X e (s + 1) a ω)) ^ P ≤ 1 * (1 / θ) ^ P :=
          mul_le_mul (Ii_le_one C κ X m θ s ω) (pow_le_pow_left₀ (hqb _).1 (hqb _).2 _)
            (pow_nonneg (hqb _).1 _) zero_le_one
      _ = _ := one_mul _
  have hHint : Integrable H μ := int_of_bdd μ H hHmeas _ hHb
  have hLint : Integrable (fun ω => Ii C κ X m θ (s + 1) ω *
      (1 / max θ (Yc C θ X e (s + 1) a ω)) ^ P) μ := by
    refine int_of_bdd μ _ ((I.Ii_meas' m θ (s + 1) hsT).mul
      ((measurable_const.div (measurable_const.max hYm')).pow_const _)) ((1 / θ) ^ P) fun ω => ?_
    rw [abs_mul, abs_of_nonneg (Ii_nonneg C κ X m θ (s + 1) ω),
      abs_of_nonneg (pow_nonneg (hqb _).1 _)]
    calc Ii C κ X m θ (s + 1) ω * (1 / max θ (Yc C θ X e (s + 1) a ω)) ^ P ≤ 1 * (1 / θ) ^ P :=
          mul_le_mul (Ii_le_one C κ X m θ (s + 1) ω) (pow_le_pow_left₀ (hqb _).1 (hqb _).2 _)
            (pow_nonneg (hqb _).1 _) zero_le_one
      _ = _ := one_mul _
  have hLH : ∫ ω, Ii C κ X m θ (s + 1) ω * (1 / max θ (Yc C θ X e (s + 1) a ω)) ^ P ∂μ ≤
      ∫ ω, H ω ∂μ :=
    integral_mono hLint hHint fun ω => mul_le_mul_of_nonneg_right (I.Ii_succ_le m θ s hsT ω)
      (pow_nonneg (hqb _).1 _)
  -- pointwise Taylor
  have hpt : ∀ ω, H ω ≤ g0 ω + (g1 ω * D s a ω + g2 ω * D s a ω ^ 2) := by
    intro ω
    by_cases hω : ω ∈ Iset C κ X m θ s
    · simp only [H, g0, g1, g2, f0, f1, f2, Ii_mem C κ X m θ hω, one_mul, hqv]
      have hf := I.Iset_facts m θ s hθ hms hsT.le ω hω a
      set y := Yc C θ X e s a ω with hy
      have hy0 : 0 < y := lt_of_lt_of_le hθ hf.2.2.2.1
      have hmy : max θ y = y := max_eq_right hf.2.2.2.1
      rw [hmy]
      have hrel := I.xi_rel m θ s a hθ hms hsT hQ1 ω hω
      rw [← hy] at hrel
      have hY1 : Yc C θ X e (s + 1) a ω = y + (D s a ω - e s a ω) := Yc_succ C X θ e D I.Xs s a ω
      rw [hY1]
      have hεP : (P : ℝ) * (2 / B) ≤ 1 / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ hB (by norm_num)]; linarith
      have hT := inv_pow_taylor y (D s a ω - e s a ω) (2 / B) P (by omega) hy0 (by positivity)
        hrel hεP
      have hpos : 0 < y + (D s a ω - e s a ω) := by
        have := neg_abs_le (D s a ω - e s a ω)
        have h2B : 2 / B * y ≤ y / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ hB (by norm_num)]
          have h4B : (4 : ℝ) ≤ B := by linarith
          have := mul_le_mul_of_nonneg_left h4B hy0.le
          linarith
        linarith
      have hmax : (1 / max θ (y + (D s a ω - e s a ω))) ^ P ≤ 1 / (y + (D s a ω - e s a ω)) ^ P := by
        rw [← one_div_pow]
        have hm0 : 0 < max θ (y + (D s a ω - e s a ω)) := lt_of_lt_of_le hθ (le_max_left _ _)
        exact pow_le_pow_left₀ (by positivity) (one_div_le_one_div_of_le hpos (le_max_right _ _)) _
      have e1 : 1 / y ^ P - P * (D s a ω - e s a ω) / y ^ (P + 1) +
          (P : ℝ) * (P + 1) * (D s a ω - e s a ω) ^ 2 / y ^ (P + 2) =
          (1 / y) ^ P + P * e s a ω * (1 / y) ^ (P + 1) +
            P * (P + 1) * e s a ω ^ 2 * (1 / y) ^ (P + 2) +
          ((-(P : ℝ) * (1 / y) ^ (P + 1) - 2 * e s a ω * (P * (P + 1)) * (1 / y) ^ (P + 2)) *
              D s a ω + P * (P + 1) * (1 / y) ^ (P + 2) * D s a ω ^ 2) := by
        rw [one_div_pow, one_div_pow, one_div_pow]; ring
      linarith
    · simp only [H, g0, g1, g2, Ii_nmem C κ X m θ hω, zero_mul, mul_zero, add_zero, le_refl]
  have hstep := I.step_one s hsT a H g0 g1 g2 hHint
    (int_of_bdd μ g0 (hm0.mono hmF le_rfl) M0 hb0) hm1 M1 hb1 hM1 hm2 M2 hb2 hM2
    (fun ω => by
      simp only [g2, f2]
      have h1 := (hqb (Yc C θ X e s a ω)).1
      rw [hqv]
      exact mul_nonneg (Ii_nonneg C κ X m θ s ω) (by positivity)) hpt
  -- bound the right-hand side
  obtain ⟨Mr, hMr, hmr, hbr⟩ := I.Ii_comp m θ s a hθ hms hsT
    (fun p => (1 + P / (2 * n)) * qf p ^ P - P * Δ a * qf p ^ (P + 1)) (by fun_prop)
  have hRint : Integrable (fun ω => Ii C κ X m θ s ω * ((1 + P / (2 * n)) *
      (1 / max θ (Yc C θ X e s a ω)) ^ P - P * Δ a * (1 / max θ (Yc C θ X e s a ω)) ^ (P + 1))) μ := by
    have := int_of_bdd μ _ (hmr.mono hmF le_rfl) Mr hbr
    simp only [hqv] at this
    exact this
  have hrhs : ∀ ω, g0 ω + (g1 ω * (Δ a + e s a ω) + g2 ω * Venv d K X jstar s a ω) ≤
      Ii C κ X m θ s ω * ((1 + P / (2 * n)) * (1 / max θ (Yc C θ X e s a ω)) ^ P -
        P * Δ a * (1 / max θ (Yc C θ X e s a ω)) ^ (P + 1)) := by
    intro ω
    by_cases hω : ω ∈ Iset C κ X m θ s
    · simp only [g0, g1, g2, f0, f1, f2, Ii_mem C κ X m θ hω, one_mul, hqv]
      have hf := I.Iset_facts m θ s hθ hms hsT.le ω hω a
      set y := Yc C θ X e s a ω with hy
      have hy0 : 0 < y := lt_of_lt_of_le hθ hf.2.2.2.1
      have hmy : max θ y = y := max_eq_right hf.2.2.2.1
      rw [hmy]
      set q := 1 / y with hqdef
      have hq0 : 0 < q := by positivity
      have hyq : y * q = 1 := by rw [hqdef]; field_simp
      have hV := I.Venv_le m θ s a hθ hms hsT ω hω
      rw [← hy] at hV
      have hΔ0 := I.Δnonneg a
      have hΔ2 := I.hΔ2 a
      set ee := e s a ω
      have hW : Venv d K X jstar s a ω - ee ^ 2 - 2 * ee * Δ a ≤ 5 * β + 2 * y ^ 2 / (B * n) := by
        have : -ee ^ 2 - 2 * ee * Δ a ≤ Δ a ^ 2 := by linarith [sq_nonneg (ee + Δ a)]
        have : Δ a ^ 2 ≤ 4 := by
          have := pow_le_pow_left₀ hΔ0 hΔ2 2; norm_num at this; linarith
        linarith
      have h1 : 20 * ((P + 1) * β * n * q ^ 2) ≤ 1 := by
        have hθy : θ ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hθ.le hf.2.2.2.1 2
        have : 20 * ((P + 1) * β * n) ≤ y ^ 2 := by linarith
        have h2 := mul_le_mul_of_nonneg_right this (sq_nonneg q)
        have e2 : y ^ 2 * q ^ 2 = 1 := by rw [← mul_pow, hyq, one_pow]
        linarith
      have h2 : 5 * P * (P + 1) * β * q ^ 2 ≤ P / (4 * n) := by
        rw [le_div_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ P)
        linarith
      have h3 : 2 * P * (P + 1) / (B * n) ≤ P / (4 * n) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hB8 : 8 * ((P : ℝ) + 1) ≤ B := by linarith
        have := mul_le_mul_of_nonneg_left hB8 (by positivity : (0 : ℝ) ≤ P * n)
        linarith
      have hq2 : P * (P + 1) * q ^ 2 * (5 * β + 2 * y ^ 2 / (B * n)) ≤ P / (2 * n) := by
        have e3 : P * (P + 1) * q ^ 2 * (5 * β + 2 * y ^ 2 / (B * n)) =
            5 * P * (P + 1) * β * q ^ 2 + 2 * P * (P + 1) * (y * q) ^ 2 / (B * n) := by ring
        rw [e3, hyq, one_pow, mul_one]
        have e4 : (P : ℝ) / (4 * n) + P / (4 * n) = P / (2 * n) := by field_simp; ring
        linarith
      have hkey : P * (P + 1) * q ^ (P + 2) * (Venv d K X jstar s a ω - ee ^ 2 - 2 * ee * Δ a) ≤
          P / (2 * n) * q ^ P := by
        have hqP : 0 ≤ q ^ P := by positivity
        have e5 : P * (P + 1) * q ^ (P + 2) * (Venv d K X jstar s a ω - ee ^ 2 - 2 * ee * Δ a) =
            q ^ P * (P * (P + 1) * q ^ 2 * (Venv d K X jstar s a ω - ee ^ 2 - 2 * ee * Δ a)) := by ring
        rw [e5]
        have h4 : P * (P + 1) * q ^ 2 * (Venv d K X jstar s a ω - ee ^ 2 - 2 * ee * Δ a) ≤
            P * (P + 1) * q ^ 2 * (5 * β + 2 * y ^ 2 / (B * n)) :=
          mul_le_mul_of_nonneg_left hW (by positivity)
        have := mul_le_mul_of_nonneg_left (h4.trans hq2) hqP
        linarith
      have e6 : q ^ P + P * ee * q ^ (P + 1) + P * (P + 1) * ee ^ 2 * q ^ (P + 2) +
          ((-(P : ℝ) * q ^ (P + 1) - 2 * ee * (P * (P + 1)) * q ^ (P + 2)) * (Δ a + ee) +
            P * (P + 1) * q ^ (P + 2) * Venv d K X jstar s a ω) =
          q ^ P - P * Δ a * q ^ (P + 1) +
            P * (P + 1) * q ^ (P + 2) * (Venv d K X jstar s a ω - ee ^ 2 - 2 * ee * Δ a) := by ring
      rw [e6]
      have e7 : (1 + P / (2 * n)) * q ^ P - P * Δ a * q ^ (P + 1) =
          q ^ P - P * Δ a * q ^ (P + 1) + P / (2 * n) * q ^ P := by ring
      rw [e7]
      linarith
    · simp only [g0, g1, g2, Ii_nmem C κ X m θ hω, zero_mul, add_zero, le_refl]
  have hEint : Integrable (fun ω => Δ a + e s a ω) μ :=
    int_of_bdd μ _ (measurable_const.add (((I.κm s hsT).2 a).mono hmF le_rfl)) 2 fun ω =>
      ((I.κb s hsT ω).2.2 a).2
  have hVint : Integrable (Venv d K X jstar s a) μ :=
    int_of_bdd μ _ (I.Vmeas s hsT.le a) _ fun ω => I.Venv_bound s hsT.le ω a
  have hLint2 : Integrable (fun ω => g0 ω + (g1 ω * (Δ a + e s a ω) + g2 ω * Venv d K X jstar s a ω)) μ :=
    (int_of_bdd μ g0 (hm0.mono hmF le_rfl) M0 hb0).add
      ((hEint.bdd_mul (hm1.mono hmF le_rfl).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hb1 ω)).add
       (hVint.bdd_mul (hm2.mono hmF le_rfl).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hb2 ω)))
  exact hLH.trans (hstep.trans (integral_mono hLint2 hRint hrhs))

end C37

/-! ===== module Seq ===== -/

/-! # Scalar inequalities: weighted AM–GM tangents, Bernoulli bounds, power tails -/

namespace C37

open Finset

/-- tangent of `x ↦ x^{P+1}`: `(P+1) w x^P ≤ P x^{P+1} + w^{P+1}` -/
lemma amgm_inv (P : ℕ) (x w : ℝ) (hx : 0 ≤ x) (hw : 0 ≤ w) :
    ((P : ℝ) + 1) * w * x ^ P ≤ P * x ^ (P + 1) + w ^ (P + 1) := by
  rcases eq_or_lt_of_le hx with h0 | hpos
  · subst h0
    rcases Nat.eq_zero_or_pos P with hP | hP
    · subst hP; simp
    · rw [zero_pow (by omega), zero_pow (by omega)]; simp; positivity
  · set u := w / x with hu
    have hu0 : 0 ≤ u := by positivity
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ u - 1 by linarith) (P + 1)
    have e1 : w = u * x := by rw [hu]; field_simp
    rw [e1]
    have hxP : 0 < x ^ (P + 1) := by positivity
    have e2 : (u * x) ^ (P + 1) = (1 + (u - 1)) ^ (P + 1) * x ^ (P + 1) := by
      rw [mul_pow]; ring_nf
    rw [e2]
    have e3 : ((P : ℝ) + 1) * (u * x) * x ^ P = ((P : ℝ) + 1) * u * x ^ (P + 1) := by ring
    rw [e3]
    have := mul_le_mul_of_nonneg_right hb hxP.le
    push_cast at this
    linarith

/-- tangent of `y ↦ y^P`: `P c y^{P−1} ≤ (P−1) y^P + c^P` -/
lemma amgm_pos (P : ℕ) (hP : 2 ≤ P) (y c : ℝ) (hy : 0 ≤ y) (hc : 0 ≤ c) :
    (P : ℝ) * c * y ^ (P - 1) ≤ ((P : ℝ) - 1) * y ^ P + c ^ P := by
  rcases eq_or_lt_of_le hy with h0 | hpos
  · subst h0
    rw [zero_pow (by omega), zero_pow (by omega)]; simp; positivity
  · set u := c / y with hu
    have hu0 : 0 ≤ u := by positivity
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ u - 1 by linarith) P
    have e1 : c = u * y := by rw [hu]; field_simp
    rw [e1]
    have hyP : 0 < y ^ P := by positivity
    have e2 : (u * y) ^ P = (1 + (u - 1)) ^ P * y ^ P := by rw [mul_pow]; ring_nf
    have e3 : (P : ℝ) * (u * y) * y ^ (P - 1) = P * u * y ^ P := by
      have : y ^ P = y * y ^ (P - 1) := by rw [← pow_succ']; congr 1; omega
      rw [this]; ring
    rw [e2, e3]
    have := mul_le_mul_of_nonneg_right hb hyP.le
    linarith

/-- Bernoulli for negative powers: `1 − P h ≤ (1 + h)^{−P}` -/
lemma inv_bern (P : ℕ) (h : ℝ) (hh : -1 < h) : 1 - P * h ≤ 1 / (1 + h) ^ P := by
  have h1 : 0 < 1 + h := by linarith
  set g := -h / (1 + h) with hg
  have hg2 : (-2 : ℝ) ≤ g := by
    rw [hg, le_div_iff₀ h1]; linarith
  have hb := one_add_mul_le_pow hg2 P
  have e : 1 / (1 + h) ^ P = (1 + g) ^ P := by
    rw [hg, one_div, ← inv_pow]; congr 1; field_simp; ring
  rw [e]
  have hgh : -h ≤ g := by
    rw [hg, le_div_iff₀ h1]; linarith [sq_nonneg h]
  have hP : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  nlinarith

/-- `1 + p x/(1+x) ≤ (1 + x)^p` for `p ≥ 0`, `x ≥ 0` -/
lemma rpow_lower (p x : ℝ) (hp : 0 ≤ p) (hx : 0 ≤ x) : 1 + p * x / (1 + x) ≤ (1 + x) ^ p := by
  have h1 : 0 < 1 + x := by linarith
  rcases le_or_gt 1 p with hp1 | hp1
  · have hb := one_add_mul_self_le_rpow_one_add (show (-1 : ℝ) ≤ x by linarith) hp1
    have : p * x / (1 + x) ≤ p * x := by
      rw [div_le_iff₀ h1]; nlinarith [mul_nonneg hp hx]
    linarith
  · set y := 1 / (1 + x) with hy
    have hy0 : 0 < y := by positivity
    have hy1 : y ≤ 1 := by rw [hy, div_le_one h1]; linarith
    have hb := rpow_one_add_le_one_add_mul_self (show (-1 : ℝ) ≤ y - 1 by linarith) hp hp1.le
    have e1 : (1 + x) ^ p = 1 / y ^ p := by
      rw [hy, Real.div_rpow zero_le_one h1.le, Real.one_rpow, one_div_one_div]
    rw [e1]
    have hyp : 0 < y ^ p := Real.rpow_pos_of_pos hy0 p
    have e2 : 1 + (y - 1) = y := by ring
    rw [e2] at hb
    have hv : p * x / (1 + x) = p * (1 - y) := by rw [hy]; field_simp; ring
    rw [hv]
    have hv1 : p * (1 - y) < 1 := by linarith
    rw [le_div_iff₀ hyp]
    have : 0 ≤ p * (1 - y) := mul_nonneg hp (by linarith)
    nlinarith

/-- the tangent of `x ↦ x^{1−s}` at `x`: `(s−1) x^{−s} ≤ (x−1)^{1−s} − x^{1−s}` for `x ≥ 2` -/
lemma rpow_tangent (s x : ℝ) (hs : 1 < s) (hx : 2 ≤ x) :
    (s - 1) * x ^ (-s) ≤ (x - 1) ^ (1 - s) - x ^ (1 - s) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hl := rpow_lower (s - 1) (1 / (x - 1)) (by linarith) (by positivity)
  have e1 : (1 + 1 / (x - 1)) = x / (x - 1) := by field_simp; ring
  have e2 : (s - 1) * (1 / (x - 1)) / (1 + 1 / (x - 1)) = (s - 1) / x := by
    rw [e1]; field_simp
  rw [e2, e1] at hl
  -- (x/(x−1))^{s−1} = (x−1)^{1−s} x^{s−1}
  have e3 : (x / (x - 1)) ^ (s - 1) = (x - 1) ^ (1 - s) * x ^ (s - 1) := by
    rw [Real.div_rpow hx0.le hx1.le, div_eq_mul_inv, ← Real.rpow_neg hx1.le]
    rw [show -(s - 1) = 1 - s by ring]; ring
  rw [e3] at hl
  have hxs : 0 < x ^ (s - 1) := Real.rpow_pos_of_pos hx0 _
  have e4 : x ^ (1 - s) * x ^ (s - 1) = 1 := by
    rw [← Real.rpow_add hx0]; norm_num
  have e5 : x ^ (-s) * x ^ (s - 1) = 1 / x := by
    rw [← Real.rpow_add hx0, show -s + (s - 1) = -1 by ring, Real.rpow_neg_one, one_div]
  -- multiply the target by `x^{s−1} > 0`
  have key : ((s - 1) * x ^ (-s)) * x ^ (s - 1) ≤ ((x - 1) ^ (1 - s) - x ^ (1 - s)) * x ^ (s - 1) := by
    have : ((s - 1) * x ^ (-s)) * x ^ (s - 1) = (s - 1) / x := by
      rw [mul_assoc, e5]; ring
    rw [this, sub_mul, e4]
    linarith
  exact le_of_mul_le_mul_right key hxs

/-- power tail (Lemma I.8 type): `Σ_{i<L} (N+i)^{−s} ≤ N^{1−s} · s/(s−1)` -/
lemma tail_sum (s : ℝ) (hs : 1 < s) (N : ℕ) (hN : 1 ≤ N) (L : ℕ) :
    ∑ i ∈ range L, ((N : ℝ) + i) ^ (-s) ≤ (N : ℝ) ^ (1 - s) * (s / (s - 1)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  -- telescoping part
  have htel : ∀ L, ∑ i ∈ range L, ((N : ℝ) + 1 + i) ^ (-s) ≤
      ((N : ℝ) ^ (1 - s) - ((N : ℝ) + L) ^ (1 - s)) / (s - 1) := by
    intro L
    induction L with
    | zero => simp
    | succ L ih =>
      rw [sum_range_succ]
      have ht := rpow_tangent s ((N : ℝ) + L + 1) hs (by
        have : (0 : ℝ) ≤ L := Nat.cast_nonneg L
        linarith)
      have e1 : (N : ℝ) + L + 1 - 1 = N + L := by ring
      rw [e1] at ht
      have e2 : (N : ℝ) + 1 + L = N + L + 1 := by ring
      rw [e2]
      push_cast
      have e3 : (N : ℝ) + (L + 1) = N + L + 1 := by ring
      rw [e3]
      have h4 : ((N : ℝ) + L + 1) ^ (-s) ≤ (((N : ℝ) + L) ^ (1 - s) - ((N : ℝ) + L + 1) ^ (1 - s)) / (s - 1) := by
        rw [le_div_iff₀ (by linarith)]; linarith [ht]
      calc ∑ x ∈ range L, ((N : ℝ) + 1 + x) ^ (-s) + ((N : ℝ) + L + 1) ^ (-s) ≤
          ((N : ℝ) ^ (1 - s) - ((N : ℝ) + L) ^ (1 - s)) / (s - 1) +
            (((N : ℝ) + L) ^ (1 - s) - ((N : ℝ) + L + 1) ^ (1 - s)) / (s - 1) := add_le_add ih h4
        _ = _ := by ring
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL; simp; positivity
  · obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    rw [sum_range_succ']
    have h1 := htel L'
    have e : ∀ i : ℕ, ((N : ℝ) + ((i + 1 : ℕ) : ℝ)) = N + 1 + i := fun i => by push_cast; ring
    simp only [e]
    simp only [Nat.cast_zero, add_zero]
    have h2 : ((N : ℝ) ^ (1 - s) - ((N : ℝ) + L') ^ (1 - s)) / (s - 1) ≤ (N : ℝ) ^ (1 - s) / (s - 1) := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      have : 0 ≤ ((N : ℝ) + L') ^ (1 - s) := by positivity
      linarith
    have h3 : (N : ℝ) ^ (-s) ≤ (N : ℝ) ^ (1 - s) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hs1 : (s - 1) ≠ 0 := ne_of_gt (by linarith)
    have e4 : (N : ℝ) ^ (1 - s) * (s / (s - 1)) = (N : ℝ) ^ (1 - s) + (N : ℝ) ^ (1 - s) / (s - 1) := by
      field_simp; ring
    rw [e4]
    linarith

end C37

namespace C37

/-- binomial lower bound `x^P + P x^{P−1} y ≤ (x + y)^P` -/
lemma add_pow_ge (P : ℕ) (hP : 1 ≤ P) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ P + P * x ^ (P - 1) * y ≤ (x + y) ^ P := by
  rcases eq_or_lt_of_le hx with h0 | hpos
  · subst h0
    rcases Nat.lt_or_ge P 2 with h1 | h2
    · have : P = 1 := by omega
      subst this; simp
    · rw [zero_pow (by omega), zero_pow (by omega)]; simp; positivity
  · have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ y / x by
      have : 0 ≤ y / x := by positivity
      linarith) P
    have e1 : (x + y) ^ P = x ^ P * (1 + y / x) ^ P := by
      rw [← mul_pow]; congr 1; field_simp
    have e2 : x ^ P = x * x ^ (P - 1) := by rw [← pow_succ']; congr 1; omega
    rw [e1]
    have hxP : 0 < x ^ P := by positivity
    have := mul_le_mul_of_nonneg_left hb hxP.le
    have e3 : x ^ P * (1 + P * (y / x)) = x ^ P + P * x ^ (P - 1) * y := by
      rw [e2]; field_simp
    linarith

end C37

/-! ===== module LocalMom ===== -/

/-! # Inverse and positive local moments on a window (v1 Lemmas C.30, C.14) -/

namespace C37

open MeasureTheory Finset

lemma kap0_nonneg (K : ℕ) (hK : 1 ≤ K) : 0 ≤ kap0 K := by
  unfold kap0
  have : (512 : ℝ) ≤ Pord K := by exact_mod_cast Pord_ge K hK
  have := Bc_pos K hK
  apply div_nonneg _ this.le; linarith

lemma kap0_le (K : ℕ) (hK : 1 ≤ K) : kap0 K ≤ 1 / 1024 := by
  unfold kap0
  have hP : (512 : ℝ) ≤ Pord K := by exact_mod_cast Pord_ge K hK
  have hB := Bc_ge K hK
  have hB0 := Bc_pos K hK
  rw [div_le_div_iff₀ hB0 (by norm_num)]
  linarith

variable {d K : ℕ} {jstar : Fin K} {Δ : Fin K → ℝ} {Δ₀ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω} {T : ℕ} {C : ℝ} {X D e : ℕ → Fin K → Ω → ℝ}
  {κ : ℕ → Ω → ℝ}

lemma Iface.inv_int [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (m : ℕ)
    (θ : ℝ) (s : ℕ) (a : Fin K) (hθ : 0 < θ) (hsT : s ≤ T) (j : ℕ) :
    Integrable (fun ω => Ii C κ X m θ s ω * (1 / max θ (Yc C θ X e s a ω)) ^ j) μ := by
  have hqb : ∀ y, 0 ≤ 1 / max θ y ∧ 1 / max θ y ≤ 1 / θ := fun y =>
    ⟨by have := lt_of_lt_of_le hθ (le_max_left θ y); positivity,
      one_div_le_one_div_of_le hθ (le_max_left _ _)⟩
  refine int_of_bdd μ _ ((I.Ii_meas' m θ s hsT).mul ((measurable_const.div
    (measurable_const.max (I.Yc_meas' θ s hsT a))).pow_const _)) ((1 / θ) ^ j) fun ω => ?_
  rw [abs_mul, abs_of_nonneg (Ii_nonneg C κ X m θ s ω), abs_of_nonneg (pow_nonneg (hqb _).1 _)]
  calc Ii C κ X m θ s ω * (1 / max θ (Yc C θ X e s a ω)) ^ j ≤ 1 * (1 / θ) ^ j :=
        mul_le_mul (Ii_le_one C κ X m θ s ω) (pow_le_pow_left₀ (hqb _).1 (hqb _).2 _)
          (pow_nonneg (hqb _).1 _) zero_le_one
    _ = _ := one_mul _

lemma Iface.pos_int [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (m : ℕ)
    (θ : ℝ) (s : ℕ) (a : Fin K) (hθ : 0 < θ) (hms : m ≤ s) (hsT : s ≤ T) (j : ℕ) :
    Integrable (fun ω => Ii C κ X m θ s ω * Yc C θ X e s a ω ^ j) μ := by
  refine int_of_bdd μ _ ((I.Ii_meas' m θ s hsT).mul ((I.Yc_meas' θ s hsT a).pow_const _))
    ((renv d K s + 4 * C + 2 * θ) ^ j) fun ω => ?_
  by_cases hω : ω ∈ Iset C κ X m θ s
  · rw [Ii_mem C κ X m θ hω, one_mul, abs_pow]
    have hf := I.Iset_facts m θ s hθ hms hsT ω hω a
    exact pow_le_pow_left₀ (abs_nonneg _) (by
      rw [abs_of_nonneg (by linarith [hf.2.2.2.1])]; exact hf.2.2.2.2.2) _
  · rw [Ii_nmem C κ X m θ hω, zero_mul, abs_zero]
    have := renv_nonneg d K I.hK I.hd s; have := I.hC; positivity

set_option maxHeartbeats 1000000 in
/-- Lemma C.30: `E[I_t Y_t^{−P}] ≤ (4/(nΔ))^P` -/
lemma Iface.inv_moment [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ)
    (m : ℕ) (θ : ℝ) (t : ℕ) (a : Fin K) (hθ : 0 < θ) (ha : a ≠ jstar) (hmt : m ≤ t)
    (htT : t ≤ T) (hmhalf : 2 * ((m : ℝ) + 1) ≤ (t : ℝ) + 1)
    (hθP : 2 * ((Pord K : ℝ) + 1) ≤ θ) (hmP : (Pord K : ℝ) + 1 ≤ 2 * ((m : ℝ) + 1))
    (hQ1 : ∀ s, m ≤ s → s < t → 3 * IAFTRL.Bc K * IAFTRL.beta d K (s + 1) ≤ θ)
    (hQ2 : ∀ s, m ≤ s → s < t →
      20 * ((Pord K : ℝ) + 1) * IAFTRL.beta d K (s + 1) * ((s : ℝ) + 1) ≤ θ ^ 2) :
    ∫ ω, Ii C κ X m θ t ω * (1 / max θ (Yc C θ X e t a ω)) ^ Pord K ∂μ ≤
      (4 / (((t : ℝ) + 1) * Δ a)) ^ Pord K := by
  have hK := I.hK
  have hPn := Pord_ge K hK
  set P := Pord K with hPdef
  have hPr : (512 : ℝ) ≤ P := by exact_mod_cast hPn
  set Δa := Δ a with hΔa
  have hΔ0 : 0 < Δa := lt_of_lt_of_le I.hΔ₀ (I.hΔge a ha)
  have hΔ2 : Δa ≤ 2 := I.hΔ2 a
  let u : ℕ → ℝ := fun s => ∫ ω, Ii C κ X m θ s ω * (1 / max θ (Yc C θ X e s a ω)) ^ P ∂μ
  let v : ℕ → ℝ := fun s => ∫ ω, Ii C κ X m θ s ω * (1 / max θ (Yc C θ X e s a ω)) ^ (P + 1) ∂μ
  have hqb : ∀ y, 0 ≤ 1 / max θ y := fun y => by
    have := lt_of_lt_of_le hθ (le_max_left θ y); positivity
  have claim : ∀ k, m + k ≤ t → ∃ c, ((P : ℝ) + 1) * Δa ≤ c ∧
      Δa * ((((m + k : ℕ) : ℝ) + 1) ^ 2 - ((m : ℝ) + 1) ^ 2) / 2 ≤ (((m + k : ℕ) : ℝ) + 1) * c ∧
      u (m + k) ≤ 1 / c ^ P := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨θ, by nlinarith, by simp; positivity, ?_⟩
      simp only [add_zero, u]
      calc ∫ ω, Ii C κ X m θ m ω * (1 / max θ (Yc C θ X e m a ω)) ^ P ∂μ ≤ ∫ _ω, (1 / θ) ^ P ∂μ :=
            integral_mono (I.inv_int m θ m a hθ (by omega) P) (integrable_const _) fun ω => by
              calc Ii C κ X m θ m ω * (1 / max θ (Yc C θ X e m a ω)) ^ P ≤ 1 * (1 / θ) ^ P :=
                    mul_le_mul (Ii_le_one C κ X m θ m ω) (pow_le_pow_left₀ (hqb _)
                      (one_div_le_one_div_of_le hθ (le_max_left _ _)) _) (pow_nonneg (hqb _) _)
                      zero_le_one
                _ = _ := one_mul _
        _ = 1 / θ ^ P := by simp [one_div_pow]
    | succ k ih =>
      intro hk
      obtain ⟨c, hc1, hc2, hc3⟩ := ih (by omega)
      set s := m + k with hs
      have hsT : s < T := by omega
      set n : ℝ := (s : ℝ) + 1 with hn
      have hn1 : (1 : ℝ) ≤ n := by simp only [n]; linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
      have hnpos : 0 < n := by linarith
      have hnne : n ≠ 0 := ne_of_gt hnpos
      have hnP : (P : ℝ) + 1 ≤ 2 * n := by
        have : (m : ℝ) ≤ s := by exact_mod_cast (show m ≤ s by omega)
        linarith
      have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hc1
      -- the step
      have hstep := I.inv_step m θ s a hθ (by omega) hsT (hQ1 s (by omega) (by omega))
        (hQ2 s (by omega) (by omega))
      have hsplit : ∫ ω, Ii C κ X m θ s ω * ((1 + P / (2 * ((s : ℝ) + 1))) *
          (1 / max θ (Yc C θ X e s a ω)) ^ P - P * Δa * (1 / max θ (Yc C θ X e s a ω)) ^ (P + 1)) ∂μ =
          (1 + P / (2 * n)) * u s - P * Δa * v s := by
        have e : (fun ω => Ii C κ X m θ s ω * ((1 + P / (2 * ((s : ℝ) + 1))) *
            (1 / max θ (Yc C θ X e s a ω)) ^ P - P * Δa * (1 / max θ (Yc C θ X e s a ω)) ^ (P + 1))) =
            fun ω => (1 + P / (2 * n)) * (Ii C κ X m θ s ω * (1 / max θ (Yc C θ X e s a ω)) ^ P) -
              (P * Δa) * (Ii C κ X m θ s ω * (1 / max θ (Yc C θ X e s a ω)) ^ (P + 1)) := by
          funext ω; ring
        rw [e, integral_sub ((I.inv_int m θ s a hθ hsT.le P).const_mul _)
          ((I.inv_int m θ s a hθ hsT.le (P + 1)).const_mul _), integral_const_mul, integral_const_mul]
      -- tangent
      have htan : ((P : ℝ) + 1) * (1 / c) * u s ≤ P * v s + (1 / c) ^ (P + 1) := by
        have hpt : ∀ ω, ((P : ℝ) + 1) * (1 / c) * (Ii C κ X m θ s ω * (1 / max θ (Yc C θ X e s a ω)) ^ P) ≤
            P * (Ii C κ X m θ s ω * (1 / max θ (Yc C θ X e s a ω)) ^ (P + 1)) + (1 / c) ^ (P + 1) := by
          intro ω
          have hA := amgm_inv P (1 / max θ (Yc C θ X e s a ω)) (1 / c) (hqb _) (by positivity)
          have hI0 := Ii_nonneg C κ X m θ s ω
          have hI1 := Ii_le_one C κ X m θ s ω
          have h1 := mul_le_mul_of_nonneg_left hA hI0
          have h2 : Ii C κ X m θ s ω * (1 / c) ^ (P + 1) ≤ (1 / c) ^ (P + 1) :=
            mul_le_of_le_one_left (by positivity) hI1
          linarith
        have i2 : Integrable (fun ω => (P : ℝ) * (Ii C κ X m θ s ω *
            (1 / max θ (Yc C θ X e s a ω)) ^ (P + 1)) + (1 / c) ^ (P + 1)) μ :=
          ((I.inv_int m θ s a hθ hsT.le (P + 1)).const_mul (P : ℝ)).add (integrable_const _)
        have hint := integral_mono (((I.inv_int m θ s a hθ hsT.le P).const_mul (((P : ℝ) + 1) * (1 / c))))
          i2 hpt
        rw [integral_const_mul, integral_add ((I.inv_int m θ s a hθ hsT.le (P + 1)).const_mul (P : ℝ))
          (integrable_const _), integral_const_mul, integral_const] at hint
        show ((P : ℝ) + 1) * (1 / c) * (∫ ω, Ii C κ X m θ s ω * (1 / max θ (Yc C θ X e s a ω)) ^ P ∂μ) ≤
          P * (∫ ω, Ii C κ X m θ s ω * (1 / max θ (Yc C θ X e s a ω)) ^ (P + 1) ∂μ) + (1 / c) ^ (P + 1)
        simpa using hint
      set c' := (1 - 1 / (2 * n)) * c + Δa with hc'
      refine ⟨c', ?_, ?_, ?_⟩
      · -- `(P+1) Δ ≤ c'`
        have h1 : (1 - 1 / (2 * n)) * (((P : ℝ) + 1) * Δa) ≤ (1 - 1 / (2 * n)) * c :=
          mul_le_mul_of_nonneg_left hc1 (by
            have : 1 / (2 * n) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
            linarith)
        have h2 : ((P : ℝ) + 1) * Δa / (2 * n) ≤ Δa := by
          rw [div_le_iff₀ (by positivity)]
          have := mul_le_mul_of_nonneg_left hnP hΔ0.le
          linarith
        have e : (1 - 1 / (2 * n)) * (((P : ℝ) + 1) * Δa) = ((P : ℝ) + 1) * Δa - ((P : ℝ) + 1) * Δa / (2 * n) := by
          ring
        linarith
      · -- the linear lower bound
        have hcast : (((m + (k + 1) : ℕ) : ℝ) + 1) = n + 1 := by
          simp only [n, hs]; push_cast; ring
        have hcast0 : (((m + k : ℕ) : ℝ) + 1) = n := by simp only [n, hs]
        rw [hcast]
        have h1 : n * c + Δa * (n + 1) ≤ (n + 1) * c' := by
          rw [hc']
          have e : (n + 1) * ((1 - 1 / (2 * n)) * c + Δa) = n * c + Δa * (n + 1) + c * (1 / 2 - 1 / (2 * n)) := by
            field_simp; ring
          rw [e]
          have : 0 ≤ c * (1 / 2 - 1 / (2 * n)) := mul_nonneg hc0.le (by
            rw [sub_nonneg, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith)
          linarith
        linarith
      · -- the inverse-moment bound
        have hcoef : 0 ≤ 1 + P / (2 * n) - ((P : ℝ) + 1) * Δa / c := by
          have : ((P : ℝ) + 1) * Δa / c ≤ 1 := by rw [div_le_one hc0]; exact hc1
          have : 0 ≤ (P : ℝ) / (2 * n) := by positivity
          linarith
        have hu1 : u (s + 1) ≤ (1 + P / (2 * n) - ((P : ℝ) + 1) * Δa / c) * u s + Δa * (1 / c) ^ (P + 1) := by
          have hv : P * Δa * v s ≥ Δa * (((P : ℝ) + 1) * (1 / c) * u s - (1 / c) ^ (P + 1)) := by
            have := mul_le_mul_of_nonneg_left htan hΔ0.le
            linarith
          have hh := hstep.trans_eq hsplit
          have e : (1 + P / (2 * n) - ((P : ℝ) + 1) * Δa / c) * u s =
              (1 + P / (2 * n)) * u s - Δa * (((P : ℝ) + 1) * (1 / c) * u s) := by field_simp
          simp only [u] at hh ⊢
          rw [e]
          linarith
        have hu2 : u (s + 1) ≤ (1 + P / (2 * n) - P * Δa / c) * (1 / c ^ P) := by
          have h1 := mul_le_mul_of_nonneg_left hc3 hcoef
          have e : (1 + P / (2 * n) - ((P : ℝ) + 1) * Δa / c) * (1 / c ^ P) + Δa * (1 / c) ^ (P + 1) =
              (1 + P / (2 * n) - P * Δa / c) * (1 / c ^ P) := by
            rw [one_div_pow, pow_succ]; field_simp; ring
          linarith
        have hh : -1 < -1 / (2 * n) + Δa / c := by
          have : -1 / (2 * n) ≥ -1 / 2 := by
            rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
          have : 0 ≤ Δa / c := by positivity
          linarith
        have hb := inv_bern P (-1 / (2 * n) + Δa / c) hh
        have hcc : c' = c * (1 + (-1 / (2 * n) + Δa / c)) := by rw [hc']; field_simp; ring
        have hfin : (1 + P / (2 * n) - P * Δa / c) * (1 / c ^ P) ≤ 1 / c' ^ P := by
          rw [hcc, mul_pow, ← one_div_mul_one_div, mul_comm (1 + (P : ℝ) / (2 * n) - P * Δa / c)]
          have e : 1 - (P : ℝ) * (-1 / (2 * n) + Δa / c) = 1 + P / (2 * n) - P * Δa / c := by ring
          rw [← e]
          exact mul_le_mul_of_nonneg_left hb (by positivity)
        exact hu2.trans hfin
  obtain ⟨c, hc1, hc2, hc3⟩ := claim (t - m) (by omega)
  have ht' : m + (t - m) = t := by omega
  rw [ht'] at hc2 hc3
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hc1
  have htn : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have hc4 : ((t : ℝ) + 1) * Δa / 4 ≤ c := by
    have h0 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
    have hm2 : ((m : ℝ) + 1) ^ 2 ≤ ((t : ℝ) + 1) ^ 2 / 4 := by
      have := pow_le_pow_left₀ h0 (show (m : ℝ) + 1 ≤ ((t : ℝ) + 1) / 2 by linarith) 2
      have e : (((t : ℝ) + 1) / 2) ^ 2 = ((t : ℝ) + 1) ^ 2 / 4 := by ring
      linarith
    have h4 : Δa * ((m : ℝ) + 1) ^ 2 ≤ Δa * (((t : ℝ) + 1) ^ 2 / 4) :=
      mul_le_mul_of_nonneg_left hm2 hΔ0.le
    have h5 : 0 ≤ Δa * ((t : ℝ) + 1) ^ 2 := by positivity
    have h6 : ((t : ℝ) + 1) * (((t : ℝ) + 1) * Δa / 4) ≤ ((t : ℝ) + 1) * c := by linarith
    exact le_of_mul_le_mul_left h6 htn
  calc u t ≤ 1 / c ^ P := hc3
    _ ≤ 1 / (((t : ℝ) + 1) * Δa / 4) ^ P :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hc4 _)
    _ = (4 / (((t : ℝ) + 1) * Δa)) ^ P := by rw [one_div, ← inv_pow, inv_div]

end C37

namespace IAFTRL

open MeasureTheory

/-- **Inverse local moments.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*,
arXiv:2611.01299v1, Lemmas C.29–C.30 ((C.198), (C.201)), for the abstract interface `C37.Iface`:
on the surviving window `I_s` (budget not exceeded, `F_j ≤ θ^P` for `m ≤ j ≤ s`) the compensated
process `Y_t = X_{t,a} − Σ_{i<t} e_{i,a} + 2C + 2θ` satisfies `E[I_t Y_t^{−P}] ≤ (4/(nΔ(a)))^P`,
provided `2(m+1) ≤ n = t + 1`, `θ ≥ 2(P+1)`, `P + 1 ≤ 2(m+1)` and the local thresholds
`3Bβ_{s+1} ≤ θ`, `20(P+1)β_{s+1}(s+1) ≤ θ²` hold on the window. -/
theorem _root_.solution {d K : ℕ} {jstar : Fin K} {Δ : Fin K → ℝ} {Δ₀ : ℝ} {Ω : Type*}
    [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {F : ℕ → MeasurableSpace Ω}
    {T : ℕ} {C : ℝ} {X D e : ℕ → Fin K → Ω → ℝ} {κ : ℕ → Ω → ℝ}
    (I : C37.Iface d K jstar Δ Δ₀ μ F T C X D e κ) (m : ℕ) (θ : ℝ) (t : ℕ) (a : Fin K)
    (hθ : 0 < θ) (ha : a ≠ jstar) (hmt : m ≤ t) (htT : t ≤ T)
    (hmhalf : 2 * ((m : ℝ) + 1) ≤ (t : ℝ) + 1)
    (hθP : 2 * ((C37.Pord K : ℝ) + 1) ≤ θ) (hmP : (C37.Pord K : ℝ) + 1 ≤ 2 * ((m : ℝ) + 1))
    (hQ1 : ∀ s, m ≤ s → s < t → 3 * Bc K * beta d K (s + 1) ≤ θ)
    (hQ2 : ∀ s, m ≤ s → s < t →
      20 * ((C37.Pord K : ℝ) + 1) * beta d K (s + 1) * ((s : ℝ) + 1) ≤ θ ^ 2) :
    ∫ ω, C37.Ii C κ X m θ t ω * (1 / max θ (C37.Yc C θ X e t a ω)) ^ C37.Pord K ∂μ ≤
      (4 / (((t : ℝ) + 1) * Δ a)) ^ C37.Pord K := by
  exact I.inv_moment m θ t a hθ ha hmt htT hmhalf hθP hmP hQ1 hQ2

end IAFTRL

