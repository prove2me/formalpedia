-- Prove2me | solution 1 for IAFTRL.lemma_C_37_scalar_moments
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T15:55:33.480128+00:00
-- url     : https://prove2.me/submissions/e9c9d1a0-35d9-415b-b66b-1e33df6b2829

import Mathlib
import Definitions.Def_IAFTRL_beta
import Definitions.Def_IAFTRL_Bc
import Definitions.Def_IAFTRL_cR
import Definitions.Def_IAFTRL_C37_scalar
import Theorems.Thm_IAFTRL_lemma_C_37_abs_moments
import Theorems.Thm_IAFTRL_lemma_C_37_window
import Theorems.Thm_IAFTRL_lemma_C_37_inv_moments
import Theorems.Thm_IAFTRL_lemma_C_37_pos_moments

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

/-- after the burn-in `n^{P/4} ≥ H_G`: `E[G_t] ≤ ((16k + 1) n)^P` (C.235) -/
lemma Iface.abs_root [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ)
    (ht : t ≤ T) (hburn : HG d K ≤ ((t : ℝ) + 1) ^ ((Pord K : ℝ) / 4)) :
    ∫ ω, Gsum X t ω ∂μ ≤ ((16 * kK K + 1) * ((t : ℝ) + 1)) ^ Pord K :=
  IAFTRL.lemma_C_37_abs_moments I t ht hburn

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

/-- Lemma C.28 (single plateau window): `L · P(∃ j ∈ [m, t], F_j > L) ≤ H_0 n^ν + (64 n_0)^P (n/n_0)^q` -/
lemma Iface.window [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ)
    (t0 m t : ℕ) (L : ℝ) (hL : 0 ≤ L) (ht0m : t0 ≤ m) (hmt : m ≤ t) (htT : t ≤ T)
    (hburn : HG d K ≤ ((t0 : ℝ) + 1) ^ ((Pord K : ℝ) / 4)) (hCn : C ≤ (t0 : ℝ) + 1) :
    L * ∫ ω, (1 - sv C κ X m L (t + 1) ω) ∂μ ≤ HN d K * ((t : ℝ) + 1) ^ nuP K +
      (64 * ((t0 : ℝ) + 1)) ^ Pord K * (((t : ℝ) + 1) / ((t0 : ℝ) + 1)) ^ qN K :=
  IAFTRL.lemma_C_37_window I t0 m t L hL ht0m hmt htT hburn hCn

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
      (4 / (((t : ℝ) + 1) * Δ a)) ^ Pord K :=
  IAFTRL.lemma_C_37_inv_moments I m θ t a hθ ha hmt htT hmhalf hθP hmP hQ1 hQ2

set_option maxHeartbeats 1000000 in
/-- Lemma C.14: `E[I_t Y_t^P] ≤ (A n/(1−κ_0) + w_0 (n/n_m)^{2κ_0})^P` -/
lemma Iface.pos_moment [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ)
    (m : ℕ) (θ : ℝ) (t : ℕ) (a : Fin K) (hθ : 0 < θ) (hmt : m ≤ t) (htT : t ≤ T)
    (hQ1 : ∀ s, m ≤ s → s < t → 3 * IAFTRL.Bc K * IAFTRL.beta d K (s + 1) ≤ θ)
    (A : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ s, m ≤ s → s < t → Δ a + 5 * ((Pord K : ℝ) - 1) * IAFTRL.beta d K (s + 1) / θ ≤ A)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hW0 : ∫ ω, Ii C κ X m θ m ω * Yc C θ X e m a ω ^ Pord K ∂μ ≤ w0 ^ Pord K) :
    ∫ ω, Ii C κ X m θ t ω * Yc C θ X e t a ω ^ Pord K ∂μ ≤
      (A * ((t : ℝ) + 1) / (1 - kap0 K) + w0 * (((t : ℝ) + 1) / ((m : ℝ) + 1)) ^ (2 * kap0 K)) ^
        Pord K :=
  IAFTRL.lemma_C_37_pos_moments I m θ t a hθ hmt htT hQ1 A hA0 hA w0 hw0 hW0

end C37

/-! ===== module Sums ===== -/

/-! # Weighted time sums (v1 Lemma I.8 type) -/

namespace C37

open Finset

/-- reindexing a tail sum -/
lemma shift_sum (g : ℝ → ℝ) (N T : ℕ) (hN : 1 ≤ N) (hg : ∀ i : ℕ, 0 ≤ g ((N : ℝ) + i)) :
    ∑ t ∈ range T, (if N ≤ t + 1 then g ((t : ℝ) + 1) else 0) ≤ ∑ i ∈ range T, g ((N : ℝ) + i) := by
  rw [← Finset.sum_filter]
  have hfil : (range T).filter (fun t => N ≤ t + 1) = Finset.Ico (N - 1) T := by
    ext t; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hfil, Finset.sum_Ico_eq_sum_range]
  have e : ∀ i : ℕ, (((N - 1 + i : ℕ) : ℝ) + 1) = (N : ℝ) + i := fun i => by
    rw [Nat.cast_add, Nat.cast_sub hN]; push_cast; ring
  simp only [e]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
    (fun i _ _ => hg i)

lemma sqrt_sum (N : ℕ) : ∑ i ∈ range N, 1 / Real.sqrt ((i : ℝ) + 1) ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have ha := Real.sqrt_nonneg (N : ℝ)
    have hb : 0 < Real.sqrt ((N : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have h1 : 1 / Real.sqrt ((N : ℝ) + 1) ≤ 2 * (Real.sqrt ((N : ℝ) + 1) - Real.sqrt N) := by
      rw [div_le_iff₀ hb]
      have s1 := Real.sq_sqrt (show (0 : ℝ) ≤ (N : ℝ) + 1 by positivity)
      have s2 := Real.sq_sqrt (show (0 : ℝ) ≤ (N : ℝ) by positivity)
      linarith [sq_nonneg (Real.sqrt ((N : ℝ) + 1) - Real.sqrt N)]
    push_cast
    linarith

lemma prefix_sum (N T : ℕ) :
    ∑ t ∈ range T, (if t + 1 < N then 1 / Real.sqrt ((t : ℝ) + 1) else 0) ≤ 2 * Real.sqrt N := by
  calc _ ≤ ∑ t ∈ range N, 1 / Real.sqrt ((t : ℝ) + 1) := by
        rw [← Finset.sum_filter]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro t ht; simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢; omega
        · intro i _ _; positivity
    _ ≤ _ := sqrt_sum N

lemma pure_sum (s : ℝ) (hs : 1 < s) (T : ℕ) : ∑ t ∈ range T, ((t : ℝ) + 1) ^ (-s) ≤ s / (s - 1) := by
  have h := tail_sum s hs 1 le_rfl T
  simp only [Nat.cast_one, Real.one_rpow, one_mul] at h
  calc ∑ t ∈ range T, ((t : ℝ) + 1) ^ (-s) = ∑ t ∈ range T, (1 + (t : ℝ)) ^ (-s) :=
        sum_congr rfl fun t _ => by rw [add_comm]
    _ ≤ _ := h

/-- `(n0/x)^r/√x = n0^r x^{−(r+1/2)}` -/
lemma homog_term (r n0 x : ℝ) (hn0 : 0 < n0) (hx : 0 < x) :
    (n0 / x) ^ r / Real.sqrt x = n0 ^ r * x ^ (-(r + 1 / 2)) := by
  rw [Real.div_rpow hn0.le hx.le, Real.sqrt_eq_rpow, div_div, ← Real.rpow_add hx,
    Real.rpow_neg hx.le, div_eq_mul_inv]

lemma homog_sum (r : ℝ) (hr : 5 / 6 ≤ r) (n0 : ℝ) (hn0 : 0 < n0) (N : ℕ) (hN : 1 ≤ N)
    (hn0N : n0 ≤ N) (T : ℕ) :
    ∑ t ∈ range T, (if N ≤ t + 1 then (n0 / ((t : ℝ) + 1)) ^ r / Real.sqrt ((t : ℝ) + 1) else 0) ≤
      4 * Real.sqrt N * (n0 / N) ^ r := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h1 := shift_sum (fun x => (n0 / x) ^ r / Real.sqrt x) N T hN (fun i => by
    have : (0 : ℝ) < (N : ℝ) + i := by positivity
    positivity)
  refine h1.trans ?_
  have hs : 1 < r + 1 / 2 := by linarith
  have h2 := tail_sum (r + 1 / 2) hs N hN T
  have e1 : ∑ i ∈ range T, (n0 / ((N : ℝ) + i)) ^ r / Real.sqrt ((N : ℝ) + i) =
      n0 ^ r * ∑ i ∈ range T, ((N : ℝ) + i) ^ (-(r + 1 / 2)) := by
    rw [mul_sum]
    exact sum_congr rfl fun i _ => homog_term r n0 _ hn0 (by positivity)
  rw [e1]
  have h3 : n0 ^ r * ((N : ℝ) ^ (1 - (r + 1 / 2)) * ((r + 1 / 2) / (r + 1 / 2 - 1))) ≤
      4 * Real.sqrt N * (n0 / N) ^ r := by
    have hc : (r + 1 / 2) / (r + 1 / 2 - 1) ≤ 4 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have e2 : n0 ^ r * (N : ℝ) ^ (1 - (r + 1 / 2)) = Real.sqrt N * (n0 / N) ^ r := by
      rw [Real.div_rpow hn0.le hNr.le, Real.sqrt_eq_rpow, show 1 - (r + 1 / 2) = 1 / 2 + -r by ring,
        Real.rpow_add hNr, Real.rpow_neg hNr.le]
      field_simp
    have hpos : 0 ≤ n0 ^ r * (N : ℝ) ^ (1 - (r + 1 / 2)) := by positivity
    calc n0 ^ r * ((N : ℝ) ^ (1 - (r + 1 / 2)) * ((r + 1 / 2) / (r + 1 / 2 - 1))) =
        (n0 ^ r * (N : ℝ) ^ (1 - (r + 1 / 2))) * ((r + 1 / 2) / (r + 1 / 2 - 1)) := by ring
      _ ≤ (n0 ^ r * (N : ℝ) ^ (1 - (r + 1 / 2))) * 4 := mul_le_mul_of_nonneg_left hc hpos
      _ = _ := by rw [e2]; ring
  exact (mul_le_mul_of_nonneg_left h2 (by positivity)).trans h3

end C37

/-! ===== module PerTime ===== -/

/-! # The common good event at a fixed time (v1 Definition C.25, Lemma C.26) -/

namespace C37

open MeasureTheory Finset

/-- the good event `G_t = {I_t = 1} ∩ ⋂_{a ≠ a*} {W_{t,a} ≥ 4θ}` -/
def Gset {K : ℕ} {Ω : Type*} (C : ℝ) (κ : ℕ → Ω → ℝ) (X : ℕ → Fin K → Ω → ℝ) (jstar : Fin K)
    (m : ℕ) (θ : ℝ) (t : ℕ) : Set Ω :=
  Iset C κ X m θ t ∩ {ω | ∀ a, a ≠ jstar → 4 * θ ≤ X t a ω - 2 * bR C κ t ω}

variable {d K : ℕ} {jstar : Fin K} {Δ : Fin K → ℝ} {Δ₀ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω} {T : ℕ} {C : ℝ} {X D e : ℕ → Fin K → Ω → ℝ}
  {κ : ℕ → Ω → ℝ}

lemma Iface.Gset_meas (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (m : ℕ) (θ : ℝ) (t : ℕ)
    (ht : t ≤ T) : MeasurableSet (Gset C κ X jstar m θ t) := by
  refine (I.Iset_meas' m θ t ht).inter ?_
  have e : {ω | ∀ a, a ≠ jstar → 4 * θ ≤ X t a ω - 2 * bR C κ t ω} =
      ⋂ a, ⋂ (_ : a ≠ jstar), {ω | 4 * θ ≤ X t a ω - 2 * bR C κ t ω} := by
    ext ω; simp
  rw [e]
  exact MeasurableSet.iInter fun a => MeasurableSet.iInter fun _ =>
    measurableSet_le measurable_const ((I.Xmeas t ht a).2.sub ((I.bR_meas' t ht).const_mul 2))

/-- separation on the good event -/
lemma Iface.Gset_sep (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (m : ℕ) (θ : ℝ) (t : ℕ)
    (ω : Ω) (hω : ω ∈ Gset C κ X jstar m θ t) (a : Fin K) (ha : a ≠ jstar) : 4 * θ ≤ X t a ω := by
  obtain ⟨⟨hB, _⟩, hW⟩ := hω
  simp only [BokSet, Set.mem_setOf_eq] at hB
  have hb : 0 ≤ bR C κ t ω := by unfold bR; linarith
  have := hW a ha
  linarith

/-- the budget event fails only on a null set -/
lemma Iface.Bok_null [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ)
    (ht : t ≤ T) : ∫ ω, (BokSet C κ t)ᶜ.indicator (1 : Ω → ℝ) ω ∂μ = 0 := by
  have h : ∀ᵐ ω ∂μ, (BokSet C κ t)ᶜ.indicator (1 : Ω → ℝ) ω = 0 := by
    filter_upwards [I.κsum] with ω hω
    have : ω ∈ BokSet C κ t := by
      simp only [BokSet, Set.mem_setOf_eq]
      have : ∑ s ∈ range t, κ s ω ≤ ∑ s ∈ range T, κ s ω :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr ht) fun s hs _ => (I.κb s
          (mem_range.mp hs) ω).1
      linarith
    simp [this]
  rw [integral_congr_ae h, integral_zero]

/-- the initial positive moment of the window (C.124) -/
lemma Iface.init_pos [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ)
    (m : ℕ) (θ : ℝ) (a : Fin K) (hθ : 0 < θ) (hmT : m ≤ T)
    (hburn : HG d K ≤ ((m : ℝ) + 1) ^ ((Pord K : ℝ) / 4)) :
    ∫ ω, Ii C κ X m θ m ω * Yc C θ X e m a ω ^ Pord K ∂μ ≤
      (2 * ((16 * kK K + 1) * ((m : ℝ) + 1) + 4 * C + 2 * θ)) ^ Pord K := by
  have hK := I.hK
  have hP := Pord_ge K hK
  have hev := Pord_even K
  set P := Pord K with hPdef
  have hC := I.hC
  set L := 4 * C + 2 * θ with hL
  have hL0 : 0 ≤ L := by positivity
  have hGint : Integrable (Gsum X m) μ :=
    int_of_bdd μ _ (Finset.measurable_sum _ fun b _ => ((I.Xmeas m hmT b).2.pow_const _)) _
      fun ω => by
        unfold Gsum
        rw [abs_of_nonneg (sum_nonneg fun b _ => hev.pow_nonneg _)]
        exact sum_le_sum fun b _ => by
          rw [← hev.pow_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (I.env m hmT ω b) _
  have hpt : ∀ ω, Ii C κ X m θ m ω * Yc C θ X e m a ω ^ P ≤ 2 ^ (P - 1) * (Gsum X m ω + L ^ P) := by
    intro ω
    have hG0 : 0 ≤ Gsum X m ω := sum_nonneg fun b _ => hev.pow_nonneg _
    by_cases hω : ω ∈ Iset C κ X m θ m
    · rw [Ii_mem C κ X m θ hω, one_mul]
      have hf := I.Iset_facts m θ m hθ le_rfl hmT ω hω a
      have hY0 : 0 ≤ Yc C θ X e m a ω := by linarith [hf.2.2.2.1]
      have hYu : Yc C θ X e m a ω ≤ |X m a ω| + L := by
        unfold Yc; simp only [hL]; linarith [le_abs_self (X m a ω), neg_abs_le (Ecum e m a ω), hf.2.1]
      have hXa : X m a ω ^ P ≤ Gsum X m ω :=
        single_le_sum (f := fun b => X m b ω ^ P) (fun b _ => hev.pow_nonneg _) (mem_univ a)
      calc Yc C θ X e m a ω ^ P ≤ (|X m a ω| + L) ^ P := pow_le_pow_left₀ hY0 hYu _
        _ ≤ 2 ^ (P - 1) * (|X m a ω| ^ P + L ^ P) := add_pow_le (abs_nonneg _) hL0 P
        _ = 2 ^ (P - 1) * (X m a ω ^ P + L ^ P) := by rw [hev.pow_abs]
        _ ≤ 2 ^ (P - 1) * (Gsum X m ω + L ^ P) := by gcongr
    · rw [Ii_nmem C κ X m θ hω, zero_mul]; positivity
  have hroot := I.abs_root m hmT hburn
  have hk := kK_pos K hK
  set x := (16 * kK K + 1) * ((m : ℝ) + 1) with hx
  have hx0 : 0 ≤ x := by positivity
  calc ∫ ω, Ii C κ X m θ m ω * Yc C θ X e m a ω ^ P ∂μ ≤ ∫ ω, 2 ^ (P - 1) * (Gsum X m ω + L ^ P) ∂μ :=
        integral_mono (I.pos_int m θ m a hθ le_rfl hmT P)
          ((hGint.add (integrable_const _)).const_mul _) hpt
    _ = 2 ^ (P - 1) * (∫ ω, Gsum X m ω ∂μ + L ^ P) := by
        rw [integral_const_mul, integral_add hGint (integrable_const _), integral_const]; simp
    _ ≤ 2 ^ (P - 1) * (x ^ P + L ^ P) := by gcongr
    _ ≤ 2 ^ (P - 1) * (x + L) ^ P := by gcongr; exact pow_add_pow_le hx0 hL0 (by omega)
    _ ≤ 2 ^ P * (x + L) ^ P := by
        gcongr
        · norm_num
        · omega
    _ = (2 * (x + L)) ^ P := by rw [mul_pow]
    _ = _ := by rw [hL]; ring

/-- Lemma C.26: the failure probability of the good event at a fixed time -/
lemma Iface.fail_bound [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ)
    (t0 m t : ℕ) (θ : ℝ) (hθ : 0 < θ) (ht0m : t0 ≤ m) (hmt : m ≤ t) (htT : t ≤ T)
    (hburn : HG d K ≤ ((t0 : ℝ) + 1) ^ ((Pord K : ℝ) / 4)) (hCn : C ≤ (t0 : ℝ) + 1)
    (h4C : 4 * C ≤ θ) (hmhalf : 2 * ((m : ℝ) + 1) ≤ (t : ℝ) + 1)
    (hθP : 2 * ((Pord K : ℝ) + 1) ≤ θ) (hmP : (Pord K : ℝ) + 1 ≤ 2 * ((m : ℝ) + 1))
    (hQ1 : ∀ s, m ≤ s → s < t → 3 * IAFTRL.Bc K * IAFTRL.beta d K (s + 1) ≤ θ)
    (hQ2 : ∀ s, m ≤ s → s < t →
      20 * ((Pord K : ℝ) + 1) * IAFTRL.beta d K (s + 1) * ((s : ℝ) + 1) ≤ θ ^ 2) :
    μ.real (Gset C κ X jstar m θ t)ᶜ ≤
      (HN d K * ((t : ℝ) + 1) ^ nuP K + (64 * ((t0 : ℝ) + 1)) ^ Pord K *
        (((t : ℝ) + 1) / ((t0 : ℝ) + 1)) ^ qN K) / θ ^ Pord K +
      K * (32 * θ / (((t : ℝ) + 1) * Δ₀)) ^ Pord K := by
  have hK := I.hK
  have hP := Pord_ge K hK
  have hev := Pord_even K
  set P := Pord K with hPdef
  set n : ℝ := (t : ℝ) + 1 with hn
  have hn0 : 0 < n := by positivity
  have hC := I.hC
  set L := θ ^ P with hL
  have hLpos : 0 < L := by positivity
  set S := univ.erase jstar with hS
  have hGm := I.Gset_meas m θ t htT
  have hqb : ∀ y, 0 ≤ 1 / max θ y := fun y => by
    have := lt_of_lt_of_le hθ (le_max_left θ y); positivity
  -- pointwise domination of the failure indicator
  have hpt : ∀ ω, (Gset C κ X jstar m θ t)ᶜ.indicator (1 : Ω → ℝ) ω ≤
      (BokSet C κ t)ᶜ.indicator (1 : Ω → ℝ) ω + (1 - sv C κ X m L (t + 1) ω) +
        ∑ a ∈ S, (8 * θ) ^ P * (Ii C κ X m θ t ω * (1 / max θ (Yc C θ X e t a ω)) ^ P) := by
    intro ω
    have hsv0 : 0 ≤ 1 - sv C κ X m L (t + 1) ω := sub_nonneg.mpr (sv_le_one C κ X m L (t + 1) ω)
    have hind : 0 ≤ (BokSet C κ t)ᶜ.indicator (1 : Ω → ℝ) ω := Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hsum : 0 ≤ ∑ a ∈ S, (8 * θ) ^ P * (Ii C κ X m θ t ω * (1 / max θ (Yc C θ X e t a ω)) ^ P) :=
      sum_nonneg fun a _ => mul_nonneg (by positivity)
        (mul_nonneg (Ii_nonneg C κ X m θ t ω) (pow_nonneg (hqb _) _))
    by_cases hG : ω ∈ Gset C κ X jstar m θ t
    · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hG)]; linarith
    · rw [Set.indicator_of_mem hG, Pi.one_apply]
      by_cases hB : ω ∈ BokSet C κ t
      · by_cases hSv : ω ∈ survSet C κ X m L (t + 1)
        · -- on the surviving window some gap fails
          have hI : ω ∈ Iset C κ X m θ t := ⟨hB, hSv⟩
          have : ∃ a, a ≠ jstar ∧ X t a ω - 2 * bR C κ t ω < 4 * θ := by
            by_contra hcon
            push Not at hcon
            exact hG ⟨hI, fun a ha => hcon a ha⟩
          obtain ⟨a, ha, hWa⟩ := this
          have hf := I.Iset_facts m θ t hθ hmt htT ω hI a
          have hbC := I.bR_le t htT ω
          have hY8 : Yc C θ X e t a ω < 8 * θ := by
            unfold Yc
            have := neg_abs_le (Ecum e t a ω)
            linarith [hf.2.1]
          have hYθ := hf.2.2.2.1
          have hY0 : 0 < Yc C θ X e t a ω := lt_of_lt_of_le hθ hYθ
          have hterm : 1 ≤ (8 * θ) ^ P * (Ii C κ X m θ t ω * (1 / max θ (Yc C θ X e t a ω)) ^ P) := by
            rw [Ii_mem C κ X m θ hI, one_mul, max_eq_right hYθ, ← mul_pow]
            apply one_le_pow₀
            rw [mul_one_div, le_div_iff₀ hY0]; linarith
          have hle := single_le_sum (f := fun a => (8 * θ) ^ P *
            (Ii C κ X m θ t ω * (1 / max θ (Yc C θ X e t a ω)) ^ P))
            (fun a _ => mul_nonneg (by positivity)
              (mul_nonneg (Ii_nonneg C κ X m θ t ω) (pow_nonneg (hqb _) _)))
            (Finset.mem_erase.mpr ⟨ha, mem_univ a⟩)
          linarith
        · have : sv C κ X m L (t + 1) ω = 0 := by unfold sv; simp [hSv]
          rw [this]; linarith
      · rw [Set.indicator_of_mem (show ω ∈ (BokSet C κ t)ᶜ from hB), Pi.one_apply]; linarith
  -- integrate
  have hBm : MeasurableSet (BokSet C κ t)ᶜ := by
    have := I.Iset_meas' m θ t htT
    refine MeasurableSet.compl ?_
    exact measurableSet_le (Finset.measurable_sum _ fun i hi => (I.κm i (by
      have := mem_range.mp hi; omega)).1.mono (I.filt i (by have := mem_range.mp hi; omega)).1 le_rfl)
      measurable_const
  have i1 : Integrable ((BokSet C κ t)ᶜ.indicator (1 : Ω → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hBm
  have i2 : Integrable (fun ω => 1 - sv C κ X m L (t + 1) ω) μ :=
    (integrable_const (1 : ℝ)).sub (I.sv_int m L (t + 1) (by omega))
  have i3 : ∀ a ∈ S, Integrable (fun ω => (8 * θ) ^ P * (Ii C κ X m θ t ω *
      (1 / max θ (Yc C θ X e t a ω)) ^ P)) μ := fun a _ => (I.inv_int m θ t a hθ htT P).const_mul _
  have i4 : Integrable (fun ω => (BokSet C κ t)ᶜ.indicator (1 : Ω → ℝ) ω + (1 - sv C κ X m L (t + 1) ω) +
      ∑ a ∈ S, (8 * θ) ^ P * (Ii C κ X m θ t ω * (1 / max θ (Yc C θ X e t a ω)) ^ P)) μ :=
    (i1.add i2).add (integrable_finsetSum _ i3)
  have i0 : Integrable ((Gset C κ X jstar m θ t)ᶜ.indicator (1 : Ω → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hGm.compl
  have hmono := integral_mono i0 i4 hpt
  rw [integral_indicator_one hGm.compl] at hmono
  have i12 : Integrable (fun ω => (BokSet C κ t)ᶜ.indicator (1 : Ω → ℝ) ω +
      (1 - sv C κ X m L (t + 1) ω)) μ := i1.add i2
  have iS : Integrable (fun ω => ∑ a ∈ S, (8 * θ) ^ P * (Ii C κ X m θ t ω *
      (1 / max θ (Yc C θ X e t a ω)) ^ P)) μ := integrable_finsetSum _ i3
  rw [integral_add i12 iS, integral_add i1 i2, I.Bok_null t htT, zero_add,
    integral_finsetSum _ i3] at hmono
  -- the window term
  have hwin := I.window t0 m t L hLpos.le ht0m hmt htT hburn hCn
  have hw2 : ∫ ω, (1 - sv C κ X m L (t + 1) ω) ∂μ ≤
      (HN d K * n ^ nuP K + (64 * ((t0 : ℝ) + 1)) ^ P * (n / ((t0 : ℝ) + 1)) ^ qN K) / L := by
    rw [le_div_iff₀ hLpos, mul_comm]; exact hwin
  -- the gap terms
  have hgap : ∀ a ∈ S, ∫ ω, (8 * θ) ^ P * (Ii C κ X m θ t ω * (1 / max θ (Yc C θ X e t a ω)) ^ P) ∂μ ≤
      (32 * θ / (n * Δ₀)) ^ P := by
    intro a haS
    have ha : a ≠ jstar := (Finset.mem_erase.mp haS).1
    rw [integral_const_mul]
    have hinv := I.inv_moment m θ t a hθ ha hmt htT hmhalf hθP hmP hQ1 hQ2
    have hΔa : Δ₀ ≤ Δ a := I.hΔge a ha
    have hΔ0 := I.hΔ₀
    calc (8 * θ) ^ P * ∫ ω, Ii C κ X m θ t ω * (1 / max θ (Yc C θ X e t a ω)) ^ P ∂μ ≤
        (8 * θ) ^ P * (4 / (n * Δ a)) ^ P := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (32 * θ / (n * Δ a)) ^ P := by
          have hΔap : 0 < Δ a := lt_of_lt_of_le hΔ0 hΔa
          rw [← mul_pow]; congr 1; field_simp; ring
      _ ≤ (32 * θ / (n * Δ₀)) ^ P := by
          have hΔap : 0 < Δ a := lt_of_lt_of_le hΔ0 hΔa
          apply pow_le_pow_left₀ (div_nonneg (by positivity) (mul_nonneg hn0.le hΔap.le))
          apply div_le_div_of_nonneg_left (by positivity) (mul_pos hn0 hΔ0)
          exact mul_le_mul_of_nonneg_left hΔa hn0.le
  have hsumg : ∑ a ∈ S, ∫ ω, (8 * θ) ^ P * (Ii C κ X m θ t ω * (1 / max θ (Yc C θ X e t a ω)) ^ P) ∂μ ≤
      K * (32 * θ / (n * Δ₀)) ^ P := by
    calc _ ≤ ∑ _a ∈ S, (32 * θ / (n * Δ₀)) ^ P := sum_le_sum hgap
      _ = S.card * (32 * θ / (n * Δ₀)) ^ P := by rw [sum_const, nsmul_eq_mul]
      _ ≤ K * (32 * θ / (n * Δ₀)) ^ P := by
          apply mul_le_mul_of_nonneg_right _ (by have := I.hΔ₀; positivity)
          have : S.card ≤ K := by
            rw [hS]; exact (Finset.card_erase_le).trans (by simp)
          exact_mod_cast this
  linarith

/-- (C.113) with Lemma C.30: the inverse gap ratio moment on the good event -/
lemma Iface.gap_inv [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ)
    (m t : ℕ) (θ : ℝ) (a : Fin K) (ha : a ≠ jstar) (hθ : 0 < θ) (hmt : m ≤ t) (htT : t ≤ T)
    (h4C : 4 * C ≤ θ) (hmhalf : 2 * ((m : ℝ) + 1) ≤ (t : ℝ) + 1)
    (hθP : 2 * ((Pord K : ℝ) + 1) ≤ θ) (hmP : (Pord K : ℝ) + 1 ≤ 2 * ((m : ℝ) + 1))
    (hQ1 : ∀ s, m ≤ s → s < t → 3 * IAFTRL.Bc K * IAFTRL.beta d K (s + 1) ≤ θ)
    (hQ2 : ∀ s, m ≤ s → s < t →
      20 * ((Pord K : ℝ) + 1) * IAFTRL.beta d K (s + 1) * ((s : ℝ) + 1) ≤ θ ^ 2) :
    Integrable ((Gset C κ X jstar m θ t).indicator
      fun ω => (((t : ℝ) + 1) * Δ a / X t a ω) ^ Pord K) μ ∧
    ∫ ω, (Gset C κ X jstar m θ t).indicator
      (fun ω => (((t : ℝ) + 1) * Δ a / X t a ω) ^ Pord K) ω ∂μ ≤ 8 ^ Pord K := by
  have hK := I.hK
  have hev := Pord_even K
  set P := Pord K with hPdef
  set n : ℝ := (t : ℝ) + 1 with hn
  have hn0 : 0 < n := by positivity
  have hΔa : 0 < Δ a := lt_of_lt_of_le I.hΔ₀ (I.hΔge a ha)
  have hGm := I.Gset_meas m θ t htT
  have hC := I.hC
  have hqb : ∀ y, 0 ≤ 1 / max θ y := fun y => by
    have := lt_of_lt_of_le hθ (le_max_left θ y); positivity
  have hfm : Measurable (fun ω => (n * Δ a / X t a ω) ^ P) :=
    (measurable_const.div (I.Xmeas t htT a).2).pow_const _
  have hint : Integrable ((Gset C κ X jstar m θ t).indicator fun ω => (n * Δ a / X t a ω) ^ P) μ := by
    refine int_of_bdd μ _ (hfm.indicator hGm) ((n * Δ a / (4 * θ)) ^ P) fun ω => ?_
    by_cases hω : ω ∈ Gset C κ X jstar m θ t
    · rw [Set.indicator_of_mem hω]
      have hX := I.Gset_sep m θ t ω hω a ha
      have hX0 : 0 < X t a ω := by linarith
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left (by positivity)
        (by positivity) hX) _
    · rw [Set.indicator_of_notMem hω, abs_zero]; positivity
  refine ⟨hint, ?_⟩
  have hpt : ∀ ω, (Gset C κ X jstar m θ t).indicator (fun ω => (n * Δ a / X t a ω) ^ P) ω ≤
      (2 * n * Δ a) ^ P * (Ii C κ X m θ t ω * (1 / max θ (Yc C θ X e t a ω)) ^ P) := by
    intro ω
    by_cases hω : ω ∈ Gset C κ X jstar m θ t
    · rw [Set.indicator_of_mem hω, Ii_mem C κ X m θ hω.1, one_mul]
      have hX := I.Gset_sep m θ t ω hω a ha
      have hX0 : 0 < X t a ω := by linarith
      have hf := I.Iset_facts m θ t hθ hmt htT ω hω.1 a
      have hY0 : 0 < Yc C θ X e t a ω := lt_of_lt_of_le hθ hf.2.2.2.1
      rw [max_eq_right hf.2.2.2.1, ← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      have hY2 : Yc C θ X e t a ω ≤ 2 * X t a ω := by
        unfold Yc; linarith [neg_abs_le (Ecum e t a ω), hf.2.1]
      rw [mul_one_div, div_le_div_iff₀ hX0 hY0]
      linarith [mul_le_mul_of_nonneg_left hY2 (by positivity : (0 : ℝ) ≤ n * Δ a)]
    · rw [Set.indicator_of_notMem hω]
      exact mul_nonneg (by positivity) (mul_nonneg (Ii_nonneg C κ X m θ t ω) (pow_nonneg (hqb _) _))
  have hinv := I.inv_moment m θ t a hθ ha hmt htT hmhalf hθP hmP hQ1 hQ2
  calc ∫ ω, (Gset C κ X jstar m θ t).indicator (fun ω => (n * Δ a / X t a ω) ^ P) ω ∂μ ≤
      ∫ ω, (2 * n * Δ a) ^ P * (Ii C κ X m θ t ω * (1 / max θ (Yc C θ X e t a ω)) ^ P) ∂μ :=
        integral_mono hint ((I.inv_int m θ t a hθ htT P).const_mul _) hpt
    _ = (2 * n * Δ a) ^ P * ∫ ω, Ii C κ X m θ t ω * (1 / max θ (Yc C θ X e t a ω)) ^ P ∂μ :=
        integral_const_mul _ _
    _ ≤ (2 * n * Δ a) ^ P * (4 / (n * Δ a)) ^ P := mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 8 ^ P := by rw [← mul_pow]; congr 1; field_simp; ring

/-- (C.113) with Lemma C.14: the positive gap ratio moment on the good event -/
lemma Iface.gap_pos [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ)
    (m t : ℕ) (θ : ℝ) (a : Fin K) (ha : a ≠ jstar) (hθ : 0 < θ) (hmt : m ≤ t) (htT : t ≤ T)
    (hQ1 : ∀ s, m ≤ s → s < t → 3 * IAFTRL.Bc K * IAFTRL.beta d K (s + 1) ≤ θ)
    (A : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ s, m ≤ s → s < t → Δ a + 5 * ((Pord K : ℝ) - 1) * IAFTRL.beta d K (s + 1) / θ ≤ A)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hW0 : ∫ ω, Ii C κ X m θ m ω * Yc C θ X e m a ω ^ Pord K ∂μ ≤ w0 ^ Pord K) :
    Integrable ((Gset C κ X jstar m θ t).indicator
      fun ω => (X t a ω / (((t : ℝ) + 1) * Δ a)) ^ Pord K) μ ∧
    ∫ ω, (Gset C κ X jstar m θ t).indicator
      (fun ω => (X t a ω / (((t : ℝ) + 1) * Δ a)) ^ Pord K) ω ∂μ ≤
      ((A * ((t : ℝ) + 1) / (1 - kap0 K) + w0 * (((t : ℝ) + 1) / ((m : ℝ) + 1)) ^ (2 * kap0 K)) /
        (((t : ℝ) + 1) * Δ a)) ^ Pord K := by
  have hK := I.hK
  have hev := Pord_even K
  set P := Pord K with hPdef
  set n : ℝ := (t : ℝ) + 1 with hn
  have hn0 : 0 < n := by positivity
  have hΔa : 0 < Δ a := lt_of_lt_of_le I.hΔ₀ (I.hΔge a ha)
  have hGm := I.Gset_meas m θ t htT
  have hfm : Measurable (fun ω => (X t a ω / (n * Δ a)) ^ P) :=
    ((I.Xmeas t htT a).2.div_const _).pow_const _
  have hint : Integrable ((Gset C κ X jstar m θ t).indicator fun ω => (X t a ω / (n * Δ a)) ^ P) μ := by
    refine int_of_bdd μ _ (hfm.indicator hGm) ((renv d K t / (n * Δ a)) ^ P) fun ω => ?_
    by_cases hω : ω ∈ Gset C κ X jstar m θ t
    · rw [Set.indicator_of_mem hω]
      have hX := I.Gset_sep m θ t ω hω a ha
      have hX0 : 0 ≤ X t a ω := by linarith
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right
        ((le_abs_self _).trans (I.env t htT ω a)) (by positivity)) _
    · rw [Set.indicator_of_notMem hω, abs_zero]
      have := renv_nonneg d K hK I.hd t; positivity
  refine ⟨hint, ?_⟩
  have hpt : ∀ ω, (Gset C κ X jstar m θ t).indicator (fun ω => (X t a ω / (n * Δ a)) ^ P) ω ≤
      (1 / (n * Δ a)) ^ P * (Ii C κ X m θ t ω * Yc C θ X e t a ω ^ P) := by
    intro ω
    by_cases hω : ω ∈ Gset C κ X jstar m θ t
    · rw [Set.indicator_of_mem hω, Ii_mem C κ X m θ hω.1, one_mul, ← mul_pow]
      have hX := I.Gset_sep m θ t ω hω a ha
      have hX0 : 0 ≤ X t a ω := by linarith
      have hf := I.Iset_facts m θ t hθ hmt htT ω hω.1 a
      have hXY : X t a ω ≤ Yc C θ X e t a ω := by
        unfold Yc; linarith [le_abs_self (Ecum e t a ω), hf.2.1, I.hC]
      apply pow_le_pow_left₀ (by positivity)
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right hXY (by positivity)
    · rw [Set.indicator_of_notMem hω]
      by_cases hI : ω ∈ Iset C κ X m θ t
      · rw [Ii_mem C κ X m θ hI, one_mul]
        have hf := I.Iset_facts m θ t hθ hmt htT ω hI a
        have : 0 ≤ Yc C θ X e t a ω := by linarith [hf.2.2.2.1]
        positivity
      · rw [Ii_nmem C κ X m θ hI, zero_mul, mul_zero]
  have hpos := I.pos_moment m θ t a hθ hmt htT hQ1 A hA0 hA w0 hw0 hW0
  set φ := A * n / (1 - kap0 K) + w0 * (n / ((m : ℝ) + 1)) ^ (2 * kap0 K) with hφ
  calc ∫ ω, (Gset C κ X jstar m θ t).indicator (fun ω => (X t a ω / (n * Δ a)) ^ P) ω ∂μ ≤
      ∫ ω, (1 / (n * Δ a)) ^ P * (Ii C κ X m θ t ω * Yc C θ X e t a ω ^ P) ∂μ :=
        integral_mono hint ((I.pos_int m θ t a hθ hmt htT P).const_mul _) hpt
    _ = (1 / (n * Δ a)) ^ P * ∫ ω, Ii C κ X m θ t ω * Yc C θ X e t a ω ^ P ∂μ :=
        integral_const_mul _ _
    _ ≤ (1 / (n * Δ a)) ^ P * φ ^ P := mul_le_mul_of_nonneg_left hpos (by positivity)
    _ = (φ / (n * Δ a)) ^ P := by rw [← mul_pow]; congr 1; ring

end C37

/-! ===== module MainFacts ===== -/

/-! # Tuning of the window (v1 Lemma C.27, (C.184)–(C.185)) -/

namespace C37

noncomputable def αE : ℝ := 15 / 16
noncomputable def ωE : ℝ := 255 / 256

/-- the plateau `z = 64 n_0^ω n^{1−ω}` -/
noncomputable def zf (n0 n : ℝ) : ℝ := 64 * n0 ^ ωE * n ^ (1 - ωE)

/-- the window threshold `θ = n^α + 4 z` -/
noncomputable def θf (n0 n : ℝ) : ℝ := n ^ αE + 4 * zf n0 n

/-- the pure-time threshold constant -/
noncomputable def Cbig (d K : ℕ) (Δ₀ : ℝ) : ℝ :=
  3 * IAFTRL.Bc K * Cb d K + 20 * ((Pord K : ℝ) + 1) * Cb d K + 2 * ((Pord K : ℝ) + 1) +
    10 * (Pord K : ℝ) * Cb d K / Δ₀

noncomputable def Qc (d K : ℕ) (Δ₀ : ℝ) : ℝ := Cbig d K Δ₀ ^ ((8 : ℝ) / 3)

noncomputable def Nb (d K : ℕ) : ℕ := ⌈HG d K⌉₊ + Pord K

noncomputable def L0 (Δ₀ : ℝ) : ℝ := (32768 / Δ₀) ^ ((256 : ℝ) / 255)

noncomputable def t0f (d K : ℕ) (C : ℝ) : ℕ := Nb d K + ⌈C⌉₊

noncomputable def Ncf (d K : ℕ) (Δ₀ C : ℝ) : ℕ :=
  ⌈Qc d K Δ₀ + L0 Δ₀ * ((t0f d K C : ℝ) + 1)⌉₊

section Facts

variable {d K : ℕ} {Δ₀ C : ℝ}

lemma Cbig_pos (hd : 1 ≤ d) (hK : 1 ≤ K) (hΔ₀ : 0 < Δ₀) : 0 < Cbig d K Δ₀ := by
  unfold Cbig; have := Cb_ge16 d K hd; have := Bc_pos K hK; positivity

lemma L0_ge (hΔ₀ : 0 < Δ₀) (hΔ₀1 : Δ₀ ≤ 1) : 1 ≤ L0 Δ₀ := by
  unfold L0
  apply Real.one_le_rpow _ (by norm_num)
  rw [le_div_iff₀ hΔ₀]; linarith

lemma L0_pow (hΔ₀ : 0 < Δ₀) : L0 Δ₀ ^ ωE = 32768 / Δ₀ := by
  unfold L0 ωE
  rw [← Real.rpow_mul (by positivity)]; norm_num

lemma Nb_burn (hK : 1 ≤ K) (x : ℝ) (hx : (Nb d K : ℝ) ≤ x) : HG d K ≤ x ^ ((Pord K : ℝ) / 4) := by
  have hH : HG d K ≤ (⌈HG d K⌉₊ : ℝ) := Nat.le_ceil _
  have hH1 : 1 ≤ HG d K := le_max_left _ _
  have hNb : (⌈HG d K⌉₊ : ℝ) ≤ Nb d K := by unfold Nb; push_cast; linarith [(Nat.cast_nonneg (Pord K) : (0 : ℝ) ≤ _)]
  have hx1 : 1 ≤ x := by linarith
  have hP : (4 : ℝ) ≤ (Pord K : ℝ) / 4 := by
    have : (512 : ℝ) ≤ Pord K := by exact_mod_cast Pord_ge K hK
    linarith
  calc HG d K ≤ x := by linarith
    _ = x ^ (1 : ℝ) := (Real.rpow_one x).symm
    _ ≤ x ^ ((Pord K : ℝ) / 4) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)

lemma Nb_ge (d K : ℕ) : (Pord K : ℝ) ≤ Nb d K := by
  unfold Nb; push_cast; linarith [(Nat.cast_nonneg ⌈HG d K⌉₊ : (0 : ℝ) ≤ _)]

lemma t0f_ge (d K : ℕ) (C : ℝ) : (Nb d K : ℝ) ≤ t0f d K C := by
  unfold t0f; push_cast; linarith [(Nat.cast_nonneg ⌈C⌉₊ : (0 : ℝ) ≤ _)]

lemma C_le_t0 (d K : ℕ) (C : ℝ) : C ≤ (t0f d K C : ℝ) + 1 := by
  unfold t0f; push_cast
  have := Nat.le_ceil C
  linarith [(Nat.cast_nonneg (Nb d K) : (0 : ℝ) ≤ _)]

/-- `z = 64 n (n_0/n)^ω` -/
lemma zf_eq (n0 n : ℝ) (hn0 : 0 < n0) (hn : 0 < n) : zf n0 n = 64 * n * (n0 / n) ^ ωE := by
  unfold zf
  rw [Real.div_rpow hn0.le hn.le, Real.rpow_sub hn, Real.rpow_one]
  field_simp

/-- `z = 64 n_0 (n/n_0)^{1−ω}` -/
lemma zf_eq' (n0 n : ℝ) (hn0 : 0 < n0) (hn : 0 < n) :
    zf n0 n = 64 * n0 * (n / n0) ^ (1 - ωE) := by
  unfold zf
  rw [Real.div_rpow hn.le hn0.le, Real.rpow_sub hn0, Real.rpow_one]
  field_simp

end Facts

section Good

variable {d K : ℕ} {Δ₀ C : ℝ}

lemma good_QL (hd : 1 ≤ d) (hK : 1 ≤ K) (hΔ₀ : 0 < Δ₀) (n : ℝ)
    (hgood : (Ncf d K Δ₀ C : ℝ) ≤ n) :
    Qc d K Δ₀ ≤ n ∧ L0 Δ₀ * ((t0f d K C : ℝ) + 1) ≤ n := by
  have h := (Nat.le_ceil (Qc d K Δ₀ + L0 Δ₀ * ((t0f d K C : ℝ) + 1))).trans hgood
  have hQ : 0 ≤ Qc d K Δ₀ := by unfold Qc; exact Real.rpow_nonneg (Cbig_pos hd hK hΔ₀).le _
  have hL : 0 ≤ L0 Δ₀ * ((t0f d K C : ℝ) + 1) := by unfold L0; positivity
  exact ⟨by linarith, by linarith⟩

lemma good_n1 (hd : 1 ≤ d) (hK : 1 ≤ K) (hΔ₀ : 0 < Δ₀) (hΔ₀1 : Δ₀ ≤ 1) (n : ℝ)
    (hgood : (Ncf d K Δ₀ C : ℝ) ≤ n) : (t0f d K C : ℝ) + 1 ≤ n := by
  have h := (good_QL hd hK hΔ₀ n hgood).2
  have hL := L0_ge hΔ₀ hΔ₀1
  have : (t0f d K C : ℝ) + 1 ≤ L0 Δ₀ * ((t0f d K C : ℝ) + 1) := le_mul_of_one_le_left (by positivity) hL
  linarith

lemma good_Cbig (hd : 1 ≤ d) (hK : 1 ≤ K) (hΔ₀ : 0 < Δ₀) (n : ℝ)
    (hgood : (Ncf d K Δ₀ C : ℝ) ≤ n) : Cbig d K Δ₀ ≤ n ^ ((3 : ℝ) / 8) := by
  have h := (good_QL hd hK hΔ₀ n hgood).1
  have hc := (Cbig_pos hd hK hΔ₀).le
  have hQ : 0 ≤ Qc d K Δ₀ := by unfold Qc; exact Real.rpow_nonneg hc _
  calc Cbig d K Δ₀ = (Qc d K Δ₀) ^ ((3 : ℝ) / 8) := by
        unfold Qc; rw [← Real.rpow_mul hc]; norm_num
    _ ≤ n ^ ((3 : ℝ) / 8) := Real.rpow_le_rpow hQ h (by norm_num)

lemma Cbig_ge (hd : 1 ≤ d) (hK : 1 ≤ K) (hΔ₀ : 0 < Δ₀) :
    3 * IAFTRL.Bc K * Cb d K ≤ Cbig d K Δ₀ ∧ 20 * ((Pord K : ℝ) + 1) * Cb d K ≤ Cbig d K Δ₀ ∧
      2 * ((Pord K : ℝ) + 1) ≤ Cbig d K Δ₀ ∧ 10 * (Pord K : ℝ) * Cb d K / Δ₀ ≤ Cbig d K Δ₀ := by
  have h1 := Cb_ge16 d K hd
  have h2 := Bc_pos K hK
  have h3 : 0 ≤ 3 * IAFTRL.Bc K * Cb d K := by positivity
  have h4 : 0 ≤ 20 * ((Pord K : ℝ) + 1) * Cb d K := by positivity
  have h5 : 0 ≤ 2 * ((Pord K : ℝ) + 1) := by positivity
  have h6 : 0 ≤ 10 * (Pord K : ℝ) * Cb d K / Δ₀ := by positivity
  unfold Cbig
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma good_big (hd : 1 ≤ d) (hK : 1 ≤ K) (hΔ₀ : 0 < Δ₀) (n : ℝ) (hn1 : 1 ≤ n)
    (hgood : (Ncf d K Δ₀ C : ℝ) ≤ n) : 1026 ≤ n := by
  have h := good_Cbig hd hK hΔ₀ n hgood
  have hP : (512 : ℝ) ≤ Pord K := by exact_mod_cast Pord_ge K hK
  have hc := (Cbig_ge hd hK hΔ₀).2.2.1
  have hle : n ^ ((3 : ℝ) / 8) ≤ n := by
    calc n ^ ((3 : ℝ) / 8) ≤ n ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      _ = n := Real.rpow_one n
  linarith

/-- `(n_0/n)^ω ≤ Δ₀/32768` -/
lemma good_rho (hd : 1 ≤ d) (hK : 1 ≤ K) (hΔ₀ : 0 < Δ₀) (n : ℝ) (hn1 : 1 ≤ n)
    (hgood : (Ncf d K Δ₀ C : ℝ) ≤ n) :
    (((t0f d K C : ℝ) + 1) / n) ^ ωE ≤ Δ₀ / 32768 := by
  have h := (good_QL hd hK hΔ₀ n hgood).2
  have hL : 0 < L0 Δ₀ := by unfold L0; positivity
  have hn0 : 0 < (t0f d K C : ℝ) + 1 := by positivity
  have hn : 0 < n := by linarith
  have h1 : ((t0f d K C : ℝ) + 1) / n ≤ 1 / L0 Δ₀ := by
    rw [div_le_div_iff₀ hn hL]; linarith
  calc (((t0f d K C : ℝ) + 1) / n) ^ ωE ≤ (1 / L0 Δ₀) ^ ωE :=
        Real.rpow_le_rpow (by positivity) h1 (by unfold ωE; norm_num)
    _ = Δ₀ / 32768 := by
        rw [Real.div_rpow zero_le_one hL.le, Real.one_rpow, L0_pow hΔ₀]; field_simp

lemma good_z_le (hd : 1 ≤ d) (hK : 1 ≤ K) (hΔ₀ : 0 < Δ₀) (hΔ₀1 : Δ₀ ≤ 1) (n : ℝ) (hn1 : 1 ≤ n)
    (hgood : (Ncf d K Δ₀ C : ℝ) ≤ n) : zf ((t0f d K C : ℝ) + 1) n ≤ n / 512 := by
  have hn0 : 0 < (t0f d K C : ℝ) + 1 := by positivity
  rw [zf_eq _ n hn0 (by linarith)]
  have h := good_rho hd hK hΔ₀ n hn1 hgood
  have : 64 * n * (((t0f d K C : ℝ) + 1) / n) ^ ωE ≤ 64 * n * (Δ₀ / 32768) :=
    mul_le_mul_of_nonneg_left h (by positivity)
  have e : 64 * n * (Δ₀ / 32768) = n * Δ₀ / 512 := by ring
  have : n * Δ₀ / 512 ≤ n / 512 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    nlinarith
  linarith

lemma good_z_ge (hd : 1 ≤ d) (hK : 1 ≤ K) (hΔ₀ : 0 < Δ₀) (hΔ₀1 : Δ₀ ≤ 1) (n : ℝ) (hn1 : 1 ≤ n)
    (hgood : (Ncf d K Δ₀ C : ℝ) ≤ n) : (t0f d K C : ℝ) + 1 ≤ zf ((t0f d K C : ℝ) + 1) n := by
  have hn0 : 0 < (t0f d K C : ℝ) + 1 := by positivity
  have hnn := good_n1 hd hK hΔ₀ hΔ₀1 n hgood
  rw [zf_eq' _ n hn0 (by linarith)]
  have h1 : 1 ≤ (n / ((t0f d K C : ℝ) + 1)) ^ (1 - ωE) :=
    Real.one_le_rpow (by rw [le_div_iff₀ hn0]; linarith) (by unfold ωE; norm_num)
  nlinarith

/-- `√n · C_big ≤ n^α` -/
lemma good_sqrt (hd : 1 ≤ d) (hK : 1 ≤ K) (hΔ₀ : 0 < Δ₀) (n : ℝ) (hn1 : 1 ≤ n)
    (hgood : (Ncf d K Δ₀ C : ℝ) ≤ n) : Real.sqrt n * Cbig d K Δ₀ ≤ n ^ αE := by
  have hn : 0 < n := by linarith
  have h := good_Cbig hd hK hΔ₀ n hgood
  have e : n ^ αE = n ^ ((1 : ℝ) / 2) * n ^ ((7 : ℝ) / 16) := by
    rw [← Real.rpow_add hn]; unfold αE; norm_num
  have h2 : n ^ ((3 : ℝ) / 8) ≤ n ^ ((7 : ℝ) / 16) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  rw [e, Real.sqrt_eq_rpow]
  exact mul_le_mul_of_nonneg_left (h.trans h2) (by positivity)

/-- `n^{3/2} · C_big ≤ (n^α)^2` -/
lemma good_sq (hd : 1 ≤ d) (hK : 1 ≤ K) (hΔ₀ : 0 < Δ₀) (n : ℝ) (hn1 : 1 ≤ n)
    (hgood : (Ncf d K Δ₀ C : ℝ) ≤ n) : n * Real.sqrt n * Cbig d K Δ₀ ≤ (n ^ αE) ^ 2 := by
  have hn : 0 < n := by linarith
  have h := good_Cbig hd hK hΔ₀ n hgood
  have e : (n ^ αE) ^ 2 = n * n ^ ((1 : ℝ) / 2) * n ^ ((3 : ℝ) / 8) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    conv_rhs => rw [show n * n ^ ((1 : ℝ) / 2) = n ^ (1 : ℝ) * n ^ ((1 : ℝ) / 2) by rw [Real.rpow_one]]
    rw [← Real.rpow_add hn, ← Real.rpow_add hn]; unfold αE; norm_num
  rw [e, Real.sqrt_eq_rpow]
  exact mul_le_mul_of_nonneg_left h (by positivity)

end Good

end C37

/-! ===== module Conv ===== -/

/-! # Converting the per-time bounds into summable forms ((C.179), (C.125)) -/

namespace C37

lemma rpow_pow' (x a : ℝ) (hx : 0 ≤ x) (P : ℕ) : (x ^ a) ^ P = x ^ (a * P) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

set_option maxHeartbeats 1000000 in
/-- (C.179), (C.194): the failure bound in summable form -/
lemma fail_conv (P q K : ℕ) (hP : 512 ≤ P) (HN Δ₀ n n0 : ℝ) (hHN : 0 ≤ HN) (hΔ₀ : 0 < Δ₀)
    (hn1 : 1 ≤ n) (hn0 : 1 ≤ n0) (hn0n : n0 ≤ n) :
    (HN * n ^ (3 * (P : ℝ) / 4) + (64 * n0) ^ P * (n / n0) ^ q) / (θf n0 n) ^ P +
        K * (32 * θf n0 n / (n * Δ₀)) ^ P ≤
      HN * n ^ (-(3 * (P : ℝ) / 16)) + (n0 / n) ^ ((P : ℝ) / 256 - q) +
        K * 2 ^ (P - 1) * (32 / Δ₀) ^ P * n ^ (-((P : ℝ) / 16)) +
        K * 2 ^ (P - 1) * (8192 / Δ₀) ^ P * (n0 / n) ^ (ωE * P) := by
  have hn : 0 < n := by linarith
  have hn0p : 0 < n0 := by linarith
  set ρ := n0 / n with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := by rw [hρ, div_le_one hn]; exact hn0n
  have hz : zf n0 n = 64 * n * ρ ^ ωE := zf_eq n0 n hn0p hn
  set z := zf n0 n with hzdef
  have hz0 : 0 < z := by rw [hz]; positivity
  have hnα : 0 < n ^ αE := by positivity
  set θ := θf n0 n with hθdef
  have hθ : θ = n ^ αE + 4 * z := rfl
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hθP : 0 < θ ^ P := by positivity
  -- (a) the particular term
  have ha : HN * n ^ (3 * (P : ℝ) / 4) / θ ^ P ≤ HN * n ^ (-(3 * (P : ℝ) / 16)) := by
    have h1 : n ^ (αE * P) ≤ θ ^ P := by
      rw [← rpow_pow' n αE hn.le P]
      exact pow_le_pow_left₀ hnα.le (by rw [hθ]; linarith) P
    have h2 : 0 < n ^ (αE * P) := by positivity
    calc HN * n ^ (3 * (P : ℝ) / 4) / θ ^ P ≤ HN * n ^ (3 * (P : ℝ) / 4) / n ^ (αE * P) :=
          div_le_div_of_nonneg_left (by positivity) h2 h1
      _ = HN * n ^ (-(3 * (P : ℝ) / 16)) := by
          rw [mul_div_assoc, ← Real.rpow_sub hn]; unfold αE; congr 2; ring
  -- (b) the homogeneous term
  have hb : (64 * n0) ^ P * (n / n0) ^ q / θ ^ P ≤ ρ ^ ((P : ℝ) / 256 - q) := by
    have h4z : (256 * n * ρ ^ ωE) ^ P ≤ θ ^ P := by
      apply pow_le_pow_left₀ (by positivity)
      rw [hθ, hz]; linarith
    have hden : 0 < (256 * n * ρ ^ ωE) ^ P := by positivity
    have e1 : n0 = ρ * n := by rw [hρ]; field_simp
    have e2 : n / n0 = ρ⁻¹ := by rw [hρ]; field_simp
    have hρω : ρ ^ ωE ≠ 0 := (Real.rpow_pos_of_pos hρ0 _).ne'
    have e3 : 64 * n0 / (256 * n * ρ ^ ωE) = 1 / 4 * ρ ^ (1 - ωE) := by
      rw [Real.rpow_sub hρ0, Real.rpow_one, e1]; field_simp; ring
    calc (64 * n0) ^ P * (n / n0) ^ q / θ ^ P ≤ (64 * n0) ^ P * (n / n0) ^ q / (256 * n * ρ ^ ωE) ^ P :=
          div_le_div_of_nonneg_left (by positivity) hden h4z
      _ = (64 * n0 / (256 * n * ρ ^ ωE)) ^ P * (n / n0) ^ q := by rw [mul_div_right_comm, ← div_pow]
      _ = (1 / 4) ^ P * ρ ^ ((P : ℝ) / 256 - q) := by
          rw [e3, e2, mul_pow, rpow_pow' ρ _ hρ0.le, inv_pow, ← Real.rpow_natCast ρ q,
            ← Real.rpow_neg hρ0.le, mul_assoc, ← Real.rpow_add hρ0]
          unfold ωE; congr 2; ring
      _ ≤ ρ ^ ((P : ℝ) / 256 - q) := by
          have : (1 / 4 : ℝ) ^ P ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
          have h0 : 0 < ρ ^ ((P : ℝ) / 256 - q) := by positivity
          have := mul_le_mul_of_nonneg_right this h0.le
          linarith
  -- (c) the gap terms
  have hc : (K : ℝ) * (32 * θ / (n * Δ₀)) ^ P ≤
      K * 2 ^ (P - 1) * (32 / Δ₀) ^ P * n ^ (-((P : ℝ) / 16)) +
        K * 2 ^ (P - 1) * (8192 / Δ₀) ^ P * ρ ^ (ωE * P) := by
    have e1 : 32 * θ / (n * Δ₀) = 32 / Δ₀ * (n ^ (αE - 1) + 256 * ρ ^ ωE) := by
      rw [hθ, hz, Real.rpow_sub_one hn.ne']; field_simp; ring
    rw [e1, mul_pow]
    have h2 := add_pow_le (show 0 ≤ n ^ (αE - 1) by positivity)
      (show 0 ≤ 256 * ρ ^ ωE by positivity) P
    have e2 : (n ^ (αE - 1)) ^ P = n ^ (-((P : ℝ) / 16)) := by
      rw [rpow_pow' n _ hn.le]; unfold αE; congr 1; ring
    have e3 : (256 * ρ ^ ωE) ^ P = 256 ^ P * ρ ^ (ωE * P) := by
      rw [mul_pow, rpow_pow' ρ _ hρ0.le]
    rw [e2, e3] at h2
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ K * (32 / Δ₀) ^ P)
    have e4 : (8192 / Δ₀) ^ P = (32 / Δ₀) ^ P * 256 ^ P := by rw [← mul_pow]; congr 1; ring
    rw [e4]
    linarith [h3]
  have e0 : (HN * n ^ (3 * (P : ℝ) / 4) + (64 * n0) ^ P * (n / n0) ^ q) / θ ^ P =
      HN * n ^ (3 * (P : ℝ) / 4) / θ ^ P + (64 * n0) ^ P * (n / n0) ^ q / θ ^ P := add_div _ _ _
  rw [e0]
  linarith

set_option maxHeartbeats 1000000 in
/-- (C.123)–(C.125): the positive local moment bound in the form `8 Ψ_t` -/
lemma pos_conv (P : ℕ) (k k0 Δa Δ₀ C n n0 : ℝ) (m : ℕ)
    (hk1 : 1 ≤ k) (hk : k < 1.65) (hk0 : 0 ≤ k0) (hk01 : k0 ≤ 1 / 1024)
    (hΔ₀ : 0 < Δ₀) (hΔa : Δ₀ ≤ Δa) (hC : 0 ≤ C) (hCn0 : C ≤ n0) (hn0 : 2 ≤ n0) (hn1 : 1 ≤ n)
    (hn0n : n0 ≤ n) (hzm : zf n0 n ≤ m) (hmz : (m : ℝ) < zf n0 n + 1) (hzn : n0 ≤ zf n0 n) :
    (((Δa + Δ₀ / 2) * n / (1 - k0) + 2 * ((16 * k + 1) * ((m : ℝ) + 1) + 4 * C + 2 * θf n0 n) *
        (n / ((m : ℝ) + 1)) ^ (2 * k0)) / (n * Δa)) ^ P ≤
      (8 * (1 + (1120 * (n0 / n) ^ ((1 : ℝ) / 2) + n ^ (-(1 : ℝ) / 32)) / Δ₀)) ^ P := by
  have hn : 0 < n := by linarith
  have hn0p : 0 < n0 := by linarith
  have hΔap : 0 < Δa := lt_of_lt_of_le hΔ₀ hΔa
  set ρ := n0 / n with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := by rw [hρ, div_le_one hn]; exact hn0n
  set z := zf n0 n with hzdef
  have hz : z = 64 * n * ρ ^ ωE := zf_eq n0 n hn0p hn
  have hz2 : 2 ≤ z := le_trans hn0 hzn
  have hz0 : 0 < z := by linarith
  set κ1 := 2 * k0 with hκ1
  have hκ10 : 0 ≤ κ1 := by positivity
  have hκ11 : κ1 ≤ 1 / 512 := by linarith
  set θ := θf n0 n with hθdef
  have hθ : θ = n ^ αE + 4 * z := rfl
  have hnα : 0 < n ^ αE := by positivity
  -- s1
  have hs1 : (Δa + Δ₀ / 2) * n / (1 - k0) ≤ 2 * n * Δa := by
    rw [div_le_iff₀ (by linarith)]
    have : Δa + Δ₀ / 2 ≤ 2 * Δa * (1 - k0) := by nlinarith
    nlinarith
  -- s2
  have hs2 : 2 * ((16 * k + 1) * ((m : ℝ) + 1) + 4 * C + 2 * θ) ≤ 140 * z + 4 * n ^ αE := by
    have hm1 : (m : ℝ) + 1 ≤ 2 * z := by linarith
    have h16 : 16 * k + 1 ≤ 27.4 := by linarith
    have h3 : (16 * k + 1) * ((m : ℝ) + 1) ≤ 27.4 * (2 * z) :=
      mul_le_mul h16 hm1 (by positivity) (by norm_num)
    rw [hθ]; linarith
  -- s3
  have hs3 : (n / ((m : ℝ) + 1)) ^ κ1 ≤ (n / z) ^ κ1 :=
    Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_left hn.le hz0 (by linarith)) hκ10
  -- s4
  have hs4 : z * (n / z) ^ κ1 ≤ 64 * n * ρ ^ ((1 : ℝ) / 2) := by
    have hzn' : 0 < z / n := by positivity
    have e1 : z * (n / z) ^ κ1 = n * (z / n) ^ (1 - κ1) := by
      rw [Real.rpow_sub hzn', Real.rpow_one, show n / z = (z / n)⁻¹ by rw [inv_div],
        Real.inv_rpow hzn'.le]
      field_simp
    rw [e1]
    have e2 : z / n = 64 * ρ ^ ωE := by rw [hz]; field_simp
    rw [e2, Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hρ0.le]
    have h1 : (64 : ℝ) ^ (1 - κ1) ≤ 64 := by
      calc (64 : ℝ) ^ (1 - κ1) ≤ 64 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 64 := Real.rpow_one 64
    have h2 : ρ ^ (ωE * (1 - κ1)) ≤ ρ ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1 (by unfold ωE; linarith)
    have h3 : 0 ≤ ρ ^ (ωE * (1 - κ1)) := by positivity
    have := mul_le_mul h1 h2 h3 (by norm_num)
    have := mul_le_mul_of_nonneg_left this hn.le
    linarith
  -- s5
  have hs5 : n ^ αE * (n / z) ^ κ1 ≤ n * n ^ (-(1 : ℝ) / 32) := by
    have h1 : (n / z) ^ κ1 ≤ n ^ κ1 :=
      Real.rpow_le_rpow (by positivity) (div_le_self hn.le (by linarith)) hκ10
    have h2 : n ^ αE * n ^ κ1 ≤ n * n ^ (-(1 : ℝ) / 32) := by
      rw [← Real.rpow_add hn]
      conv_rhs => rw [show n * n ^ (-(1 : ℝ) / 32) = n ^ (1 : ℝ) * n ^ (-(1 : ℝ) / 32) by rw [Real.rpow_one]]
      rw [← Real.rpow_add hn]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by unfold αE; linarith)
    calc n ^ αE * (n / z) ^ κ1 ≤ n ^ αE * n ^ κ1 := mul_le_mul_of_nonneg_left h1 hnα.le
      _ ≤ _ := h2
  -- s6
  have hs6 : 2 * ((16 * k + 1) * ((m : ℝ) + 1) + 4 * C + 2 * θ) * (n / ((m : ℝ) + 1)) ^ κ1 ≤
      8960 * n * ρ ^ ((1 : ℝ) / 2) + 4 * (n * n ^ (-(1 : ℝ) / 32)) := by
    have hp : 0 ≤ (n / ((m : ℝ) + 1)) ^ κ1 := by positivity
    have hp' : 0 ≤ (n / z) ^ κ1 := by positivity
    calc 2 * ((16 * k + 1) * ((m : ℝ) + 1) + 4 * C + 2 * θ) * (n / ((m : ℝ) + 1)) ^ κ1 ≤
        (140 * z + 4 * n ^ αE) * (n / z) ^ κ1 :=
          mul_le_mul hs2 hs3 hp (by positivity)
      _ = 140 * (z * (n / z) ^ κ1) + 4 * (n ^ αE * (n / z) ^ κ1) := by ring
      _ ≤ 140 * (64 * n * ρ ^ ((1 : ℝ) / 2)) + 4 * (n * n ^ (-(1 : ℝ) / 32)) := by
          gcongr
      _ = _ := by ring
  -- final
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hb0 : 0 ≤ ((Δa + Δ₀ / 2) * n / (1 - k0) + 2 * ((16 * k + 1) * ((m : ℝ) + 1) + 4 * C + 2 * θ) *
      (n / ((m : ℝ) + 1)) ^ κ1) / (n * Δa) := by
    apply div_nonneg _ (by positivity)
    apply add_nonneg (div_nonneg (by positivity) (by linarith))
    apply mul_nonneg _ (by positivity)
    have : 0 ≤ 16 * k + 1 := by linarith
    positivity
  apply pow_le_pow_left₀ hb0
  have hρh : 0 ≤ ρ ^ ((1 : ℝ) / 2) := by positivity
  have hnh : 0 ≤ n ^ (-(1 : ℝ) / 32) := by positivity
  rw [div_le_iff₀ (by positivity)]
  have hsum : (Δa + Δ₀ / 2) * n / (1 - k0) + 2 * ((16 * k + 1) * ((m : ℝ) + 1) + 4 * C + 2 * θ) *
      (n / ((m : ℝ) + 1)) ^ κ1 ≤ 2 * n * Δa + (8960 * n * ρ ^ ((1 : ℝ) / 2) + 4 * (n * n ^ (-(1 : ℝ) / 32))) := by
    linarith
  have hfin : 2 * n * Δa + (8960 * n * ρ ^ ((1 : ℝ) / 2) + 4 * (n * n ^ (-(1 : ℝ) / 32))) ≤
      8 * (1 + (1120 * ρ ^ ((1 : ℝ) / 2) + n ^ (-(1 : ℝ) / 32)) / Δ₀) * (n * Δa) := by
    have e : 8 * (1 + (1120 * ρ ^ ((1 : ℝ) / 2) + n ^ (-(1 : ℝ) / 32)) / Δ₀) * (n * Δa) =
        8 * n * Δa + n * (8960 * ρ ^ ((1 : ℝ) / 2) + 8 * n ^ (-(1 : ℝ) / 32)) * (Δa / Δ₀) := by
      field_simp; ring
    rw [e]
    have hr : 1 ≤ Δa / Δ₀ := by rw [le_div_iff₀ hΔ₀]; linarith
    have hX : 0 ≤ n * (8960 * ρ ^ ((1 : ℝ) / 2) + 8 * n ^ (-(1 : ℝ) / 32)) := by positivity
    have := mul_le_mul_of_nonneg_left hr hX
    have h1 : 0 ≤ n * Δa := by positivity
    have h2 : 0 ≤ n * n ^ (-(1 : ℝ) / 32) := by positivity
    linarith
  linarith

end C37

/-! ===== module Main ===== -/

/-! # The window at a fixed endpoint and its hypotheses (v1 Lemma C.27) -/

namespace C37

open MeasureTheory Finset

noncomputable def n0f (d K : ℕ) (C : ℝ) : ℝ := (t0f d K C : ℝ) + 1
noncomputable def zt (d K : ℕ) (C : ℝ) (t : ℕ) : ℝ := zf (n0f d K C) ((t : ℝ) + 1)
noncomputable def θt (d K : ℕ) (C : ℝ) (t : ℕ) : ℝ := θf (n0f d K C) ((t : ℝ) + 1)
noncomputable def mt (d K : ℕ) (C : ℝ) (t : ℕ) : ℕ := ⌈zt d K C t⌉₊

section WH

variable {d K : ℕ} {Δ₀ C : ℝ}

lemma n0f_ge (d K : ℕ) (C : ℝ) (hK : 1 ≤ K) : (Pord K : ℝ) + 1 ≤ n0f d K C := by
  unfold n0f; linarith [Nb_ge d K, t0f_ge d K C]

lemma wh_z (hd : 1 ≤ d) (hK : 1 ≤ K) (hΔ₀ : 0 < Δ₀) (hΔ₀1 : Δ₀ ≤ 1) (t : ℕ)
    (hg : Ncf d K Δ₀ C ≤ t + 1) :
    n0f d K C ≤ zt d K C t ∧ zt d K C t ≤ ((t : ℝ) + 1) / 512 ∧ 1026 ≤ (t : ℝ) + 1 ∧
      n0f d K C ≤ (t : ℝ) + 1 := by
  have hg' : (Ncf d K Δ₀ C : ℝ) ≤ (t : ℝ) + 1 := by exact_mod_cast hg
  have hn1 : (1 : ℝ) ≤ (t : ℝ) + 1 := by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
  exact ⟨good_z_ge hd hK hΔ₀ hΔ₀1 _ hn1 hg', good_z_le hd hK hΔ₀ hΔ₀1 _ hn1 hg',
    good_big hd hK hΔ₀ _ hn1 hg', good_n1 hd hK hΔ₀ hΔ₀1 _ hg'⟩

lemma wh_m (hd : 1 ≤ d) (hK : 1 ≤ K) (hΔ₀ : 0 < Δ₀) (hΔ₀1 : Δ₀ ≤ 1) (t : ℕ)
    (hg : Ncf d K Δ₀ C ≤ t + 1) :
    t0f d K C ≤ mt d K C t ∧ zt d K C t ≤ mt d K C t ∧ (mt d K C t : ℝ) < zt d K C t + 1 ∧
      2 * ((mt d K C t : ℝ) + 1) ≤ (t : ℝ) + 1 ∧ (Pord K : ℝ) + 1 ≤ 2 * ((mt d K C t : ℝ) + 1) ∧
      mt d K C t ≤ t := by
  obtain ⟨h1, h2, h3, h4⟩ := wh_z (C := C) hd hK hΔ₀ hΔ₀1 t hg
  have hz : zt d K C t ≤ mt d K C t := Nat.le_ceil _
  have hz' : (mt d K C t : ℝ) < zt d K C t + 1 := Nat.ceil_lt_add_one (by
    have : (0 : ℝ) < n0f d K C := by unfold n0f; positivity
    linarith)
  have ht0 : t0f d K C ≤ mt d K C t := by
    have : (t0f d K C : ℝ) < mt d K C t := by unfold n0f at h1; linarith
    exact_mod_cast this.le
  have h2m : 2 * ((mt d K C t : ℝ) + 1) ≤ (t : ℝ) + 1 := by linarith
  have hP : (Pord K : ℝ) + 1 ≤ 2 * ((mt d K C t : ℝ) + 1) := by
    have := n0f_ge d K C hK
    have : (t0f d K C : ℝ) ≤ mt d K C t := by exact_mod_cast ht0
    unfold n0f at *
    have := Nb_ge d K
    have := t0f_ge d K C
    linarith
  have hmt : mt d K C t ≤ t := by
    have : (mt d K C t : ℝ) ≤ t := by linarith
    exact_mod_cast this
  exact ⟨ht0, hz, hz', h2m, hP, hmt⟩

lemma wh_θ (hd : 1 ≤ d) (hK : 1 ≤ K) (hΔ₀ : 0 < Δ₀) (hΔ₀1 : Δ₀ ≤ 1) (hC : 0 ≤ C) (t : ℕ)
    (hg : Ncf d K Δ₀ C ≤ t + 1) :
    0 < θt d K C t ∧ 4 * C ≤ θt d K C t ∧ 2 * ((Pord K : ℝ) + 1) ≤ θt d K C t ∧
      Real.sqrt ((t : ℝ) + 1) * Cbig d K Δ₀ ≤ θt d K C t ∧
      ((t : ℝ) + 1) * Real.sqrt ((t : ℝ) + 1) * Cbig d K Δ₀ ≤ θt d K C t ^ 2 ∧
      4 * ((t : ℝ) + 1) ^ ((3 : ℝ) / 4) ≤ 4 * θt d K C t := by
  obtain ⟨h1, h2, h3, h4⟩ := wh_z (C := C) hd hK hΔ₀ hΔ₀1 t hg
  have hg' : (Ncf d K Δ₀ C : ℝ) ≤ (t : ℝ) + 1 := by exact_mod_cast hg
  have hn1 : (1 : ℝ) ≤ (t : ℝ) + 1 := by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
  have hn0 : (0 : ℝ) < n0f d K C := by unfold n0f; positivity
  have hθ : θt d K C t = ((t : ℝ) + 1) ^ αE + 4 * zt d K C t := rfl
  have hα : 0 < ((t : ℝ) + 1) ^ αE := by positivity
  have hs := good_sqrt hd hK hΔ₀ _ hn1 hg'
  have hsq := good_sq hd hK hΔ₀ _ hn1 hg'
  have hcb := Cbig_ge hd hK hΔ₀
  have hsq1 : 1 ≤ Real.sqrt ((t : ℝ) + 1) := by
    have := Real.sqrt_le_sqrt hn1; simpa using this
  have hz0 : 0 ≤ zt d K C t := by linarith
  have hCn : C ≤ n0f d K C := by unfold n0f; exact C_le_t0 d K C
  refine ⟨by rw [hθ]; positivity, by rw [hθ]; linarith, ?_, by rw [hθ]; linarith, ?_, ?_⟩
  · have hcp := (Cbig_pos hd hK hΔ₀).le
    have : Cbig d K Δ₀ ≤ Real.sqrt ((t : ℝ) + 1) * Cbig d K Δ₀ := le_mul_of_one_le_left hcp hsq1
    rw [hθ]; linarith [hcb.2.2.1]
  · have h5 : (((t : ℝ) + 1) ^ αE) ^ 2 ≤ θt d K C t ^ 2 :=
      pow_le_pow_left₀ hα.le (by rw [hθ]; linarith) 2
    linarith
  · have : ((t : ℝ) + 1) ^ ((3 : ℝ) / 4) ≤ ((t : ℝ) + 1) ^ αE :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by unfold αE; norm_num)
    rw [hθ]; linarith

/-- the local thresholds hold throughout the window -/
lemma wh_Q (hd : 1 ≤ d) (hK : 1 ≤ K) (hΔ₀ : 0 < Δ₀) (hΔ₀1 : Δ₀ ≤ 1) (hC : 0 ≤ C) (t : ℕ)
    (hg : Ncf d K Δ₀ C ≤ t + 1) (s : ℕ) (hs : s ≤ t) :
    3 * IAFTRL.Bc K * IAFTRL.beta d K (s + 1) ≤ θt d K C t ∧
      20 * ((Pord K : ℝ) + 1) * IAFTRL.beta d K (s + 1) * ((s : ℝ) + 1) ≤ θt d K C t ^ 2 ∧
      5 * ((Pord K : ℝ) - 1) * IAFTRL.beta d K (s + 1) / θt d K C t ≤ Δ₀ / 2 := by
  obtain ⟨hθ0, -, -, hθs, hθq, -⟩ := wh_θ hd hK hΔ₀ hΔ₀1 hC t hg
  have hcb := Cbig_ge hd hK hΔ₀
  have hβC : IAFTRL.beta d K (s + 1) ≤ Cb d K * Real.sqrt ((t : ℝ) + 1) := by
    have h1 := beta_le_Cb d K (s + 1) hK (by omega)
    have h2 : Real.sqrt ((s + 1 : ℕ) : ℝ) ≤ Real.sqrt ((t : ℝ) + 1) := Real.sqrt_le_sqrt (by
      push_cast; have : (s : ℝ) ≤ t := by exact_mod_cast hs
      linarith)
    have := Cb_ge16 d K hd
    calc IAFTRL.beta d K (s + 1) ≤ Cb d K * Real.sqrt ((s + 1 : ℕ) : ℝ) := h1
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by linarith)
  have hβ0 : 0 ≤ IAFTRL.beta d K (s + 1) := by have := beta_ge16 d K (s + 1) hd; linarith
  have hsq0 : 0 ≤ Real.sqrt ((t : ℝ) + 1) := Real.sqrt_nonneg _
  have hP : (512 : ℝ) ≤ Pord K := by exact_mod_cast Pord_ge K hK
  have hB := Bc_pos K hK
  have hCb := Cb_ge16 d K hd
  refine ⟨?_, ?_, ?_⟩
  · calc 3 * IAFTRL.Bc K * IAFTRL.beta d K (s + 1) ≤ 3 * IAFTRL.Bc K * (Cb d K * Real.sqrt ((t : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hβC (by positivity)
      _ = Real.sqrt ((t : ℝ) + 1) * (3 * IAFTRL.Bc K * Cb d K) := by ring
      _ ≤ Real.sqrt ((t : ℝ) + 1) * Cbig d K Δ₀ := mul_le_mul_of_nonneg_left hcb.1 hsq0
      _ ≤ _ := hθs
  · have hst : (s : ℝ) ≤ t := by exact_mod_cast hs
    have hs1 : (s : ℝ) + 1 ≤ (t : ℝ) + 1 := by linarith
    calc 20 * ((Pord K : ℝ) + 1) * IAFTRL.beta d K (s + 1) * ((s : ℝ) + 1) ≤
        20 * ((Pord K : ℝ) + 1) * (Cb d K * Real.sqrt ((t : ℝ) + 1)) * ((t : ℝ) + 1) := by
          gcongr
      _ = ((t : ℝ) + 1) * Real.sqrt ((t : ℝ) + 1) * (20 * ((Pord K : ℝ) + 1) * Cb d K) := by ring
      _ ≤ ((t : ℝ) + 1) * Real.sqrt ((t : ℝ) + 1) * Cbig d K Δ₀ :=
          mul_le_mul_of_nonneg_left hcb.2.1 (by positivity)
      _ ≤ _ := hθq
  · rw [div_le_iff₀ hθ0]
    have h1 : 5 * ((Pord K : ℝ) - 1) * IAFTRL.beta d K (s + 1) ≤
        5 * (Pord K : ℝ) * (Cb d K * Real.sqrt ((t : ℝ) + 1)) := by
      have := mul_le_mul_of_nonneg_left hβC (by positivity : (0 : ℝ) ≤ 5 * (Pord K : ℝ))
      linarith
    have h2 : 10 * (Pord K : ℝ) * Cb d K / Δ₀ * Real.sqrt ((t : ℝ) + 1) ≤ θt d K C t :=
      le_trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hcb.2.2.2 hsq0) hθs
    have e : Δ₀ / 2 * (10 * (Pord K : ℝ) * Cb d K / Δ₀ * Real.sqrt ((t : ℝ) + 1)) =
        5 * (Pord K : ℝ) * (Cb d K * Real.sqrt ((t : ℝ) + 1)) := by field_simp; ring
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ Δ₀ / 2)
    linarith

end WH

/-- `n^{−a}/√n ≤ n^{−2}` for `a ≥ 3/2`, `n ≥ 1` -/
lemma pow_sqrt_le (a n : ℝ) (ha : 3 / 2 ≤ a) (hn : 1 ≤ n) : n ^ (-a) / Real.sqrt n ≤ n ^ (-(2 : ℝ)) := by
  have hn0 : 0 < n := by linarith
  rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hn0]
  exact Real.rpow_le_rpow_of_exponent_le hn (by linarith)

set_option maxHeartbeats 1000000 in
/-- Lemma C.24: the weighted failure sum -/
lemma fail_sum (P q K : ℕ) (hP : 512 ≤ P) (hq : (q : ℝ) ≤ (P : ℝ) / 4000 + 1) (hKP : (K : ℝ) ≤ 2 ^ P)
    (HN Δ₀ n0 : ℝ) (hHN : 0 ≤ HN) (hΔ₀ : 0 < Δ₀) (hn0 : 1 ≤ n0) (N : ℕ) (hN : 1 ≤ N)
    (hn0N : n0 ≤ N) (hNL : (n0 / N) ^ ωE ≤ Δ₀ / 32768) (T : ℕ) (f : ℕ → ℝ)
    (hf0 : ∀ t, 0 ≤ f t)
    (hf : ∀ t < T, f t ≤ if N ≤ t + 1 then
      HN * ((t : ℝ) + 1) ^ (-(3 * (P : ℝ) / 16)) + (n0 / ((t : ℝ) + 1)) ^ ((P : ℝ) / 256 - q) +
        K * 2 ^ (P - 1) * (32 / Δ₀) ^ P * ((t : ℝ) + 1) ^ (-((P : ℝ) / 16)) +
        K * 2 ^ (P - 1) * (8192 / Δ₀) ^ P * (n0 / ((t : ℝ) + 1)) ^ (ωE * P) else 1) :
    ∑ t ∈ range T, f t / Real.sqrt ((t : ℝ) + 1) ≤
      8 * Real.sqrt N + 2 * (HN + K * 2 ^ (P - 1) * (32 / Δ₀) ^ P) := by
  have hPr : (512 : ℝ) ≤ P := by exact_mod_cast hP
  set A3 := (K : ℝ) * 2 ^ (P - 1) * (32 / Δ₀) ^ P with hA3
  set A4 := (K : ℝ) * 2 ^ (P - 1) * (8192 / Δ₀) ^ P with hA4
  have hA3p : 0 ≤ A3 := by positivity
  have hA4p : 0 ≤ A4 := by positivity
  set r0 := (P : ℝ) / 256 - q with hr0
  have hr0 : 5 / 6 ≤ r0 := by rw [hr0]; linarith
  have hωP : 5 / 6 ≤ ωE * P := by unfold ωE; linarith
  have hn0p : 0 < n0 := by linarith
  -- termwise domination
  have hterm : ∀ t ∈ range T, f t / Real.sqrt ((t : ℝ) + 1) ≤
      (if t + 1 < N then 1 / Real.sqrt ((t : ℝ) + 1) else 0) + HN * ((t : ℝ) + 1) ^ (-(2 : ℝ)) +
      (if N ≤ t + 1 then (n0 / ((t : ℝ) + 1)) ^ r0 / Real.sqrt ((t : ℝ) + 1) else 0) +
      A3 * ((t : ℝ) + 1) ^ (-(2 : ℝ)) +
      A4 * (if N ≤ t + 1 then (n0 / ((t : ℝ) + 1)) ^ (ωE * P) / Real.sqrt ((t : ℝ) + 1) else 0) := by
    intro t ht
    have htT := mem_range.mp ht
    have hn1 : (1 : ℝ) ≤ (t : ℝ) + 1 := by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
    have hsq : 0 < Real.sqrt ((t : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
    have hp2 : 0 ≤ ((t : ℝ) + 1) ^ (-(2 : ℝ)) := by positivity
    have hft := hf t htT
    by_cases hg : N ≤ t + 1
    · rw [if_pos hg] at hft
      have hng : ¬ (t + 1 < N) := by omega
      rw [if_neg hng, if_pos hg, if_pos hg, zero_add]
      have h1 : f t / Real.sqrt ((t : ℝ) + 1) ≤ (HN * ((t : ℝ) + 1) ^ (-(3 * (P : ℝ) / 16)) +
          (n0 / ((t : ℝ) + 1)) ^ r0 + A3 * ((t : ℝ) + 1) ^ (-((P : ℝ) / 16)) +
          A4 * (n0 / ((t : ℝ) + 1)) ^ (ωE * P)) / Real.sqrt ((t : ℝ) + 1) :=
        div_le_div_of_nonneg_right hft hsq.le
      have e : (HN * ((t : ℝ) + 1) ^ (-(3 * (P : ℝ) / 16)) +
          (n0 / ((t : ℝ) + 1)) ^ r0 + A3 * ((t : ℝ) + 1) ^ (-((P : ℝ) / 16)) +
          A4 * (n0 / ((t : ℝ) + 1)) ^ (ωE * P)) / Real.sqrt ((t : ℝ) + 1) =
          HN * (((t : ℝ) + 1) ^ (-(3 * (P : ℝ) / 16)) / Real.sqrt ((t : ℝ) + 1)) +
          (n0 / ((t : ℝ) + 1)) ^ r0 / Real.sqrt ((t : ℝ) + 1) +
          A3 * (((t : ℝ) + 1) ^ (-((P : ℝ) / 16)) / Real.sqrt ((t : ℝ) + 1)) +
          A4 * ((n0 / ((t : ℝ) + 1)) ^ (ωE * P) / Real.sqrt ((t : ℝ) + 1)) := by ring
      have h2 := pow_sqrt_le (3 * (P : ℝ) / 16) ((t : ℝ) + 1) (by linarith) hn1
      have h3 := pow_sqrt_le ((P : ℝ) / 16) ((t : ℝ) + 1) (by linarith) hn1
      have h4 := mul_le_mul_of_nonneg_left h2 hHN
      have h5 := mul_le_mul_of_nonneg_left h3 hA3p
      linarith
    · rw [if_neg hg] at hft
      have hlt : t + 1 < N := by omega
      rw [if_pos hlt, if_neg hg, if_neg hg, mul_zero, add_zero, add_zero]
      have h1 : f t / Real.sqrt ((t : ℝ) + 1) ≤ 1 / Real.sqrt ((t : ℝ) + 1) :=
        div_le_div_of_nonneg_right hft hsq.le
      have : 0 ≤ HN * ((t : ℝ) + 1) ^ (-(2 : ℝ)) := mul_nonneg hHN hp2
      have : 0 ≤ A3 * ((t : ℝ) + 1) ^ (-(2 : ℝ)) := mul_nonneg hA3p hp2
      linarith
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum,
    ← mul_sum]
  have s1 := prefix_sum N T
  have s2 := pure_sum 2 (by norm_num) T
  rw [show (2 : ℝ) / (2 - 1) = 2 by norm_num] at s2
  have s3 := homog_sum r0 hr0 n0 hn0p N hN hn0N T
  have s4 := homog_sum (ωE * P) hωP n0 hn0p N hN hn0N T
  have hρ1 : n0 / N ≤ 1 := by
    rw [div_le_one (by exact_mod_cast (show 0 < N by omega))]; exact hn0N
  have hρ0 : 0 ≤ n0 / N := by positivity
  have h3' : (n0 / N) ^ r0 ≤ 1 := Real.rpow_le_one hρ0 hρ1 (by linarith)
  have hA4b : A4 * (n0 / N) ^ (ωE * P) ≤ 1 / 2 := by
    have e1 : (n0 / N) ^ (ωE * P) = ((n0 / N) ^ ωE) ^ P := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hρ0]
    rw [e1]
    have h1 : ((n0 / N) ^ ωE) ^ P ≤ (Δ₀ / 32768) ^ P := pow_le_pow_left₀ (by positivity) hNL P
    have h2 : A4 * (Δ₀ / 32768) ^ P = K * 2 ^ (P - 1) * (1 / 4) ^ P := by
      rw [hA4, mul_assoc, ← mul_pow]; congr 2; field_simp; ring
    have h3 : (K : ℝ) * 2 ^ (P - 1) * (1 / 4) ^ P ≤ 1 / 2 := by
      have e : (2 : ℝ) ^ P = 2 * 2 ^ (P - 1) := by rw [← pow_succ']; congr 1; omega
      have e2 : (1 / 4 : ℝ) ^ P = 1 / 2 ^ P * (1 / 2 ^ P) := by
        rw [one_div_mul_one_div, ← mul_pow, one_div_pow]; norm_num
      rw [e2]
      have h2P : (0 : ℝ) < 2 ^ P := by positivity
      have : (K : ℝ) * 2 ^ (P - 1) * (1 / 2 ^ P * (1 / 2 ^ P)) = K / 2 ^ P * (2 ^ (P - 1) / 2 ^ P) := by
        field_simp
      rw [this]
      have h4 : (K : ℝ) / 2 ^ P ≤ 1 := by rw [div_le_one h2P]; exact hKP
      have h5 : (2 : ℝ) ^ (P - 1) / 2 ^ P = 1 / 2 := by rw [e]; field_simp
      rw [h5]
      have : 0 ≤ (K : ℝ) / 2 ^ P := by positivity
      linarith
    calc A4 * ((n0 / N) ^ ωE) ^ P ≤ A4 * (Δ₀ / 32768) ^ P := mul_le_mul_of_nonneg_left h1 hA4p
      _ ≤ 1 / 2 := by rw [h2]; exact h3
  have hsN : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have s3' : ∑ t ∈ range T, (if N ≤ t + 1 then (n0 / ((t : ℝ) + 1)) ^ r0 / Real.sqrt ((t : ℝ) + 1) else 0) ≤
      4 * Real.sqrt N := s3.trans (by
        have := mul_le_mul_of_nonneg_left h3' (by positivity : (0 : ℝ) ≤ 4 * Real.sqrt N)
        linarith)
  have s4' : A4 * ∑ t ∈ range T, (if N ≤ t + 1 then (n0 / ((t : ℝ) + 1)) ^ (ωE * P) /
      Real.sqrt ((t : ℝ) + 1) else 0) ≤ 2 * Real.sqrt N := by
    have := mul_le_mul_of_nonneg_left s4 hA4p
    have e : A4 * (4 * Real.sqrt N * (n0 / N) ^ (ωE * P)) = 4 * Real.sqrt N * (A4 * (n0 / N) ^ (ωE * P)) := by ring
    have := mul_le_mul_of_nonneg_left hA4b (by positivity : (0 : ℝ) ≤ 4 * Real.sqrt N)
    linarith
  have s2' : HN * ∑ t ∈ range T, ((t : ℝ) + 1) ^ (-(2 : ℝ)) ≤ 2 * HN := by
    have := mul_le_mul_of_nonneg_left s2 hHN; linarith
  have s2'' : A3 * ∑ t ∈ range T, ((t : ℝ) + 1) ^ (-(2 : ℝ)) ≤ 2 * A3 := by
    have := mul_le_mul_of_nonneg_left s2 hA3p; linarith
  linarith

/-- the summed distortion (C.119) -/
lemma psi_sum (Δ₀ n0 : ℝ) (hΔ₀ : 0 < Δ₀) (hn0 : 1 ≤ n0) (N : ℕ) (hN : 1 ≤ N) (hn0N : n0 ≤ N)
    (T : ℕ) :
    ∑ t ∈ range T, ((if N ≤ t + 1 then 1 + (1120 * (n0 / ((t : ℝ) + 1)) ^ ((1 : ℝ) / 2) +
      ((t : ℝ) + 1) ^ (-(1 : ℝ) / 32)) / Δ₀ else 1) - 1) / ((t : ℝ) + 1) ≤ 3393 / Δ₀ := by
  have hn0p : 0 < n0 := by linarith
  have hterm : ∀ t ∈ range T, ((if N ≤ t + 1 then 1 + (1120 * (n0 / ((t : ℝ) + 1)) ^ ((1 : ℝ) / 2) +
      ((t : ℝ) + 1) ^ (-(1 : ℝ) / 32)) / Δ₀ else 1) - 1) / ((t : ℝ) + 1) ≤
      1 / Δ₀ * (1120 * (if N ≤ t + 1 then n0 ^ ((1 : ℝ) / 2) * ((t : ℝ) + 1) ^ (-((3 : ℝ) / 2)) else 0) +
        ((t : ℝ) + 1) ^ (-((33 : ℝ) / 32))) := by
    intro t _
    have hn : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    by_cases hg : N ≤ t + 1
    · rw [if_pos hg, if_pos hg]
      have e1 : (n0 / ((t : ℝ) + 1)) ^ ((1 : ℝ) / 2) / ((t : ℝ) + 1) =
          n0 ^ ((1 : ℝ) / 2) * ((t : ℝ) + 1) ^ (-((3 : ℝ) / 2)) := by
        rw [Real.div_rpow hn0p.le hn.le, div_div, show -((3 : ℝ) / 2) = -((1 : ℝ) / 2 + 1) by norm_num,
          Real.rpow_neg hn.le, Real.rpow_add hn, Real.rpow_one, div_eq_mul_inv]
      have e2 : ((t : ℝ) + 1) ^ (-(1 : ℝ) / 32) / ((t : ℝ) + 1) = ((t : ℝ) + 1) ^ (-((33 : ℝ) / 32)) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hn]; norm_num
      have e3 : (1 + (1120 * (n0 / ((t : ℝ) + 1)) ^ ((1 : ℝ) / 2) + ((t : ℝ) + 1) ^ (-(1 : ℝ) / 32)) / Δ₀ - 1) /
          ((t : ℝ) + 1) = 1 / Δ₀ * (1120 * ((n0 / ((t : ℝ) + 1)) ^ ((1 : ℝ) / 2) / ((t : ℝ) + 1)) +
            ((t : ℝ) + 1) ^ (-(1 : ℝ) / 32) / ((t : ℝ) + 1)) := by
        field_simp; ring
      rw [e3, e1, e2]
    · rw [if_neg hg, if_neg hg, sub_self, zero_div, mul_zero, zero_add]
      positivity
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum, sum_add_distrib, ← mul_sum]
  have s1 := shift_sum (fun x => n0 ^ ((1 : ℝ) / 2) * x ^ (-((3 : ℝ) / 2))) N T hN (fun i => by positivity)
  have s2 := tail_sum ((3 : ℝ) / 2) (by norm_num) N hN T
  have s3 := pure_sum ((33 : ℝ) / 32) (by norm_num) T
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have s12 : ∑ t ∈ range T, (if N ≤ t + 1 then n0 ^ ((1 : ℝ) / 2) * ((t : ℝ) + 1) ^ (-((3 : ℝ) / 2)) else 0) ≤ 3 := by
    refine s1.trans ?_
    rw [← mul_sum]
    have h1 := mul_le_mul_of_nonneg_left s2 (by positivity : (0 : ℝ) ≤ n0 ^ ((1 : ℝ) / 2))
    refine h1.trans ?_
    have e : n0 ^ ((1 : ℝ) / 2) * ((N : ℝ) ^ (1 - (3 : ℝ) / 2) * ((3 : ℝ) / 2 / ((3 : ℝ) / 2 - 1))) =
        3 * (n0 / N) ^ ((1 : ℝ) / 2) := by
      rw [Real.div_rpow hn0p.le hNr.le, show (1 : ℝ) - 3 / 2 = -(1 / 2) by norm_num, Real.rpow_neg hNr.le]
      norm_num; ring
    rw [e]
    have : (n0 / N) ^ ((1 : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one (by positivity) (by rw [div_le_one hNr]; exact hn0N) (by norm_num)
    linarith
  have hfin : 1120 * ∑ t ∈ range T, (if N ≤ t + 1 then n0 ^ ((1 : ℝ) / 2) *
      ((t : ℝ) + 1) ^ (-((3 : ℝ) / 2)) else 0) + ∑ t ∈ range T, ((t : ℝ) + 1) ^ (-((33 : ℝ) / 32)) ≤ 3393 := by
    norm_num at s3; linarith
  calc 1 / Δ₀ * (1120 * ∑ t ∈ range T, (if N ≤ t + 1 then n0 ^ ((1 : ℝ) / 2) *
      ((t : ℝ) + 1) ^ (-((3 : ℝ) / 2)) else 0) + ∑ t ∈ range T, ((t : ℝ) + 1) ^ (-((33 : ℝ) / 32))) ≤
      1 / Δ₀ * 3393 := mul_le_mul_of_nonneg_left hfin (by positivity)
    _ = 3393 / Δ₀ := by ring

end C37

/-! ===== module Final ===== -/

/-! # Assembly of `IAFTRL.lemma_C_37_scalar_moments` -/

namespace C37

open MeasureTheory Finset

/-- the good events -/
def Gfun {K : ℕ} {Ω : Type*} (d : ℕ) (Δ₀ C : ℝ) (κ : ℕ → Ω → ℝ) (X : ℕ → Fin K → Ω → ℝ)
    (jstar : Fin K) (T t : ℕ) : Set Ω :=
  if t < T ∧ Ncf d K Δ₀ C ≤ t + 1 then Gset C κ X jstar (mt d K C t) (θt d K C t) t else ∅

/-- the distortion factors -/
noncomputable def Ψfun (d K : ℕ) (Δ₀ C : ℝ) (t : ℕ) : ℝ :=
  if Ncf d K Δ₀ C ≤ t + 1 then
    1 + (1120 * (n0f d K C / ((t : ℝ) + 1)) ^ ((1 : ℝ) / 2) + ((t : ℝ) + 1) ^ (-(1 : ℝ) / 32)) / Δ₀
  else 1

/-- the failure-sum constant -/
noncomputable def Mfail (d K : ℕ) (Δ₀ : ℝ) : ℝ :=
  IAFTRL.cR d K * (8 * Real.sqrt (Qc d K Δ₀ + 1) +
    8 * 32768 * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt ((Nb d K : ℝ) + 2) +
    2 * (HN d K + K * 2 ^ (Pord K - 1) * (32 / Δ₀) ^ Pord K))

noncomputable def Mbig (d K : ℕ) (Δ₀ : ℝ) : ℝ := 1 + Mfail d K Δ₀ + 1121 / Δ₀ + 3393 / Δ₀

lemma sqrt_add_le' (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    linarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b,
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt h
    _ = _ := Real.sqrt_sq (by positivity)

lemma cR_le (d K : ℕ) (hK : 2 ≤ K) :
    IAFTRL.cR d K ≤ 2 * Real.sqrt ((d : ℝ) * Real.log K) := by
  unfold IAFTRL.cR
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hlog : Real.log (Real.exp 1 * K) = 1 + Real.log K := by
    rw [Real.log_mul (by positivity) hK0.ne', Real.log_exp]
  have hl2 : Real.log 2 ≤ Real.log K := Real.log_le_log (by norm_num) (by exact_mod_cast hK)
  have := Real.log_two_gt_d9
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [hlog]
  calc Real.sqrt ((d : ℝ) * (1 + Real.log K)) ≤ Real.sqrt (2 ^ 2 * ((d : ℝ) * Real.log K)) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = 2 * Real.sqrt ((d : ℝ) * Real.log K) := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

lemma sqrtNc_le (d K : ℕ) (Δ₀ C : ℝ) (hd : 1 ≤ d) (hK : 1 ≤ K) (hΔ₀ : 0 < Δ₀) (hC : 0 ≤ C) :
    Real.sqrt (Ncf d K Δ₀ C) ≤ Real.sqrt (Qc d K Δ₀ + 1) +
      32768 * Δ₀ ^ (-(128 : ℝ) / 255) * (Real.sqrt ((Nb d K : ℝ) + 2) + Real.sqrt C) := by
  have hQ : 0 ≤ Qc d K Δ₀ := by unfold Qc; exact Real.rpow_nonneg (Cbig_pos hd hK hΔ₀).le _
  have hL : 0 ≤ L0 Δ₀ := by unfold L0; positivity
  have hn0 : 0 ≤ (t0f d K C : ℝ) + 1 := by positivity
  have h1 : (Ncf d K Δ₀ C : ℝ) ≤ (Qc d K Δ₀ + 1) + L0 Δ₀ * ((t0f d K C : ℝ) + 1) := by
    have := Nat.ceil_lt_add_one (show 0 ≤ Qc d K Δ₀ + L0 Δ₀ * ((t0f d K C : ℝ) + 1) by positivity)
    unfold Ncf; linarith
  have h2 : Real.sqrt (Ncf d K Δ₀ C) ≤ Real.sqrt (Qc d K Δ₀ + 1) +
      Real.sqrt (L0 Δ₀) * Real.sqrt ((t0f d K C : ℝ) + 1) := by
    calc Real.sqrt (Ncf d K Δ₀ C) ≤ Real.sqrt ((Qc d K Δ₀ + 1) + L0 Δ₀ * ((t0f d K C : ℝ) + 1)) :=
          Real.sqrt_le_sqrt h1
      _ ≤ Real.sqrt (Qc d K Δ₀ + 1) + Real.sqrt (L0 Δ₀ * ((t0f d K C : ℝ) + 1)) :=
          sqrt_add_le' _ _ (by positivity) (by positivity)
      _ = _ := by rw [Real.sqrt_mul hL]
  have h3 : Real.sqrt (L0 Δ₀) ≤ 32768 * Δ₀ ^ (-(128 : ℝ) / 255) := by
    unfold L0
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity), Real.div_rpow (by norm_num) hΔ₀.le]
    have e : (256 : ℝ) / 255 * (1 / 2) = 128 / 255 := by norm_num
    rw [e, div_eq_mul_inv, ← Real.rpow_neg hΔ₀.le, neg_div]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc (32768 : ℝ) ^ ((128 : ℝ) / 255) ≤ 32768 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 32768 := Real.rpow_one _
  have h4 : Real.sqrt ((t0f d K C : ℝ) + 1) ≤ Real.sqrt ((Nb d K : ℝ) + 2) + Real.sqrt C := by
    have e : (t0f d K C : ℝ) + 1 ≤ ((Nb d K : ℝ) + 2) + C := by
      unfold t0f; push_cast
      have := Nat.ceil_lt_add_one hC
      linarith
    calc Real.sqrt ((t0f d K C : ℝ) + 1) ≤ Real.sqrt (((Nb d K : ℝ) + 2) + C) := Real.sqrt_le_sqrt e
      _ ≤ _ := sqrt_add_le' _ _ (by positivity) hC
  have h5 : Real.sqrt (L0 Δ₀) * Real.sqrt ((t0f d K C : ℝ) + 1) ≤
      32768 * Δ₀ ^ (-(128 : ℝ) / 255) * (Real.sqrt ((Nb d K : ℝ) + 2) + Real.sqrt C) :=
    mul_le_mul h3 h4 (Real.sqrt_nonneg _) (by positivity)
  linarith

variable {d K : ℕ} {jstar : Fin K} {Δ : Fin K → ℝ} {Δ₀ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω} {T : ℕ} {C : ℝ} {X D e : ℕ → Fin K → Ω → ℝ}
  {κ : ℕ → Ω → ℝ}

lemma Iface.Gfun_meas (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ) :
    MeasurableSet (Gfun d Δ₀ C κ X jstar T t) := by
  unfold Gfun
  split_ifs with h
  · exact I.Gset_meas _ _ t h.1.le
  · exact MeasurableSet.empty

lemma Iface.Gfun_sep (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ) (ht : t < T) (ω : Ω)
    (hω : ω ∈ Gfun d Δ₀ C κ X jstar T t) (a : Fin K) (ha : a ≠ jstar) :
    4 * ((t : ℝ) + 1) ^ ((3 : ℝ) / 4) ≤ X t a ω := by
  unfold Gfun at hω
  split_ifs at hω with h
  · have h1 := I.Gset_sep _ _ t ω hω a ha
    have h2 := (wh_θ I.hd I.hK I.hΔ₀ I.hΔ₀1 I.hC t h.2).2.2.2.2.2
    linarith
  · exact absurd hω (Set.notMem_empty ω)

set_option maxHeartbeats 1000000 in
lemma Iface.Gfun_fail [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ)
    (ht : t < T) :
    μ.real (Gfun d Δ₀ C κ X jstar T t)ᶜ ≤ if Ncf d K Δ₀ C ≤ t + 1 then
      HN d K * ((t : ℝ) + 1) ^ (-(3 * (Pord K : ℝ) / 16)) +
        (n0f d K C / ((t : ℝ) + 1)) ^ ((Pord K : ℝ) / 256 - qN K) +
        K * 2 ^ (Pord K - 1) * (32 / Δ₀) ^ Pord K * ((t : ℝ) + 1) ^ (-((Pord K : ℝ) / 16)) +
        K * 2 ^ (Pord K - 1) * (8192 / Δ₀) ^ Pord K * (n0f d K C / ((t : ℝ) + 1)) ^ (ωE * Pord K)
      else 1 := by
  have hK := I.hK
  split_ifs with hg
  · have hG : Gfun d Δ₀ C κ X jstar T t = Gset C κ X jstar (mt d K C t) (θt d K C t) t := by
      unfold Gfun; rw [if_pos ⟨ht, hg⟩]
    rw [hG]
    obtain ⟨hθ0, h4C, hθP, -, -, -⟩ := wh_θ I.hd hK I.hΔ₀ I.hΔ₀1 I.hC t hg
    obtain ⟨ht0m, -, -, h2m, hmP, hmt⟩ := wh_m (C := C) I.hd hK I.hΔ₀ I.hΔ₀1 t hg
    obtain ⟨-, -, -, hn0n⟩ := wh_z (C := C) I.hd hK I.hΔ₀ I.hΔ₀1 t hg
    have hburn := Nb_burn (d := d) hK ((t0f d K C : ℝ) + 1) (by linarith [t0f_ge d K C])
    have hCn := C_le_t0 d K C
    have hfb := I.fail_bound (t0f d K C) (mt d K C t) t (θt d K C t) hθ0 ht0m hmt ht.le hburn hCn
      h4C h2m hθP hmP (fun s _ hs => (wh_Q I.hd hK I.hΔ₀ I.hΔ₀1 I.hC t hg s hs.le).1)
      (fun s _ hs => (wh_Q I.hd hK I.hΔ₀ I.hΔ₀1 I.hC t hg s hs.le).2.1)
    have hn1 : (1 : ℝ) ≤ (t : ℝ) + 1 := by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
    have hn0 : (1 : ℝ) ≤ n0f d K C := by unfold n0f; linarith [(Nat.cast_nonneg (t0f d K C) : (0 : ℝ) ≤ _)]
    have hc := fail_conv (Pord K) (qN K) K (Pord_ge K hK) (HN d K) Δ₀ ((t : ℝ) + 1) (n0f d K C)
      (le_trans zero_le_one (le_max_left _ _)) I.hΔ₀ hn1 hn0 hn0n
    have e : nuP K = 3 * (Pord K : ℝ) / 4 := rfl
    rw [e] at hfb
    exact hfb.trans hc
  · rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by
      rw [ENNReal.ofReal_one]; exact prob_le_one)

lemma Iface.Gfun_inv [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ)
    (ht : t < T) (a : Fin K) (ha : a ≠ jstar) :
    Integrable ((Gfun d Δ₀ C κ X jstar T t).indicator
      fun ω => (((t : ℝ) + 1) * Δ a / X t a ω) ^ Pord K) μ ∧
    ∫ ω, (Gfun d Δ₀ C κ X jstar T t).indicator
      (fun ω => (((t : ℝ) + 1) * Δ a / X t a ω) ^ Pord K) ω ∂μ ≤ 8 ^ Pord K := by
  have hK := I.hK
  by_cases hg : Ncf d K Δ₀ C ≤ t + 1
  · have hG : Gfun d Δ₀ C κ X jstar T t = Gset C κ X jstar (mt d K C t) (θt d K C t) t := by
      unfold Gfun; rw [if_pos ⟨ht, hg⟩]
    rw [hG]
    obtain ⟨hθ0, h4C, hθP, -, -, -⟩ := wh_θ I.hd hK I.hΔ₀ I.hΔ₀1 I.hC t hg
    obtain ⟨-, -, -, h2m, hmP, hmt⟩ := wh_m (C := C) I.hd hK I.hΔ₀ I.hΔ₀1 t hg
    exact I.gap_inv (mt d K C t) t (θt d K C t) a ha hθ0 hmt ht.le h4C h2m hθP hmP
      (fun s _ hs => (wh_Q I.hd hK I.hΔ₀ I.hΔ₀1 I.hC t hg s hs.le).1)
      (fun s _ hs => (wh_Q I.hd hK I.hΔ₀ I.hΔ₀1 I.hC t hg s hs.le).2.1)
  · have hG : Gfun d Δ₀ C κ X jstar T t = ∅ := by
      unfold Gfun; rw [if_neg (fun h => hg h.2)]
    rw [hG, Set.indicator_empty]
    exact ⟨integrable_zero _ _ _, by simp⟩

set_option maxHeartbeats 1000000 in
lemma Iface.Gfun_pos [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ)
    (ht : t < T) (a : Fin K) (ha : a ≠ jstar) :
    Integrable ((Gfun d Δ₀ C κ X jstar T t).indicator
      fun ω => (X t a ω / (((t : ℝ) + 1) * Δ a)) ^ Pord K) μ ∧
    ∫ ω, (Gfun d Δ₀ C κ X jstar T t).indicator
      (fun ω => (X t a ω / (((t : ℝ) + 1) * Δ a)) ^ Pord K) ω ∂μ ≤
        (8 * Ψfun d K Δ₀ C t) ^ Pord K := by
  have hK := I.hK
  by_cases hg : Ncf d K Δ₀ C ≤ t + 1
  · have hG : Gfun d Δ₀ C κ X jstar T t = Gset C κ X jstar (mt d K C t) (θt d K C t) t := by
      unfold Gfun; rw [if_pos ⟨ht, hg⟩]
    rw [hG]
    obtain ⟨hθ0, h4C, hθP, -, -, -⟩ := wh_θ I.hd hK I.hΔ₀ I.hΔ₀1 I.hC t hg
    obtain ⟨ht0m, hzm, hmz, h2m, hmP, hmt⟩ := wh_m (C := C) I.hd hK I.hΔ₀ I.hΔ₀1 t hg
    obtain ⟨hzn, -, -, hn0n⟩ := wh_z (C := C) I.hd hK I.hΔ₀ I.hΔ₀1 t hg
    have hΔa : Δ₀ ≤ Δ a := I.hΔge a ha
    have hburn : HG d K ≤ ((mt d K C t : ℝ) + 1) ^ ((Pord K : ℝ) / 4) :=
      Nb_burn (d := d) hK _ (by
        have : (t0f d K C : ℝ) ≤ mt d K C t := by exact_mod_cast ht0m
        linarith [t0f_ge d K C])
    have hW0 := I.init_pos (mt d K C t) (θt d K C t) a hθ0 (by omega) hburn
    have hk := kK_pos K hK
    have hC := I.hC
    have hw0 : 0 < 2 * ((16 * kK K + 1) * ((mt d K C t : ℝ) + 1) + 4 * C + 2 * θt d K C t) := by
      positivity
    have hA0 : 0 ≤ Δ a + Δ₀ / 2 := by have := I.hΔ₀; linarith
    have hpos := I.gap_pos (mt d K C t) t (θt d K C t) a ha hθ0 hmt ht.le
      (fun s _ hs => (wh_Q I.hd hK I.hΔ₀ I.hΔ₀1 I.hC t hg s hs.le).1) (Δ a + Δ₀ / 2) hA0
      (fun s _ hs => by have := (wh_Q I.hd hK I.hΔ₀ I.hΔ₀1 I.hC t hg s hs.le).2.2; linarith)
      _ hw0 hW0
    refine ⟨hpos.1, hpos.2.trans ?_⟩
    have hn1 : (1 : ℝ) ≤ (t : ℝ) + 1 := by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
    have hn02 : (2 : ℝ) ≤ n0f d K C := by
      have := n0f_ge d K C hK
      have : (512 : ℝ) ≤ Pord K := by exact_mod_cast Pord_ge K hK
      linarith
    have hconv := pos_conv (Pord K) (kK K) (kap0 K) (Δ a) Δ₀ C ((t : ℝ) + 1) (n0f d K C) (mt d K C t)
      (kfac_ge K hK) (kK_lt K hK) (kap0_nonneg K hK) (kap0_le K hK) I.hΔ₀ hΔa hC
      (by unfold n0f; exact C_le_t0 d K C) hn02 hn1 hn0n hzm hmz hzn
    have hΨ : Ψfun d K Δ₀ C t = 1 + (1120 * (n0f d K C / ((t : ℝ) + 1)) ^ ((1 : ℝ) / 2) +
        ((t : ℝ) + 1) ^ (-(1 : ℝ) / 32)) / Δ₀ := by unfold Ψfun; rw [if_pos hg]
    rw [hΨ]
    exact hconv
  · have hG : Gfun d Δ₀ C κ X jstar T t = ∅ := by
      unfold Gfun; rw [if_neg (fun h => hg h.2)]
    rw [hG, Set.indicator_empty]
    refine ⟨integrable_zero _ _ _, ?_⟩
    simp only [integral_zero]
    have : Ψfun d K Δ₀ C t = 1 := by unfold Ψfun; rw [if_neg hg]
    rw [this]; positivity

end C37

namespace IAFTRL

open MeasureTheory

set_option maxHeartbeats 2000000 in
theorem _root_.solution : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {d K : ℕ}, 1 ≤ d → ∀ (jstar : Fin K) (Δ : Fin K → ℝ) (Δ₀ : ℝ), 0 < Δ₀ → Δ₀ ≤ 1 →
      Δ jstar = 0 → (∀ a, a ≠ jstar → Δ₀ ≤ Δ a) → (∀ a, Δ a ≤ 2) →
      ∃ M : ℝ, ∀ {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (F : ℕ → MeasurableSpace Ω) (T : ℕ) (C : ℝ) (X D e : ℕ → Fin K → Ω → ℝ)
        (κ : ℕ → Ω → ℝ), 1 ≤ T → 0 ≤ C →
        (∀ t < T, F t ≤ mΩ ∧ F t ≤ F (t + 1)) →
        (∀ a ω, X 0 a ω = 0) → (∀ t a ω, X (t + 1) a ω = X t a ω + D t a ω) →
        (∀ t ω, D t jstar ω = 0) →
        (∀ t < T, ∀ a, Measurable[F (t + 1)] (D t a) ∧ Measurable (D t a)) →
        (∀ t < T, Measurable[F t] (κ t) ∧ ∀ a, Measurable[F t] (e t a)) →
        (∀ t < T, ∀ ω, 0 ≤ κ t ω ∧ κ t ω ≤ 2 ∧
          ∀ a, |e t a ω| ≤ 2 * κ t ω ∧ |Δ a + e t a ω| ≤ 2) →
        (∀ᵐ ω ∂P, ∑ t ∈ Finset.range T, κ t ω ≤ C) →
        (∀ t < T, ∀ a, P[D t a | F t] =ᵐ[P] fun ω => Δ a + e t a ω) →
        (∀ t < T, ∀ a ω, |D t a ω| ≤ 2 * beta d K (t + 1) +
          ((X t a ω - ⨅ b, X t b ω) + (X t jstar ω - ⨅ b, X t b ω)) / Bc K) →
        (∀ t < T, ∀ a, P[fun ω => D t a ω ^ 2 | F t] ≤ᵐ[P] fun ω => 4 * beta d K (t + 1) +
          2 * ((X t a ω - ⨅ b, X t b ω) ^ 2 + (X t jstar ω - ⨅ b, X t b ω) ^ 2) /
            (Bc K * ((t : ℝ) + 1))) →
        ∃ (G : ℕ → Set Ω) (p : ℕ) (Ψ : ℕ → ℝ), (∀ t, MeasurableSet (G t)) ∧
          8 ≤ p ∧ (K : ℝ) ≤ 2 ^ p ∧
          (∀ t < T, ∀ ω ∈ G t, ∀ a, a ≠ jstar → 4 * (t + 1 : ℝ) ^ ((3 : ℝ) / 4) ≤ X t a ω) ∧
          cR d K * ∑ t ∈ Finset.range T, (P (G t)ᶜ).toReal / Real.sqrt (t + 1) ≤
            c₀ * (Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C) +
              M ∧
          (∀ t < T, ∀ a, a ≠ jstar →
            Integrable ((G t).indicator fun ω => ((t + 1 : ℝ) * Δ a / X t a ω) ^ p) P ∧
            ∫ ω, (G t).indicator (fun ω => ((t + 1 : ℝ) * Δ a / X t a ω) ^ p) ω ∂P ≤ 8 ^ p) ∧
          (∀ t < T, ∀ a, a ≠ jstar →
            Integrable ((G t).indicator fun ω => (X t a ω / ((t + 1 : ℝ) * Δ a)) ^ p) P ∧
            ∫ ω, (G t).indicator (fun ω => (X t a ω / ((t + 1 : ℝ) * Δ a)) ^ p) ω ∂P ≤
              (8 * Ψ t) ^ p) ∧
          (∀ t < T, 1 ≤ Ψ t ∧ Ψ t ≤ M) ∧
          ∑ t ∈ Finset.range T, (Ψ t - 1) / (t + 1) ≤ M := by
  refine ⟨524288, by norm_num, ?_⟩
  intro d K hd jstar Δ Δ₀ hΔ₀ hΔ₀1 hΔj hΔge hΔ2
  have hK : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (fun h => (h ▸ jstar).elim0)
  by_cases hK2 : 2 ≤ K
  · refine ⟨C37.Mbig d K Δ₀, ?_⟩
    intro Ω mΩ P hP F T C X D e κ hT hC hfilt hX0 hXs hDj hDm hκm hκb hκsum hmean hmag hsec
    have I : C37.Iface d K jstar Δ Δ₀ P F T C X D e κ :=
      { hd := hd, hΔ₀ := hΔ₀, hΔ₀1 := hΔ₀1, hΔj := hΔj, hΔge := hΔge, hΔ2 := hΔ2, hT := hT,
        hC := hC, filt := hfilt, X0 := hX0, Xs := hXs, Dj := hDj, Dm := hDm, κm := hκm,
        κb := hκb, κsum := hκsum, mean := hmean, mag := hmag, sec := hsec }
    have hMf0 : 0 ≤ C37.Mfail d K Δ₀ := by
      unfold C37.Mfail
      have hHN : 0 ≤ C37.HN d K := le_trans zero_le_one (le_max_left _ _)
      refine mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (add_nonneg (by positivity) (by positivity))
        (mul_nonneg (by norm_num) (add_nonneg hHN (by positivity))))
    refine ⟨C37.Gfun d Δ₀ C κ X jstar T, C37.Pord K, C37.Ψfun d K Δ₀ C, fun t => I.Gfun_meas t,
      by have := C37.Pord_ge K hK; omega, C37.K_le_two_pow K hK, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht ω hω a ha
      exact I.Gfun_sep t ht ω hω a ha
    · -- the failure sum
      set Nc := C37.Ncf d K Δ₀ C with hNc
      set n0 := C37.n0f d K C with hn0def
      have hn0 : (1 : ℝ) ≤ n0 := by
        simp only [n0, C37.n0f]; linarith [(Nat.cast_nonneg (C37.t0f d K C) : (0 : ℝ) ≤ _)]
      have hn0N : n0 ≤ (Nc : ℝ) := C37.good_n1 hd hK hΔ₀ hΔ₀1 _ le_rfl
      have hN1 : 1 ≤ Nc := by
        have : (1 : ℝ) ≤ Nc := le_trans hn0 hn0N
        exact_mod_cast this
      have hNL := C37.good_rho hd hK hΔ₀ (Nc : ℝ) (by exact_mod_cast hN1) (le_refl _)
      have hq : (C37.qN K : ℝ) ≤ (C37.Pord K : ℝ) / 4000 + 1 := by
        have h1 := Nat.ceil_lt_add_one (C37.vN_nonneg K hK)
        have h2 := C37.vN_le K hK
        unfold C37.qN; linarith
      have hsum := C37.fail_sum (C37.Pord K) (C37.qN K) K (C37.Pord_ge K hK) hq
        (C37.K_le_two_pow K hK) (C37.HN d K) Δ₀ n0 (le_trans zero_le_one (le_max_left _ _)) hΔ₀
        hn0 Nc hN1 hn0N hNL T (fun t => P.real (C37.Gfun d Δ₀ C κ X jstar T t)ᶜ)
        (fun t => measureReal_nonneg) (fun t ht => I.Gfun_fail t ht)
      have hsq := C37.sqrtNc_le d K Δ₀ C hd hK hΔ₀ hC
      have hcR := C37.cR_le d K hK2
      have hcR0 : 0 ≤ cR d K := Real.sqrt_nonneg _
      have e1 : ∀ t : ℕ, (P (C37.Gfun d Δ₀ C κ X jstar T t)ᶜ).toReal / Real.sqrt ((t : ℝ) + 1) =
          P.real (C37.Gfun d Δ₀ C κ X jstar T t)ᶜ / Real.sqrt ((t : ℝ) + 1) := fun t => rfl
      simp only [e1]
      set S := ∑ t ∈ Finset.range T, P.real (C37.Gfun d Δ₀ C κ X jstar T t)ᶜ / Real.sqrt ((t : ℝ) + 1)
      set A3 := (K : ℝ) * 2 ^ (C37.Pord K - 1) * (32 / Δ₀) ^ C37.Pord K with hA3
      set E := Δ₀ ^ (-(128 : ℝ) / 255) with hE
      have hE0 : 0 ≤ E := by positivity
      have hS : S ≤ 8 * (Real.sqrt (C37.Qc d K Δ₀ + 1) +
          32768 * E * (Real.sqrt ((C37.Nb d K : ℝ) + 2) + Real.sqrt C)) + 2 * (C37.HN d K + A3) := by
        linarith
      have hS0 : 0 ≤ 8 * (Real.sqrt (C37.Qc d K Δ₀ + 1) +
          32768 * E * (Real.sqrt ((C37.Nb d K : ℝ) + 2) + Real.sqrt C)) + 2 * (C37.HN d K + A3) := by
        have : 0 ≤ C37.HN d K := le_trans zero_le_one (le_max_left _ _)
        positivity
      have h1 := mul_le_mul_of_nonneg_left hS hcR0
      have e2 : cR d K * (8 * (Real.sqrt (C37.Qc d K Δ₀ + 1) +
          32768 * E * (Real.sqrt ((C37.Nb d K : ℝ) + 2) + Real.sqrt C)) + 2 * (C37.HN d K + A3)) =
          cR d K * (8 * 32768) * (E * Real.sqrt C) + C37.Mfail d K Δ₀ := by
        unfold C37.Mfail; rw [← hE, ← hA3]; ring
      have h2 : cR d K * (8 * 32768) * (E * Real.sqrt C) ≤
          524288 * (Real.sqrt ((d : ℝ) * Real.log K) * E * Real.sqrt C) := by
        have h3 : 0 ≤ E * Real.sqrt C := by positivity
        have := mul_le_mul_of_nonneg_right hcR (by positivity : (0 : ℝ) ≤ (8 * 32768) * (E * Real.sqrt C))
        linarith
      have hM : C37.Mfail d K Δ₀ ≤ C37.Mbig d K Δ₀ := by
        unfold C37.Mbig; have : 0 ≤ 1121 / Δ₀ := by positivity
        have : 0 ≤ 3393 / Δ₀ := by positivity
        linarith
      linarith
    · intro t ht a ha
      exact I.Gfun_inv t ht a ha
    · intro t ht a ha
      exact I.Gfun_pos t ht a ha
    · intro t _
      unfold C37.Ψfun
      split_ifs with hg
      · have hn0p : 0 ≤ C37.n0f d K C := by unfold C37.n0f; positivity
        have h1 : 0 ≤ (C37.n0f d K C / ((t : ℝ) + 1)) ^ ((1 : ℝ) / 2) :=
          Real.rpow_nonneg (div_nonneg hn0p (by positivity)) _
        have h2 : (C37.n0f d K C / ((t : ℝ) + 1)) ^ ((1 : ℝ) / 2) ≤ 1 := by
          obtain ⟨-, -, -, hn0n⟩ := C37.wh_z (C := C) hd hK hΔ₀ hΔ₀1 t hg
          exact Real.rpow_le_one (by unfold C37.n0f; positivity)
            (by rw [div_le_one (by positivity)]; exact hn0n) (by norm_num)
        have h3 : 0 ≤ ((t : ℝ) + 1) ^ (-(1 : ℝ) / 32) := by positivity
        have h4 : ((t : ℝ) + 1) ^ (-(1 : ℝ) / 32) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)])
            (by norm_num)
        have h5 : (1120 * (C37.n0f d K C / ((t : ℝ) + 1)) ^ ((1 : ℝ) / 2) +
            ((t : ℝ) + 1) ^ (-(1 : ℝ) / 32)) / Δ₀ ≤ 1121 / Δ₀ :=
          div_le_div_of_nonneg_right (by linarith) hΔ₀.le
        have h6 : 0 ≤ (1120 * (C37.n0f d K C / ((t : ℝ) + 1)) ^ ((1 : ℝ) / 2) +
            ((t : ℝ) + 1) ^ (-(1 : ℝ) / 32)) / Δ₀ := by positivity
        unfold C37.Mbig
        have : 0 ≤ 3393 / Δ₀ := by positivity
        constructor <;> linarith
      · unfold C37.Mbig
        have : 0 ≤ 1121 / Δ₀ := by positivity
        have : 0 ≤ 3393 / Δ₀ := by positivity
        constructor <;> linarith
    · have hn0 : (1 : ℝ) ≤ C37.n0f d K C := by
        unfold C37.n0f; linarith [(Nat.cast_nonneg (C37.t0f d K C) : (0 : ℝ) ≤ _)]
      have hn0N : C37.n0f d K C ≤ (C37.Ncf d K Δ₀ C : ℝ) := C37.good_n1 hd hK hΔ₀ hΔ₀1 _ le_rfl
      have hN1 : 1 ≤ C37.Ncf d K Δ₀ C := by
        have : (1 : ℝ) ≤ C37.Ncf d K Δ₀ C := le_trans hn0 hn0N
        exact_mod_cast this
      have h := C37.psi_sum Δ₀ (C37.n0f d K C) hΔ₀ hn0 (C37.Ncf d K Δ₀ C) hN1 hn0N T
      have e : ∀ t : ℕ, (C37.Ψfun d K Δ₀ C t - 1) / ((t : ℝ) + 1) =
          ((if C37.Ncf d K Δ₀ C ≤ t + 1 then 1 + (1120 * (C37.n0f d K C / ((t : ℝ) + 1)) ^ ((1 : ℝ) / 2) +
            ((t : ℝ) + 1) ^ (-(1 : ℝ) / 32)) / Δ₀ else 1) - 1) / ((t : ℝ) + 1) := fun t => rfl
      simp only [e]
      unfold C37.Mbig
      have : 0 ≤ 1121 / Δ₀ := by positivity
      linarith
  · -- a single action: nothing to separate
    have hK1 : K = 1 := by omega
    refine ⟨1, ?_⟩
    intro Ω mΩ P hP F T C X D e κ hT hC hfilt hX0 hXs hDj hDm hκm hκb hκsum hmean hmag hsec
    have hne : ∀ a : Fin K, a ≠ jstar → False := fun a ha =>
      ha (Fin.ext (by have := a.isLt; have := jstar.isLt; omega))
    refine ⟨fun _ => Set.univ, C37.Pord K, fun _ => 1, fun _ => MeasurableSet.univ,
      by have := C37.Pord_ge K hK; omega, C37.K_le_two_pow K hK,
      fun t _ ω _ a ha => (hne a ha).elim, ?_, fun t _ a ha => (hne a ha).elim,
      fun t _ a ha => (hne a ha).elim, fun t _ => ⟨le_rfl, le_rfl⟩, ?_⟩
    · simp only [Set.compl_univ, measure_empty, ENNReal.toReal_zero, zero_div,
        Finset.sum_const_zero, mul_zero]
      have : 0 ≤ (524288 : ℝ) * (Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) *
          Real.sqrt C) := by positivity
      linarith
    · simp

end IAFTRL


