-- Prove2me | solution 1 for IAFTRL.lemma_C_37_window
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T15:54:10.762377+00:00
-- url     : https://prove2.me/submissions/aa0e48ee-525d-4969-9f85-29c9722814d5

import Mathlib
import Definitions.Def_IAFTRL_beta
import Definitions.Def_IAFTRL_Bc
import Definitions.Def_IAFTRL_cR
import Definitions.Def_IAFTRL_C37_scalar
import Theorems.Thm_IAFTRL_lemma_C_37_abs_moments

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

set_option maxHeartbeats 1000000 in
/-- the two-branch curvature bound (C.215)–(C.217) -/
lemma neg_case (d K : ℕ) (hd : 1 ≤ d) (hK : 1 ≤ K) (n β A N : ℝ) (hn : 1 ≤ n) (hβ16 : 16 ≤ β)
    (hβC : β ≤ Cb d K * Real.sqrt n) (hN0 : 0 ≤ N) (hNA : N ≤ A) (hAN : A ≤ kK K * N) :
    ((Pord K : ℝ) * (Pord K - 1) / 2) * kK K ^ 2 *
        (A + kK K * (3 * β + 2 * N / IAFTRL.Bc K)) ^ (Pord K - 2) *
        (6 * β + 2 * ((N + 4 / 3 * (3 * β + 2 * N / IAFTRL.Bc K)) ^ 2 + N ^ 2) /
          (IAFTRL.Bc K * n)) ≤
      cminus d K * Real.sqrt n * A ^ (Pord K - 2) + aminus K * A ^ Pord K / n +
        Dminus d K * n ^ (hP K - 1) * Real.sqrt n := by
  set P := Pord K with hPdef
  set k := kK K with hk
  set B := IAFTRL.Bc K with hB
  have hP512 := Pord_ge K hK
  have hPr : (512 : ℝ) ≤ P := by exact_mod_cast hP512
  have hk1 : 1 ≤ k := kfac_ge K hK
  have hk2 : k < 2 := kK_lt2 K hK
  have hBpos : 0 < B := Bc_pos K hK
  have hBge : 2 ^ 24 * (P : ℝ) ≤ B := Bc_ge K hK
  have hsq : 1 ≤ Real.sqrt n := by
    have := Real.sqrt_le_sqrt hn; simpa using this
  have hn0 : 0 < n := by linarith
  have hCb := Cb_ge16 d K hd
  have hc0 : (0 : ℝ) ≤ (P : ℝ) * (P - 1) / 2 := by nlinarith
  have hcP : (P : ℝ) * (P - 1) / 2 * 2 ≤ (P : ℝ) ^ 2 := by linarith
  have hβ0 : 0 ≤ β := by linarith
  have hA : 0 ≤ A := le_trans hN0 hNA
  set δ := 3 * β + 2 * N / B with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hT1 : 0 ≤ cminus d K * Real.sqrt n * A ^ (P - 2) := by unfold cminus; positivity
  have hT2 : 0 ≤ aminus K * A ^ P / n := by unfold aminus; positivity
  have hT3 : 0 ≤ Dminus d K * n ^ (hP K - 1) * Real.sqrt n := by
    unfold Dminus wminus; positivity
  rcases le_or_gt (12 * P * k * β) A with hbig | hsmall
  · -- large branch
    have hkpos : (0 : ℝ) < k := by linarith
    have h8 : (8 : ℝ) * P * k ≤ B := by
      have := mul_le_mul_of_nonneg_left hk2.le (by positivity : (0 : ℝ) ≤ 8 * P)
      have : (8 : ℝ) * P * 2 ≤ 2 ^ 24 * P := by linarith
      linarith
    have hβN : β * (12 * P) ≤ N := by
      have h := hbig.trans hAN
      by_contra hc
      have := mul_lt_mul_of_pos_left (not_le.mp hc) hkpos
      linarith
    have h2N : 2 * N / B ≤ N / (1024 * P) := by
      rw [div_le_div_iff₀ hBpos (by positivity)]
      have h2048 : (2048 : ℝ) * P ≤ B := by linarith
      have := mul_le_mul_of_nonneg_left h2048 hN0
      linarith
    have hδN : 4 / 3 * δ ≤ N / 100 := by
      have e1 : 4 * β ≤ N / 1000 := by
        rw [le_div_iff₀ (by norm_num)]
        have : (1000 : ℝ) * 4 ≤ 12 * P := by linarith
        have := mul_le_mul_of_nonneg_left this hβ0
        linarith
      have e2 : N / (1024 * P) ≤ N / 500000 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have : (500000 : ℝ) ≤ 1024 * P := by linarith
        have := mul_le_mul_of_nonneg_left this hN0
        linarith
      simp only [hδ]
      linarith
    have hV1 : (N + 4 / 3 * δ) ^ 2 + N ^ 2 ≤ 3 * A ^ 2 := by
      have h1 : N + 4 / 3 * δ ≤ 101 / 100 * N := by linarith
      have h2 : (N + 4 / 3 * δ) ^ 2 ≤ (101 / 100 * N) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      have h3 : N ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hN0 hNA 2
      have e : (101 / 100 * N) ^ 2 = 10201 / 10000 * N ^ 2 := by ring
      have : 0 ≤ N ^ 2 := sq_nonneg N
      linarith
    have hV : 6 * β + 2 * ((N + 4 / 3 * δ) ^ 2 + N ^ 2) / (B * n) ≤
        6 * Cb d K * Real.sqrt n + 6 * A ^ 2 / (B * n) := by
      have : 2 * ((N + 4 / 3 * δ) ^ 2 + N ^ 2) / (B * n) ≤ 6 * A ^ 2 / (B * n) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      have e : 6 * Cb d K * Real.sqrt n = 6 * (Cb d K * Real.sqrt n) := by ring
      linarith
    have hbase : A + k * δ ≤ (1 + 1 / (2 * P)) * A := by
      have e1 : k * (3 * β) ≤ A / (4 * P) := by
        rw [le_div_iff₀ (by positivity)]
        have : k * (3 * β) * (4 * P) = 12 * P * k * β := by ring
        linarith
      have e2 : k * (2 * N / B) ≤ A / (4 * P) := by
        rw [mul_div_assoc', div_le_div_iff₀ hBpos (by positivity)]
        have h1 : 8 * P * k * N ≤ 8 * P * k * A := mul_le_mul_of_nonneg_left hNA (by positivity)
        have h2 : 8 * P * k * A ≤ B * A := mul_le_mul_of_nonneg_right h8 hA
        calc k * (2 * N) * (4 * P) = 8 * P * k * N := by ring
          _ ≤ 8 * P * k * A := h1
          _ ≤ B * A := h2
          _ = A * B := by ring
      have e3 : (1 + 1 / (2 * P)) * A = A + A / (4 * P) + A / (4 * P) := by field_simp; ring
      rw [e3]
      have : k * δ = k * (3 * β) + k * (2 * N / B) := by simp only [hδ]; ring
      linarith
    have hpow : (A + k * δ) ^ (P - 2) ≤ 2 * A ^ (P - 2) := by
      calc (A + k * δ) ^ (P - 2) ≤ ((1 + 1 / (2 * P)) * A) ^ (P - 2) :=
            pow_le_pow_left₀ (by positivity) hbase _
        _ = (1 + 1 / (2 * P)) ^ (P - 2) * A ^ (P - 2) := mul_pow _ _ _
        _ ≤ 2 * A ^ (P - 2) := mul_le_mul_of_nonneg_right (one_add_half_pow P (by omega))
            (by positivity)
    have hAP : A ^ (P - 2) * A ^ 2 = A ^ P := by rw [← pow_add]; congr 1; omega
    calc ((P : ℝ) * (P - 1) / 2) * k ^ 2 * (A + k * δ) ^ (P - 2) *
          (6 * β + 2 * ((N + 4 / 3 * δ) ^ 2 + N ^ 2) / (B * n))
        ≤ ((P : ℝ) * (P - 1) / 2) * k ^ 2 * (2 * A ^ (P - 2)) *
          (6 * Cb d K * Real.sqrt n + 6 * A ^ 2 / (B * n)) := by gcongr
      _ ≤ (P : ℝ) ^ 2 * k ^ 2 * A ^ (P - 2) * (6 * Cb d K * Real.sqrt n + 6 * A ^ 2 / (B * n)) := by
          have : ((P : ℝ) * (P - 1) / 2) * k ^ 2 * (2 * A ^ (P - 2)) ≤
              (P : ℝ) ^ 2 * k ^ 2 * A ^ (P - 2) := by
            have h := mul_le_mul_of_nonneg_right hcP (by positivity : (0 : ℝ) ≤ k ^ 2 * A ^ (P - 2))
            linarith
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = cminus d K * Real.sqrt n * A ^ (P - 2) + aminus K * (A ^ (P - 2) * A ^ 2) / n := by
          have hcp : cminus d K = 6 * (P : ℝ) ^ 2 * k ^ 2 * Cb d K := rfl
          have hap : aminus K = 6 * (P : ℝ) ^ 2 * k ^ 2 / B := rfl
          rw [hcp, hap]; field_simp
      _ ≤ _ := by rw [hAP]; linarith
  · -- small branch
    have hN : N < 12 * P * k * β := lt_of_le_of_lt hNA hsmall
    have hkpos : (0 : ℝ) < k := by linarith
    have hPk : (1 : ℝ) ≤ P * k := by nlinarith
    have hPkβ : β ≤ P * k * β := by
      have := mul_le_mul_of_nonneg_right hPk hβ0
      linarith
    have hδ4 : δ ≤ 4 * β := by
      have : 2 * N / B ≤ β := by
        rw [div_le_iff₀ hBpos]
        have h24 : (24 : ℝ) * P * k ≤ B := by
          have := mul_le_mul_of_nonneg_left hk2.le (by positivity : (0 : ℝ) ≤ 24 * P)
          have : (24 : ℝ) * P * 2 ≤ 2 ^ 24 * P := by linarith
          linarith
        have h1 := mul_le_mul_of_nonneg_right h24 hβ0
        linarith
      simp only [hδ]; linarith
    have hNb : N + 4 / 3 * δ ≤ 18 * P * k * β := by linarith
    have hV1 : (N + 4 / 3 * δ) ^ 2 + N ^ 2 ≤ 500 * P ^ 2 * k ^ 2 * β ^ 2 := by
      have h1 : (N + 4 / 3 * δ) ^ 2 ≤ (18 * P * k * β) ^ 2 := pow_le_pow_left₀ (by positivity) hNb 2
      have h2 : N ^ 2 ≤ (12 * P * k * β) ^ 2 := pow_le_pow_left₀ hN0 hN.le 2
      have e1 : (18 * P * k * β) ^ 2 = 324 * (P ^ 2 * k ^ 2 * β ^ 2) := by ring
      have e2 : (12 * P * k * β) ^ 2 = 144 * (P ^ 2 * k ^ 2 * β ^ 2) := by ring
      have e3 : (500 : ℝ) * P ^ 2 * k ^ 2 * β ^ 2 = 500 * (P ^ 2 * k ^ 2 * β ^ 2) := by ring
      have : 0 ≤ (P : ℝ) ^ 2 * k ^ 2 * β ^ 2 := by positivity
      linarith
    have hβ2 : β ^ 2 ≤ Cb d K ^ 2 * n := by
      have := pow_le_pow_left₀ hβ0 hβC 2
      rw [mul_pow, Real.sq_sqrt hn0.le] at this; exact this
    have hV : 6 * β + 2 * ((N + 4 / 3 * δ) ^ 2 + N ^ 2) / (B * n) ≤ wminus d K * Real.sqrt n := by
      unfold wminus
      have e1 : 2 * ((N + 4 / 3 * δ) ^ 2 + N ^ 2) / (B * n) ≤
          1000 * P ^ 2 * k ^ 2 * Cb d K ^ 2 / B := by
        have h10 : 2 * ((N + 4 / 3 * δ) ^ 2 + N ^ 2) ≤ 1000 * P ^ 2 * k ^ 2 * Cb d K ^ 2 * n := by
          have := mul_le_mul_of_nonneg_left hβ2 (by positivity : (0 : ℝ) ≤ 1000 * P ^ 2 * k ^ 2)
          have e : 1000 * (P : ℝ) ^ 2 * k ^ 2 * Cb d K ^ 2 * n =
            1000 * P ^ 2 * k ^ 2 * (Cb d K ^ 2 * n) := by ring
          linarith
        calc 2 * ((N + 4 / 3 * δ) ^ 2 + N ^ 2) / (B * n) ≤
            (1000 * P ^ 2 * k ^ 2 * Cb d K ^ 2 * n) / (B * n) :=
              div_le_div_of_nonneg_right h10 (by positivity)
          _ = 1000 * P ^ 2 * k ^ 2 * Cb d K ^ 2 / B := by field_simp
      have e2 : 1000 * P ^ 2 * k ^ 2 * Cb d K ^ 2 / B ≤
          1000 * P ^ 2 * k ^ 2 * Cb d K ^ 2 / B * Real.sqrt n :=
        le_mul_of_one_le_right (by positivity) hsq
      have e3 : 6 * β ≤ 6 * Cb d K * Real.sqrt n := by
        have e : 6 * Cb d K * Real.sqrt n = 6 * (Cb d K * Real.sqrt n) := by ring
        linarith
      linarith
    have hbase : A + k * δ ≤ 16 * P * k * β := by
      have h1 : k * δ ≤ k * (4 * β) := mul_le_mul_of_nonneg_left hδ4 hkpos.le
      have h2 : k * (4 * β) ≤ 4 * (P * k * β) := by
        have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ P by linarith)
          (by positivity : (0 : ℝ) ≤ k * β)
        linarith
      linarith
    have hβn : 16 * P * k * β ≤ 16 * P * k * Cb d K * Real.sqrt n := by
      have := mul_le_mul_of_nonneg_left hβC (by positivity : (0 : ℝ) ≤ 16 * P * k)
      have e : 16 * (P : ℝ) * k * Cb d K * Real.sqrt n = 16 * P * k * (Cb d K * Real.sqrt n) := by ring
      linarith
    have hpow : (A + k * δ) ^ (P - 2) ≤ (16 * P * k * Cb d K) ^ (P - 2) * n ^ (hP K - 1) := by
      have hsqn : Real.sqrt n ^ (P - 2) = n ^ (hP K - 1) := by
        have : P - 2 = 2 * (hP K - 1) := by rw [hPdef, Pord_eq]; have := hP_ge K hK; omega
        rw [this, pow_mul, Real.sq_sqrt hn0.le]
      calc (A + k * δ) ^ (P - 2) ≤ (16 * P * k * Cb d K * Real.sqrt n) ^ (P - 2) :=
            pow_le_pow_left₀ (by positivity) (hbase.trans hβn) _
        _ = (16 * P * k * Cb d K) ^ (P - 2) * n ^ (hP K - 1) := by rw [mul_pow, hsqn]
    have hmain : ((P : ℝ) * (P - 1) / 2) * k ^ 2 * (A + k * δ) ^ (P - 2) *
        (6 * β + 2 * ((N + 4 / 3 * δ) ^ 2 + N ^ 2) / (B * n)) ≤
          Dminus d K * n ^ (hP K - 1) * Real.sqrt n := by
      calc ((P : ℝ) * (P - 1) / 2) * k ^ 2 * (A + k * δ) ^ (P - 2) *
            (6 * β + 2 * ((N + 4 / 3 * δ) ^ 2 + N ^ 2) / (B * n))
          ≤ ((P : ℝ) * (P - 1) / 2) * k ^ 2 * ((16 * P * k * Cb d K) ^ (P - 2) * n ^ (hP K - 1)) *
            (wminus d K * Real.sqrt n) := by gcongr
        _ = Dminus d K * n ^ (hP K - 1) * Real.sqrt n := by unfold Dminus; ring
    linarith

set_option maxHeartbeats 1000000 in
/-- the deterministic one-step negative-moment inequality (C.218) with its linearization (C.220) -/
lemma neg_alg (d K : ℕ) (hd : 1 ≤ d) (hK : 1 ≤ K) (n β : ℝ) (hn : 1 ≤ n) (hβ16 : 16 ≤ β)
    (hβC : β ≤ Cb d K * Real.sqrt n) (y : Fin K → ℝ) (N : ℝ) (hN0 : 0 ≤ N)
    (hyN : ∀ a, y a ≤ N) (hNA : N ≤ Aroot (vpos y)) :
    ∑ a, vpos y a ^ Pord K + ∑ a, ((Pord K : ℝ) * (Pord K - 1) / 2) *
        (max ((1 - 1 / IAFTRL.Bc K) * y a + (3 * β + 2 * N / IAFTRL.Bc K)) 0) ^ (Pord K - 2) *
        (6 * β + 2 * ((N - y a) ^ 2 + N ^ 2) / (IAFTRL.Bc K * n)) ≤
      (1 + vN K / n) * ∑ a, vpos y a ^ Pord K + J0 d K * n ^ (nuP K - 1) := by
  set P := Pord K with hPdef
  set k := kK K with hk
  set B := IAFTRL.Bc K with hB
  set v := vpos y with hv
  set A := Aroot v with hAdef
  have hP512 := Pord_ge K hK
  have hPr : (512 : ℝ) ≤ P := by exact_mod_cast hP512
  have hev := Pord_even K
  have hk1 : 1 ≤ k := kfac_ge K hK
  have hBpos : 0 < B := Bc_pos K hK
  have hBge : 2 ^ 24 * (P : ℝ) ≤ B := Bc_ge K hK
  have hn0 : 0 < n := by linarith
  have hA : 0 ≤ A := Aroot_nonneg v
  have hv0 : ∀ a, 0 ≤ v a := fun a => le_max_right _ _
  have hS : ∑ a, v a ^ P = A ^ P := (root_pow v P (by omega) hev).symm
  have hc0 : (0 : ℝ) ≤ (P : ℝ) * (P - 1) / 2 := by nlinarith
  have hβ0 : 0 ≤ β := by linarith
  -- `A ≤ k N`
  have hAN : A ≤ k * N := by
    have h1 : ∑ b, v b ^ P ≤ (K : ℝ) * N ^ P := by
      calc ∑ b, v b ^ P ≤ ∑ _b : Fin K, N ^ P := sum_le_sum fun b _ =>
            pow_le_pow_left₀ (hv0 b) (max_le (hyN b) hN0) _
        _ = K * N ^ P := by simp
    have hPpos : (0 : ℝ) < P := by linarith
    calc A = (∑ b, v b ^ P) ^ ((1 : ℝ) / P) := rfl
      _ ≤ ((K : ℝ) * N ^ P) ^ ((1 : ℝ) / P) :=
          Real.rpow_le_rpow (sum_nonneg fun b _ => pow_nonneg (hv0 b) _) h1 (by positivity)
      _ = k * N := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
            ← Real.rpow_mul hN0, mul_one_div_cancel hPpos.ne', Real.rpow_one]
          rfl
  set δ := 3 * β + 2 * N / B with hδ
  have hδ0 : 0 ≤ δ := by positivity
  set Vm := 6 * β + 2 * ((N + 4 / 3 * δ) ^ 2 + N ^ 2) / (B * n) with hVm
  have hVm0 : 0 ≤ Vm := by positivity
  -- per-coordinate bound
  have hper : ∀ a, ((P : ℝ) * (P - 1) / 2) * (max ((1 - 1 / B) * y a + δ) 0) ^ (P - 2) *
      (6 * β + 2 * ((N - y a) ^ 2 + N ^ 2) / (B * n)) ≤
      ((P : ℝ) * (P - 1) / 2) * Vm * (|v a| + δ) ^ (P - 2) := by
    intro a
    have hB1 : 1 / B ≤ 1 / 4 := by
      rw [div_le_div_iff₀ hBpos (by norm_num)]; linarith
    rcases le_or_gt ((1 - 1 / B) * y a + δ) 0 with hneg | hpos
    · rw [max_eq_right hneg, zero_pow (by omega), mul_zero, zero_mul]
      positivity
    · rw [max_eq_left hpos.le, abs_of_nonneg (hv0 a)]
      have hcv : (1 - 1 / B) * y a + δ ≤ v a + δ := by
        have : (1 - 1 / B) * y a ≤ v a := by
          rcases le_or_gt 0 (y a) with hy | hy
          · have : v a = y a := max_eq_left hy
            rw [this]
            have : 0 ≤ 1 / B * y a := by positivity
            linarith
          · have : (1 - 1 / B) * y a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hy.le
            linarith [hv0 a]
        linarith
      have hya : -(4 / 3 * δ) ≤ y a := by
        by_contra hcon
        have hcon := not_le.mp hcon
        have : (1 - 1 / B) * y a ≤ (3 / 4) * y a := by
          have : (1 - 1 / B) ≥ 3 / 4 := by linarith
          nlinarith
        linarith
      have hZ : (N - y a) ^ 2 ≤ (N + 4 / 3 * δ) ^ 2 :=
        pow_le_pow_left₀ (by linarith [hyN a]) (by linarith) 2
      have hVa : 6 * β + 2 * ((N - y a) ^ 2 + N ^ 2) / (B * n) ≤ Vm := by
        have : 2 * ((N - y a) ^ 2 + N ^ 2) ≤ 2 * ((N + 4 / 3 * δ) ^ 2 + N ^ 2) := by linarith
        have := div_le_div_of_nonneg_right this (by positivity : (0 : ℝ) ≤ B * n)
        simp only [hVm]; linarith
      have hp : ((1 - 1 / B) * y a + δ) ^ (P - 2) ≤ (v a + δ) ^ (P - 2) :=
        pow_le_pow_left₀ hpos.le hcv _
      calc ((P : ℝ) * (P - 1) / 2) * ((1 - 1 / B) * y a + δ) ^ (P - 2) *
            (6 * β + 2 * ((N - y a) ^ 2 + N ^ 2) / (B * n))
          ≤ ((P : ℝ) * (P - 1) / 2) * (v a + δ) ^ (P - 2) * Vm :=
            mul_le_mul (mul_le_mul_of_nonneg_left hp hc0) hVa (by positivity)
              (mul_nonneg hc0 (pow_nonneg (by linarith [hv0 a]) _))
        _ = _ := by ring
  have hcurv : ∑ a, ((P : ℝ) * (P - 1) / 2) * (max ((1 - 1 / B) * y a + δ) 0) ^ (P - 2) *
      (6 * β + 2 * ((N - y a) ^ 2 + N ^ 2) / (B * n)) ≤
      ((P : ℝ) * (P - 1) / 2) * k ^ 2 * (A + k * δ) ^ (P - 2) * Vm := by
    calc _ ≤ ∑ a, ((P : ℝ) * (P - 1) / 2) * Vm * (|v a| + δ) ^ (P - 2) := sum_le_sum fun a _ => hper a
      _ = ((P : ℝ) * (P - 1) / 2) * Vm * ∑ a, (|v a| + δ) ^ (P - 2) := by rw [mul_sum]
      _ ≤ ((P : ℝ) * (P - 1) / 2) * Vm * (k ^ 2 * (A + k * δ) ^ (P - 2)) :=
          mul_le_mul_of_nonneg_left (abs_curv K hK v δ hδ0) (by positivity)
      _ = _ := by ring
  have hcase := neg_case d K hd hK n β A N hn hβ16 hβC hN0 hNA hAN
  rw [← hPdef, ← hk, ← hB, ← hδ, ← hVm] at hcase
  have hcp : 0 < cminus d K := by
    unfold cminus; have := Cb_ge16 d K hd; rw [← hk, ← hPdef]; positivity
  have hLam : 0 < Lam K := by unfold Lam; rw [← hPdef]; positivity
  have hlin2 : cminus d K * Real.sqrt n * A ^ (P - 2) ≤ (Lam K / n) * A ^ P +
      cminus d K * (cminus d K / Lam K) ^ (hP K - 1) * n ^ (nuP K - 1) := by
    set R2 := cminus d K / Lam K * (n * Real.sqrt n) with hR2
    have hR2pos : 0 < R2 := by positivity
    have h := lin_pow (cminus d K * Real.sqrt n) A (Real.sqrt R2) (P - 2) P (by positivity) hA
      (Real.sqrt_pos.mpr hR2pos) (by omega)
    have e1 : P - (P - 2) = 2 := by omega
    rw [e1, Real.sq_sqrt hR2pos.le] at h
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have e2 : cminus d K * Real.sqrt n / R2 = Lam K / n := by
      rw [hR2]; field_simp
    have e3 : Real.sqrt R2 ^ (P - 2) = R2 ^ (hP K - 1) := by
      have : P - 2 = 2 * (hP K - 1) := by rw [hPdef, Pord_eq]; have := hP_ge K hK; omega
      rw [this, pow_mul, Real.sq_sqrt hR2pos.le]
    have e4 : cminus d K * Real.sqrt n * R2 ^ (hP K - 1) =
        cminus d K * (cminus d K / Lam K) ^ (hP K - 1) * n ^ (nuP K - 1) := by
      rw [hR2, mul_pow, ← nu_pow K hK n hn0]; ring
    rw [e2, e3, e4] at h
    exact h
  have hDn := nu_pow_le K hK n hn
  have hDp : 0 ≤ Dminus d K := by
    unfold Dminus wminus; rw [← hk, ← hPdef, ← hB]; have := Cb_ge16 d K hd; positivity
  have hD := mul_le_mul_of_nonneg_left hDn hDp
  have hvN : vN K = aminus K + Lam K := rfl
  have hJ0 : J0 d K = cminus d K * (cminus d K / Lam K) ^ (hP K - 1) + Dminus d K := rfl
  rw [hS, hvN, hJ0]
  have e6 : (1 + (aminus K + Lam K) / n) * A ^ P = A ^ P + (Lam K / n) * A ^ P + aminus K * A ^ P / n := by
    field_simp; ring
  rw [e6]
  have e7 : Dminus d K * n ^ (hP K - 1) * Real.sqrt n = Dminus d K * (n ^ (hP K - 1) * Real.sqrt n) := by
    ring
  rw [e7] at hcase
  linarith

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

set_option maxHeartbeats 1000000 in
/-- one weighted step of the negative-moment recursion (C.210), for a predictable weight `h ∈ [0,1]` -/
lemma Iface.neg_step [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ)
    (t : ℕ) (ht : t < T) (h : Ω → ℝ) (hh : Measurable[F t] h) (hh0 : ∀ ω, 0 ≤ h ω)
    (hh1 : ∀ ω, h ω ≤ 1) :
    ∫ ω, h ω * Fneg C κ X (t + 1) ω ∂μ ≤
      (1 + vN K / ((t : ℝ) + 1)) * ∫ ω, h ω * Fneg C κ X t ω ∂μ +
        J0 d K * ((t : ℝ) + 1) ^ (nuP K - 1) := by
  have hK := I.hK
  have hP := Pord_ge K hK
  have hPr : (512 : ℝ) ≤ Pord K := by exact_mod_cast hP
  have hev := Pord_even K
  have hB := Bc_pos K hK
  set P := Pord K with hPdef
  set B := IAFTRL.Bc K with hBdef
  set β := IAFTRL.beta d K (t + 1) with hβ
  set n : ℝ := (t : ℝ) + 1 with hn
  have hn1 : (1 : ℝ) ≤ n := by simp only [n]; linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
  have hβ16 : 16 ≤ β := beta_ge16 d K (t + 1) I.hd
  have hβC : β ≤ Cb d K * Real.sqrt n := by
    have := beta_le_Cb d K (t + 1) hK (by omega); push_cast at this; exact this
  have hBge : 2 ^ 24 * (P : ℝ) ≤ B := Bc_ge K hK
  have hmF := (I.filt t ht).1
  set r := ry d K C t with hr
  have hr0 : 0 ≤ r := ry_nonneg d K C t hK I.hd
  set c : ℝ := (P : ℝ) * (P - 1) / 2 with hc
  have hc0 : 0 ≤ c := by simp only [c]; nlinarith
  -- local abbreviations
  let y : Fin K → Ω → ℝ := fun a ω => yN C κ X t a ω
  let N : Ω → ℝ := fun ω => Nn C κ X t ω
  let v : Fin K → Ω → ℝ := fun a ω => max (y a ω) 0
  let ca : Fin K → Ω → ℝ := fun a ω => (1 - 1 / B) * y a ω + (3 * β + 2 * N ω / B)
  let Ct : Fin K → Ω → ℝ := fun a ω => c * (max (ca a ω) 0) ^ (P - 2)
  set rc := r + 3 * β + 2 * r / B with hrc
  have hy : ∀ a ω, |y a ω| ≤ r := fun a ω => I.yN_abs t ht.le a ω
  have hN : ∀ ω, |N ω| ≤ r := fun ω => I.Nn_abs t ht.le ω
  have hv : ∀ a ω, 0 ≤ v a ω ∧ v a ω ≤ r := fun a ω =>
    ⟨le_max_right _ _, max_le ((le_abs_self _).trans (hy a ω)) hr0⟩
  have hca : ∀ a ω, max (ca a ω) 0 ≤ rc := by
    intro a ω
    refine max_le ?_ (by positivity)
    have h1 : (1 - 1 / B) * y a ω ≤ r := by
      have hB1 : 1 / B ≤ 1 := by rw [div_le_one hB]; linarith
      have h0 : 0 ≤ 1 - 1 / B := by linarith
      calc (1 - 1 / B) * y a ω ≤ (1 - 1 / B) * |y a ω| := mul_le_mul_of_nonneg_left (le_abs_self _) h0
        _ ≤ 1 * r := mul_le_mul (by linarith [show 0 ≤ 1 / B by positivity]) (hy a ω) (abs_nonneg _) zero_le_one
        _ = r := one_mul r
    have h2 : 2 * N ω / B ≤ 2 * r / B :=
      div_le_div_of_nonneg_right (by linarith [le_abs_self (N ω), hN ω]) hB.le
    simp only [ca, rc]; linarith
  set cr := c * rc ^ (P - 2) with hcr
  have hCt : ∀ a ω, 0 ≤ Ct a ω ∧ Ct a ω ≤ cr := fun a ω =>
    ⟨mul_nonneg hc0 (pow_nonneg (le_max_right _ _) _),
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_max_right _ _) (hca a ω) _) hc0⟩
  have hvp : ∀ a ω, 0 ≤ v a ω ^ (P - 1) ∧ v a ω ^ (P - 1) ≤ r ^ (P - 1) := fun a ω =>
    ⟨pow_nonneg (hv a ω).1 _, pow_le_pow_left₀ (hv a ω).1 (hv a ω).2 _⟩
  have hvP : ∀ a ω, 0 ≤ v a ω ^ P ∧ v a ω ^ P ≤ r ^ P := fun a ω =>
    ⟨pow_nonneg (hv a ω).1 _, pow_le_pow_left₀ (hv a ω).1 (hv a ω).2 _⟩
  have hκ : ∀ ω, 0 ≤ κ t ω ∧ κ t ω ≤ 2 := fun ω => ⟨(I.κb t ht ω).1, (I.κb t ht ω).2.1⟩
  -- measurability
  have hym : ∀ a, Measurable[F t] (y a) := fun a => I.yN_meas t ht.le a
  have hNm : Measurable[F t] N := I.Nn_meas t ht.le
  have hκm : Measurable[F t] (κ t) := (I.κm t ht).1
  have hvm : ∀ a, Measurable[F t] (v a) := fun a => (hym a).max measurable_const
  have hcam : ∀ a, Measurable[F t] (ca a) := fun a => by
    have hφ : Continuous (fun q : ℝ × ℝ => (1 - 1 / B) * q.1 + (3 * β + 2 * q.2 / B)) := by
      fun_prop
    exact hφ.measurable.comp ((hym a).prodMk hNm)
  have hCtm : ∀ a, Measurable[F t] (Ct a) := fun a =>
    ((hcam a).max measurable_const |>.pow_const _).const_mul _
  -- coefficients
  let g0 : Ω → ℝ := fun ω => h ω * ∑ a, (v a ω ^ P - 2 * κ t ω * P * v a ω ^ (P - 1) +
    4 * κ t ω ^ 2 * Ct a ω)
  let g1 : Fin K → Ω → ℝ := fun a ω => h ω * (-(P : ℝ) * v a ω ^ (P - 1) + 4 * κ t ω * Ct a ω)
  let g2 : Fin K → Ω → ℝ := fun a ω => h ω * Ct a ω
  have hg1m : ∀ a, Measurable[F t] (g1 a) := fun a => by
    have hφ : Continuous (fun q : ℝ × ℝ × ℝ × ℝ => q.1 * (-(P : ℝ) * q.2.1 ^ (P - 1) + 4 * q.2.2.1 * q.2.2.2)) := by
      fun_prop
    exact hφ.measurable.comp (hh.prodMk ((hvm a).prodMk (hκm.prodMk (hCtm a))))
  have hg2m : ∀ a, Measurable[F t] (g2 a) := fun a => hh.mul (hCtm a)
  have hg0m : Measurable[F t] g0 := by
    refine hh.mul (Finset.measurable_sum _ fun a _ => ?_)
    have hφ : Continuous (fun q : ℝ × ℝ × ℝ => q.1 ^ P - 2 * q.2.1 * P * q.1 ^ (P - 1) +
        4 * q.2.1 ^ 2 * q.2.2) := by fun_prop
    exact hφ.measurable.comp ((hvm a).prodMk (hκm.prodMk (hCtm a)))
  have hhabs : ∀ ω, |h ω| ≤ 1 := fun ω => by rw [abs_of_nonneg (hh0 ω)]; exact hh1 ω
  have hg1b : ∀ a ω, |g1 a ω| ≤ P * r ^ (P - 1) + 8 * cr := by
    intro a ω
    simp only [g1]
    rw [abs_mul]
    have h1 : |-(P : ℝ) * v a ω ^ (P - 1) + 4 * κ t ω * Ct a ω| ≤ P * r ^ (P - 1) + 8 * cr := by
      have e1 : 0 ≤ (P : ℝ) * v a ω ^ (P - 1) := mul_nonneg (by positivity) (hvp a ω).1
      have e2 : (P : ℝ) * v a ω ^ (P - 1) ≤ P * r ^ (P - 1) :=
        mul_le_mul_of_nonneg_left (hvp a ω).2 (by positivity)
      have e3 : 0 ≤ 4 * κ t ω * Ct a ω := by have := (hκ ω).1; have := (hCt a ω).1; positivity
      have e4 : 4 * κ t ω * Ct a ω ≤ 8 * cr := by
        have := mul_le_mul (hκ ω).2 (hCt a ω).2 (hCt a ω).1 (by norm_num)
        linarith
      rw [abs_le]; constructor <;> linarith
    have h2 : 0 ≤ P * r ^ (P - 1) + 8 * cr := by positivity
    calc |h ω| * |-(P : ℝ) * v a ω ^ (P - 1) + 4 * κ t ω * Ct a ω| ≤ 1 * (P * r ^ (P - 1) + 8 * cr) :=
          mul_le_mul (hhabs ω) h1 (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hg2b : ∀ a ω, |g2 a ω| ≤ cr := by
    intro a ω
    simp only [g2]
    rw [abs_mul, abs_of_nonneg (hCt a ω).1]
    calc |h ω| * Ct a ω ≤ 1 * cr := mul_le_mul (hhabs ω) (hCt a ω).2 (hCt a ω).1 zero_le_one
      _ = cr := one_mul _
  have hg2n : ∀ a ω, 0 ≤ g2 a ω := fun a ω => mul_nonneg (hh0 ω) (hCt a ω).1
  have hg0b : ∀ ω, |g0 ω| ≤ K * (r ^ P + 4 * P * r ^ (P - 1) + 16 * cr) := by
    intro ω
    simp only [g0]
    rw [abs_mul]
    have hs : |∑ a, (v a ω ^ P - 2 * κ t ω * P * v a ω ^ (P - 1) + 4 * κ t ω ^ 2 * Ct a ω)| ≤
        K * (r ^ P + 4 * P * r ^ (P - 1) + 16 * cr) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      have : ∀ a, |v a ω ^ P - 2 * κ t ω * P * v a ω ^ (P - 1) + 4 * κ t ω ^ 2 * Ct a ω| ≤
          r ^ P + 4 * P * r ^ (P - 1) + 16 * cr := by
        intro a
        have e1 := hvP a ω
        have e2 : 0 ≤ 2 * κ t ω * P * v a ω ^ (P - 1) := by
          have := (hκ ω).1; have := (hvp a ω).1; positivity
        have e3 : 2 * κ t ω * P * v a ω ^ (P - 1) ≤ 4 * P * r ^ (P - 1) := by
          have h1 := mul_le_mul (hκ ω).2 (hvp a ω).2 (hvp a ω).1 (by norm_num)
          have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * P)
          linarith
        have e4 : 0 ≤ 4 * κ t ω ^ 2 * Ct a ω := by have := (hCt a ω).1; positivity
        have e5 : 4 * κ t ω ^ 2 * Ct a ω ≤ 16 * cr := by
          have h1 : κ t ω ^ 2 ≤ 4 := by
            have := pow_le_pow_left₀ (hκ ω).1 (hκ ω).2 2; norm_num at this; linarith
          have := mul_le_mul h1 (hCt a ω).2 (hCt a ω).1 (by norm_num)
          linarith
        rw [abs_le]; constructor <;> linarith
      calc ∑ a, |v a ω ^ P - 2 * κ t ω * P * v a ω ^ (P - 1) + 4 * κ t ω ^ 2 * Ct a ω| ≤
          ∑ _a : Fin K, (r ^ P + 4 * P * r ^ (P - 1) + 16 * cr) := sum_le_sum fun a _ => this a
        _ = _ := by simp; ring
    have h2 : 0 ≤ (K : ℝ) * (r ^ P + 4 * P * r ^ (P - 1) + 16 * cr) := by positivity
    calc |h ω| * |∑ a, (v a ω ^ P - 2 * κ t ω * P * v a ω ^ (P - 1) + 4 * κ t ω ^ 2 * Ct a ω)| ≤
        1 * (K * (r ^ P + 4 * P * r ^ (P - 1) + 16 * cr)) := mul_le_mul (hhabs ω) hs (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  -- integrability of the left side
  have hHint : Integrable (fun ω => h ω * Fneg C κ X (t + 1) ω) μ := by
    refine int_of_bdd μ _ ((hh.mono hmF le_rfl).mul (I.Fneg_meas' (t + 1) ht)) (K * ry d K C (t + 1) ^ P)
      fun ω => ?_
    rw [abs_mul, abs_of_nonneg (Fneg_nonneg _ _ _ _ _)]
    have hF : Fneg C κ X (t + 1) ω ≤ K * ry d K C (t + 1) ^ P := by
      unfold Fneg vpos
      calc ∑ a, max (yN C κ X (t + 1) a ω) 0 ^ P ≤ ∑ _a : Fin K, ry d K C (t + 1) ^ P :=
            sum_le_sum fun a _ => pow_le_pow_left₀ (le_max_right _ _)
              (max_le ((le_abs_self _).trans (I.yN_abs (t + 1) ht a ω))
                (ry_nonneg d K C (t + 1) hK I.hd)) _
        _ = _ := by simp
    calc |h ω| * Fneg C κ X (t + 1) ω ≤ 1 * (K * ry d K C (t + 1) ^ P) :=
          mul_le_mul (hhabs ω) hF (Fneg_nonneg _ _ _ _ _) zero_le_one
      _ = _ := one_mul _
  have hg0int : Integrable g0 μ := int_of_bdd μ _ (hg0m.mono hmF le_rfl) _ hg0b
  -- the pointwise Taylor bound
  have hpt : ∀ᵐ ω ∂μ, h ω * Fneg C κ X (t + 1) ω ≤
      g0 ω + ∑ a, (g1 a ω * D t a ω + g2 a ω * D t a ω ^ 2) := by
    filter_upwards [I.bR_nonneg_ae] with ω hω
    have hb0 : 0 ≤ bR C κ t ω := hω t ht.le
    have hT : Fneg C κ X (t + 1) ω ≤ ∑ a, ((v a ω ^ P - 2 * κ t ω * P * v a ω ^ (P - 1) +
        4 * κ t ω ^ 2 * Ct a ω) + ((-(P : ℝ) * v a ω ^ (P - 1) + 4 * κ t ω * Ct a ω) * D t a ω +
          Ct a ω * D t a ω ^ 2)) := by
      unfold Fneg vpos
      refine sum_le_sum fun a _ => ?_
      dsimp only
      set z := -(2 * κ t ω) - D t a ω with hz
      have hy1 : yN C κ X (t + 1) a ω = y a ω + z := by
        simp only [y, yN, z]; rw [bR_succ, I.Xs]; ring
      rw [hy1]
      have hTay := pos_taylor (y a ω) z P (by omega) hev
      have hzb : |z| ≤ 3 * β + (2 * N ω - y a ω) / B := by
        have hm := I.mag t ht a ω
        have hza := Zx_eq_Nn C κ X t a ω
        have hzs := I.Nn_star t ω
        have hD : |D t a ω| ≤ 2 * β + (2 * N ω - y a ω) / B := by
          have : Zx X t a ω + Zx X t jstar ω ≤ 2 * N ω - y a ω := by
            simp only [N, y]; rw [hza, hzs]; linarith
          have := div_le_div_of_nonneg_right this hB.le
          linarith
        have h4 : |z| ≤ |D t a ω| + 2 * κ t ω := by
          rw [hz]
          have := abs_sub (-(2 * κ t ω)) (D t a ω)
          rw [abs_neg, abs_of_nonneg (by linarith [(hκ ω).1] : (0 : ℝ) ≤ 2 * κ t ω)] at this
          linarith
        linarith [(hκ ω).2]
      have hmax : max (y a ω + |z|) 0 ≤ max (ca a ω) 0 := by
        apply max_le_max _ le_rfl
        have : y a ω + (2 * N ω - y a ω) / B = (1 - 1 / B) * y a ω + 2 * N ω / B := by
          field_simp; ring
        simp only [ca]; linarith
      have hp2 : (max (y a ω + |z|) 0) ^ (P - 2) ≤ (max (ca a ω) 0) ^ (P - 2) :=
        pow_le_pow_left₀ (le_max_right _ _) hmax _
      have hcurv : c * (max (y a ω + |z|) 0) ^ (P - 2) * z ^ 2 ≤ Ct a ω * z ^ 2 := by
        simp only [Ct]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp2 hc0) (sq_nonneg z)
      have e : (max (y a ω) 0) ^ P + P * (max (y a ω) 0) ^ (P - 1) * z + Ct a ω * z ^ 2 =
          (v a ω ^ P - 2 * κ t ω * P * v a ω ^ (P - 1) + 4 * κ t ω ^ 2 * Ct a ω) +
            ((-(P : ℝ) * v a ω ^ (P - 1) + 4 * κ t ω * Ct a ω) * D t a ω + Ct a ω * D t a ω ^ 2) := by
        simp only [v, z]; ring
      have hTay' : (max (y a ω + z) 0) ^ P ≤ (max (y a ω) 0) ^ P + P * (max (y a ω) 0) ^ (P - 1) * z +
          c * (max (y a ω + |z|) 0) ^ (P - 2) * z ^ 2 := hTay
      linarith
    calc h ω * Fneg C κ X (t + 1) ω ≤ h ω * ∑ a, ((v a ω ^ P - 2 * κ t ω * P * v a ω ^ (P - 1) +
        4 * κ t ω ^ 2 * Ct a ω) + ((-(P : ℝ) * v a ω ^ (P - 1) + 4 * κ t ω * Ct a ω) * D t a ω +
          Ct a ω * D t a ω ^ 2)) := mul_le_mul_of_nonneg_left hT (hh0 ω)
      _ = g0 ω + ∑ a, (g1 a ω * D t a ω + g2 a ω * D t a ω ^ 2) := by
          simp only [g0, g1, g2]
          rw [sum_add_distrib, mul_add, mul_sum, mul_sum]
          congr 1
          exact sum_congr rfl fun a _ => by ring
  have hstep := I.step t ht (fun ω => h ω * Fneg C κ X (t + 1) ω) g0 g1 g2 hHint hg0int
    (fun a => (hg1m a).stronglyMeasurable) (fun _ => (P : ℝ) * r ^ (P - 1) + 8 * cr) hg1b
    (fun a => (hg2m a).stronglyMeasurable) (fun _ => cr) hg2b hg2n hpt
  -- bound the right-hand side
  have hrhs : ∀ᵐ ω ∂μ, g0 ω + ∑ a, (g1 a ω * (Δ a + e t a ω) + g2 a ω * Venv d K X jstar t a ω) ≤
      h ω * ((1 + vN K / n) * Fneg C κ X t ω + J0 d K * n ^ (nuP K - 1)) := by
    filter_upwards [I.bR_nonneg_ae] with ω hω
    have hb0 : 0 ≤ bR C κ t ω := hω t ht.le
    have hN0 : 0 ≤ N ω := by
      have := yN_le_Nn C κ X t jstar ω
      rw [I.yN_star t ω] at this
      simp only [N]; linarith
    have hyN : ∀ a, y a ω ≤ N ω := fun a => yN_le_Nn C κ X t a ω
    have hNA : N ω ≤ Aroot (vpos (fun b => y b ω)) := Nn_le_root C κ X t ω hK
    have halg := neg_alg d K I.hd hK n β hn1 hβ16 hβC (fun b => y b ω) (N ω) hN0 hyN hNA
    have hper : ∀ a, (v a ω ^ P - 2 * κ t ω * P * v a ω ^ (P - 1) + 4 * κ t ω ^ 2 * Ct a ω) +
        ((-(P : ℝ) * v a ω ^ (P - 1) + 4 * κ t ω * Ct a ω) * (Δ a + e t a ω) +
          Ct a ω * Venv d K X jstar t a ω) ≤
        vpos (fun b => y b ω) a ^ P + c * (max ((1 - 1 / B) * y a ω + (3 * β + 2 * N ω / B)) 0) ^ (P - 2) *
          (6 * β + 2 * ((N ω - y a ω) ^ 2 + N ω ^ 2) / (B * n)) := by
      intro a
      have hdrift : 0 ≤ Δ a + e t a ω + 2 * κ t ω := by
        have he := ((I.κb t ht ω).2.2 a).1
        have hΔ := I.Δnonneg a
        linarith [neg_abs_le (e t a ω)]
      have hvar : Venv d K X jstar t a ω + 4 * κ t ω * (Δ a + e t a ω) + 4 * κ t ω ^ 2 ≤
          6 * β + 2 * ((N ω - y a ω) ^ 2 + N ω ^ 2) / (B * n) := by
        unfold Venv
        rw [Zx_eq_Nn C κ X t a ω]
        have hzs := I.Nn_star t ω
        have hz0 := Zx_nonneg X t jstar ω
        have hzs2 : Zx X t jstar ω ^ 2 ≤ N ω ^ 2 :=
          pow_le_pow_left₀ hz0 (by simp only [N]; linarith) 2
        have h1 : 2 * ((Nn C κ X t ω - yN C κ X t a ω) ^ 2 + Zx X t jstar ω ^ 2) / (B * n) ≤
            2 * ((N ω - y a ω) ^ 2 + N ω ^ 2) / (B * n) :=
          div_le_div_of_nonneg_right (by simp only [N, y]; linarith) (by positivity)
        have hE := ((I.κb t ht ω).2.2 a).2
        have h2 : 4 * κ t ω * (Δ a + e t a ω) ≤ 16 := by
          have := mul_le_mul_of_nonneg_left (le_abs_self (Δ a + e t a ω) |>.trans hE) (hκ ω).1
          linarith [(hκ ω).2]
        have h3 : 4 * κ t ω ^ 2 ≤ 16 := by
          have := pow_le_pow_left₀ (hκ ω).1 (hκ ω).2 2; norm_num at this; linarith
        have hβd : IAFTRL.beta d K (t + 1) = β := rfl
        have hnd : IAFTRL.Bc K * ((t : ℝ) + 1) = B * n := rfl
        rw [hβd, hnd]
        linarith
      have e1 : (v a ω ^ P - 2 * κ t ω * P * v a ω ^ (P - 1) + 4 * κ t ω ^ 2 * Ct a ω) +
          ((-(P : ℝ) * v a ω ^ (P - 1) + 4 * κ t ω * Ct a ω) * (Δ a + e t a ω) +
            Ct a ω * Venv d K X jstar t a ω) = v a ω ^ P - P * v a ω ^ (P - 1) * (Δ a + e t a ω + 2 * κ t ω) +
            Ct a ω * (Venv d K X jstar t a ω + 4 * κ t ω * (Δ a + e t a ω) + 4 * κ t ω ^ 2) := by ring
      rw [e1]
      have h1 : 0 ≤ P * v a ω ^ (P - 1) * (Δ a + e t a ω + 2 * κ t ω) :=
        mul_nonneg (mul_nonneg (by positivity) (hvp a ω).1) hdrift
      have h2 := mul_le_mul_of_nonneg_left hvar (hCt a ω).1
      have e2 : vpos (fun b => y b ω) a = v a ω := rfl
      rw [e2]
      simp only [Ct] at h2 ⊢
      linarith
    have hsum : g0 ω + ∑ a, (g1 a ω * (Δ a + e t a ω) + g2 a ω * Venv d K X jstar t a ω) =
        h ω * ∑ a, ((v a ω ^ P - 2 * κ t ω * P * v a ω ^ (P - 1) + 4 * κ t ω ^ 2 * Ct a ω) +
        ((-(P : ℝ) * v a ω ^ (P - 1) + 4 * κ t ω * Ct a ω) * (Δ a + e t a ω) +
          Ct a ω * Venv d K X jstar t a ω)) := by
      simp only [g0, g1, g2]
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun a _ => by ring
    rw [hsum]
    refine mul_le_mul_of_nonneg_left ?_ (hh0 ω)
    have hF : Fneg C κ X t ω = ∑ a, vpos (fun b => y b ω) a ^ P := rfl
    rw [hF]
    calc _ ≤ ∑ a, (vpos (fun b => y b ω) a ^ P + c * (max ((1 - 1 / B) * y a ω +
          (3 * β + 2 * N ω / B)) 0) ^ (P - 2) * (6 * β + 2 * ((N ω - y a ω) ^ 2 + N ω ^ 2) / (B * n))) :=
          sum_le_sum fun a _ => hper a
      _ = ∑ a, vpos (fun b => y b ω) a ^ P + ∑ a, c * (max ((1 - 1 / B) * y a ω +
          (3 * β + 2 * N ω / B)) 0) ^ (P - 2) * (6 * β + 2 * ((N ω - y a ω) ^ 2 + N ω ^ 2) / (B * n)) :=
          sum_add_distrib
      _ ≤ _ := halg
  have hFint : Integrable (fun ω => h ω * Fneg C κ X t ω) μ := by
    refine int_of_bdd μ _ ((hh.mono hmF le_rfl).mul (I.Fneg_meas' t ht.le)) (K * r ^ P) fun ω => ?_
    rw [abs_mul, abs_of_nonneg (Fneg_nonneg _ _ _ _ _)]
    have hF : Fneg C κ X t ω ≤ K * r ^ P := by
      unfold Fneg
      calc ∑ a, vpos (fun b => yN C κ X t b ω) a ^ P ≤ ∑ _a : Fin K, r ^ P :=
            sum_le_sum fun a _ => (hvP a ω).2
        _ = _ := by simp
    calc |h ω| * Fneg C κ X t ω ≤ 1 * (K * r ^ P) :=
          mul_le_mul (hhabs ω) hF (Fneg_nonneg _ _ _ _ _) zero_le_one
      _ = _ := one_mul _
  have hJ0 : 0 ≤ J0 d K := by
    unfold J0 Dminus wminus cminus Lam
    have := Cb_ge16 d K I.hd
    have := kK_pos K hK
    have : (0 : ℝ) ≤ (P : ℝ) * (P - 1) / 2 := hc0
    positivity
  have hvN0 : 0 ≤ vN K := by unfold vN aminus Lam; positivity
  have hhint : Integrable h μ := int_of_bdd μ _ (hh.mono hmF le_rfl) 1 hhabs
  have hR : Integrable (fun ω => h ω * ((1 + vN K / n) * Fneg C κ X t ω + J0 d K * n ^ (nuP K - 1))) μ := by
    have : (fun ω => h ω * ((1 + vN K / n) * Fneg C κ X t ω + J0 d K * n ^ (nuP K - 1))) =
        fun ω => (1 + vN K / n) * (h ω * Fneg C κ X t ω) + (J0 d K * n ^ (nuP K - 1)) * h ω := by
      funext ω; ring
    rw [this]
    exact (hFint.const_mul _).add (hhint.const_mul _)
  have hval : ∫ ω, h ω * ((1 + vN K / n) * Fneg C κ X t ω + J0 d K * n ^ (nuP K - 1)) ∂μ ≤
      (1 + vN K / n) * ∫ ω, h ω * Fneg C κ X t ω ∂μ + J0 d K * n ^ (nuP K - 1) := by
    have : (fun ω => h ω * ((1 + vN K / n) * Fneg C κ X t ω + J0 d K * n ^ (nuP K - 1))) =
        fun ω => (1 + vN K / n) * (h ω * Fneg C κ X t ω) + (J0 d K * n ^ (nuP K - 1)) * h ω := by
      funext ω; ring
    rw [this, integral_add (hFint.const_mul _) (hhint.const_mul _), integral_const_mul,
      integral_const_mul]
    have hh1' : ∫ ω, h ω ∂μ ≤ 1 := by
      calc ∫ ω, h ω ∂μ ≤ ∫ _ω, (1 : ℝ) ∂μ := integral_mono hhint (integrable_const _) hh1
        _ = 1 := by simp
    have : J0 d K * n ^ (nuP K - 1) * ∫ ω, h ω ∂μ ≤ J0 d K * n ^ (nuP K - 1) := by
      have h0 : 0 ≤ J0 d K * n ^ (nuP K - 1) := by positivity
      have := mul_le_mul_of_nonneg_left hh1' h0
      linarith
    linarith
  refine hstep.trans ?_
  refine le_trans ?_ hval
  by_cases hf : Integrable (fun ω => g0 ω + ∑ a, (g1 a ω * (Δ a + e t a ω) +
      g2 a ω * Venv d K X jstar t a ω)) μ
  · exact integral_mono_ae hf hR hrhs
  · rw [integral_undef hf]
    exact integral_nonneg fun ω => mul_nonneg (hh0 ω) (by
      have := Fneg_nonneg C κ X t ω
      have : 0 ≤ J0 d K * n ^ (nuP K - 1) := by positivity
      positivity)

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

/-- the initial negative moment (C.221) -/
lemma Iface.neg_init [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t0 : ℕ)
    (ht0 : t0 ≤ T) (hburn : HG d K ≤ ((t0 : ℝ) + 1) ^ ((Pord K : ℝ) / 4)) (hCn : C ≤ (t0 : ℝ) + 1) :
    ∫ ω, Fneg C κ X t0 ω ∂μ ≤ (64 * ((t0 : ℝ) + 1)) ^ Pord K := by
  have hK := I.hK
  have hP := Pord_ge K hK
  have hev := Pord_even K
  set P := Pord K with hPdef
  set n0 : ℝ := (t0 : ℝ) + 1 with hn0
  have hn0p : 0 < n0 := by simp only [n0]; positivity
  have hC := I.hC
  have hpt : ∀ ω, Fneg C κ X t0 ω ≤ 2 ^ (P - 1) * (Gsum X t0 ω + K * (2 * C) ^ P) := by
    intro ω
    unfold Fneg Gsum vpos
    have : ∀ a, max (yN C κ X t0 a ω) 0 ^ P ≤ 2 ^ (P - 1) * (X t0 a ω ^ P + (2 * C) ^ P) := by
      intro a
      have h1 : max (yN C κ X t0 a ω) 0 ≤ |X t0 a ω| + 2 * C := by
        refine max_le ?_ (by positivity)
        unfold yN
        have := I.bR_le t0 ht0 ω
        linarith [neg_abs_le (X t0 a ω)]
      calc max (yN C κ X t0 a ω) 0 ^ P ≤ (|X t0 a ω| + 2 * C) ^ P :=
            pow_le_pow_left₀ (le_max_right _ _) h1 _
        _ ≤ 2 ^ (P - 1) * (|X t0 a ω| ^ P + (2 * C) ^ P) := add_pow_le (abs_nonneg _) (by positivity) P
        _ = 2 ^ (P - 1) * (X t0 a ω ^ P + (2 * C) ^ P) := by rw [hev.pow_abs]
    calc ∑ a, max (yN C κ X t0 a ω) 0 ^ P ≤ ∑ a, 2 ^ (P - 1) * (X t0 a ω ^ P + (2 * C) ^ P) :=
          sum_le_sum fun a _ => this a
      _ = 2 ^ (P - 1) * (∑ a, X t0 a ω ^ P + K * (2 * C) ^ P) := by
          rw [← mul_sum, sum_add_distrib]; simp
  have hGint : Integrable (Gsum X t0) μ :=
    int_of_bdd μ _ (Finset.measurable_sum _ fun a _ => ((I.Xmeas t0 ht0 a).2.pow_const _)) _
      fun ω => by
        unfold Gsum
        rw [abs_of_nonneg (sum_nonneg fun a _ => hev.pow_nonneg _)]
        exact sum_le_sum fun a _ => by
          rw [← hev.pow_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (I.env t0 ht0 ω a) _
  have hroot := I.abs_root t0 ht0 hburn
  have hk := kK_pos K hK
  have hk2 : kK K < 1.65 := kK_lt K hK
  have hKk : (K : ℝ) = kK K ^ P := by
    have := kK_pow K hK 0 (by omega)
    simp at this; rw [← this]
  calc ∫ ω, Fneg C κ X t0 ω ∂μ ≤ ∫ ω, 2 ^ (P - 1) * (Gsum X t0 ω + K * (2 * C) ^ P) ∂μ :=
        integral_mono (I.Fneg_int t0 ht0) ((hGint.add (integrable_const _)).const_mul _) hpt
    _ = 2 ^ (P - 1) * (∫ ω, Gsum X t0 ω ∂μ + K * (2 * C) ^ P) := by
        rw [integral_const_mul, integral_add hGint (integrable_const _), integral_const]; simp
    _ ≤ 2 ^ (P - 1) * (((16 * kK K + 1) * n0) ^ P + ((16 * kK K + 1) * n0) ^ P) := by
        gcongr
        rw [hKk, ← mul_pow]
        apply pow_le_pow_left₀ (by positivity)
        nlinarith
    _ = (2 * (16 * kK K + 1) * n0) ^ P := by
        rw [mul_pow, mul_pow, mul_pow]
        have : (2 : ℝ) ^ P = 2 * 2 ^ (P - 1) := by rw [← pow_succ']; congr 1; omega
        rw [this]; ring
    _ ≤ (64 * n0) ^ P := pow_le_pow_left₀ (by positivity) (by nlinarith) _

/-- (C.211): `E F_t ≤ H_0 n^ν + (64 n_0)^P (n/n_0)^q` from the initial time on -/
lemma Iface.neg_bound [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t0 : ℕ)
    (ht0 : t0 ≤ T) (hburn : HG d K ≤ ((t0 : ℝ) + 1) ^ ((Pord K : ℝ) / 4)) (hCn : C ≤ (t0 : ℝ) + 1) :
    ∀ s, t0 ≤ s → s ≤ T → ∫ ω, Fneg C κ X s ω ∂μ ≤
      HN d K * ((s : ℝ) + 1) ^ nuP K + (64 * ((t0 : ℝ) + 1)) ^ Pord K *
        (((s : ℝ) + 1) / ((t0 : ℝ) + 1)) ^ qN K := by
  have hK := I.hK
  have hνv := nu_sub_vN K hK
  have hP : (512 : ℝ) ≤ Pord K := by exact_mod_cast Pord_ge K hK
  have hJ : J0 d K ≤ (nuP K - vN K) * HN d K := by
    have h := le_max_right 1 (J0 d K / (nuP K - vN K))
    rw [div_le_iff₀ (by linarith)] at h
    unfold HN; linarith
  have hinit := I.neg_init t0 ht0 hburn hCn
  refine supersol_seq (HN d K) (J0 d K) _ (vN K) (nuP K) ((t0 : ℝ) + 1) (qN K) (by positivity)
    (by unfold nuP; linarith) (vN_nonneg K hK) (Nat.le_ceil _) hJ (le_trans zero_le_one (le_max_left _ _))
    (by positivity) (fun s => ∫ ω, Fneg C κ X s ω ∂μ) t0 T ?_ ?_
  · have hH0 : 0 ≤ HN d K * ((t0 : ℝ) + 1) ^ nuP K :=
      mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (by positivity)
    have e : ((t0 : ℝ) + 1) / ((t0 : ℝ) + 1) = 1 := div_self (by positivity)
    simp only [e, one_pow, mul_one]
    linarith
  · intro s _ hsT
    have h := I.neg_step s hsT (fun _ => 1) measurable_const (fun _ => zero_le_one) (fun _ => le_rfl)
    simp only [one_mul] at h
    exact h

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
      (64 * ((t0 : ℝ) + 1)) ^ Pord K * (((t : ℝ) + 1) / ((t0 : ℝ) + 1)) ^ qN K := by
  have hK := I.hK
  have hνv := nu_sub_vN K hK
  have hP : (512 : ℝ) ≤ Pord K := by exact_mod_cast Pord_ge K hK
  have hJ : J0 d K ≤ (nuP K - vN K) * HN d K := by
    have h := le_max_right 1 (J0 d K / (nuP K - vN K))
    rw [div_le_iff₀ (by linarith)] at h
    unfold HN; linarith
  have hJ0 := J0_nonneg d K I.hd hK
  have hvN0 := vN_nonneg K hK
  let A : ℕ → ℝ := fun s => ∫ ω, (sv C κ X m L s ω * Fneg C κ X s ω + L * (1 - sv C κ X m L s ω)) ∂μ
  have hsplit : ∀ s s', s ≤ T + 1 → s' ≤ T →
      ∫ ω, (sv C κ X m L s ω * Fneg C κ X s' ω + L * (1 - sv C κ X m L s ω)) ∂μ =
        ∫ ω, sv C κ X m L s ω * Fneg C κ X s' ω ∂μ + L * ∫ ω, (1 - sv C κ X m L s ω) ∂μ := by
    intro s s' hs hs'
    have hg : Integrable (fun ω => L * (1 - sv C κ X m L s ω)) μ :=
      ((integrable_const (1 : ℝ)).sub (I.sv_int m L s hs)).const_mul L
    rw [integral_add (I.svF_int m L s s' hs hs') hg, integral_const_mul]
  have hA : ∀ s, m ≤ s → s ≤ t → A s ≤ HN d K * ((s : ℝ) + 1) ^ nuP K +
      (64 * ((t0 : ℝ) + 1)) ^ Pord K * (((s : ℝ) + 1) / ((t0 : ℝ) + 1)) ^ qN K := by
    refine supersol_seq (HN d K) (J0 d K) _ (vN K) (nuP K) ((t0 : ℝ) + 1) (qN K) (by positivity)
      (by unfold nuP; linarith) hvN0 (Nat.le_ceil _) hJ (le_trans zero_le_one (le_max_left _ _))
      (by positivity) A m t ?_ ?_
    · have e : A m = ∫ ω, Fneg C κ X m ω ∂μ := by
        simp only [A, sv_start, one_mul, sub_self, mul_zero, add_zero]
      rw [e]
      exact I.neg_bound t0 (by omega) hburn hCn m ht0m (by omega)
    · intro s hms hst
      have hsT : s < T := by omega
      have hstep := I.neg_step s hsT (sv C κ X m L (s + 1)) (I.sv_meas m L (s + 1) s le_rfl hsT.le)
        (sv_nonneg C κ X m L (s + 1)) (sv_le_one C κ X m L (s + 1))
      have hmono : ∫ ω, (sv C κ X m L (s + 1) ω * Fneg C κ X s ω + L * (1 - sv C κ X m L (s + 1) ω)) ∂μ ≤
          A s := by
        refine integral_mono ((I.svF_int m L (s + 1) s (by omega) hsT.le).add
          (((integrable_const 1).sub (I.sv_int m L (s + 1) (by omega))).const_mul L))
          ((I.svF_int m L s s (by omega) hsT.le).add
          (((integrable_const 1).sub (I.sv_int m L s (by omega))).const_mul L)) fun ω => ?_
        exact sv_step C κ X m L s hms ω
      have e1 : A (s + 1) = ∫ ω, sv C κ X m L (s + 1) ω * Fneg C κ X (s + 1) ω ∂μ +
          L * ∫ ω, (1 - sv C κ X m L (s + 1) ω) ∂μ := hsplit (s + 1) (s + 1) (by omega) hsT
      rw [hsplit (s + 1) s (by omega) hsT.le] at hmono
      have hnn : 0 ≤ L * ∫ ω, (1 - sv C κ X m L (s + 1) ω) ∂μ :=
        mul_nonneg hL (integral_nonneg fun ω => sub_nonneg.mpr (sv_le_one C κ X m L (s + 1) ω))
      have hv : 0 ≤ vN K / ((s : ℝ) + 1) := by positivity
      rw [e1]
      have hfin : (1 + vN K / ((s : ℝ) + 1)) * (∫ ω, sv C κ X m L (s + 1) ω * Fneg C κ X s ω ∂μ +
          L * ∫ ω, (1 - sv C κ X m L (s + 1) ω) ∂μ) ≤ (1 + vN K / ((s : ℝ) + 1)) * A s :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
      have hprod := mul_nonneg hv hnn
      linarith
  have hfinal : L * ∫ ω, (1 - sv C κ X m L (t + 1) ω) ∂μ ≤ A t := by
    have h1 : ∫ ω, (sv C κ X m L (t + 1) ω * Fneg C κ X t ω + L * (1 - sv C κ X m L (t + 1) ω)) ∂μ ≤ A t :=
      integral_mono ((I.svF_int m L (t + 1) t (by omega) htT).add
        (((integrable_const 1).sub (I.sv_int m L (t + 1) (by omega))).const_mul L))
        ((I.svF_int m L t t (by omega) htT).add
        (((integrable_const 1).sub (I.sv_int m L t (by omega))).const_mul L))
        fun ω => sv_step C κ X m L t hmt ω
    rw [hsplit (t + 1) t (by omega) htT] at h1
    have h0 : 0 ≤ ∫ ω, sv C κ X m L (t + 1) ω * Fneg C κ X t ω ∂μ :=
      integral_nonneg fun ω => mul_nonneg (sv_nonneg C κ X m L (t + 1) ω) (Fneg_nonneg _ _ _ _ _)
    linarith
  exact hfinal.trans (hA t hmt le_rfl)

end C37

namespace IAFTRL

open MeasureTheory

/-- **Window failure probability via stopped negative moments.** Zhao–Tan, *Best-of-Both-Worlds FTRL
for Linear Bandits*, arXiv:2611.01299v1, Lemmas C.31, C.33 and C.28 ((C.193)–(C.194)), for the abstract
interface `C37.Iface`: with `F_j = Σ_a (2b_j − X_{j,a})_+^P` (`b_j = C − Σ_{s<j} κ_s`), a start time
`t₀` after the burn-in with `C ≤ t₀ + 1`, a window `[m, t]` with `t₀ ≤ m`, and any level `L ≥ 0`,
`L · P(∃ j ∈ [m, t], F_j > L) ≤ H_0 n^ν + (64 n₀)^P (n/n₀)^q` where `n = t + 1`, `n₀ = t₀ + 1`. -/
theorem _root_.solution {d K : ℕ} {jstar : Fin K} {Δ : Fin K → ℝ} {Δ₀ : ℝ} {Ω : Type*}
    [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {F : ℕ → MeasurableSpace Ω}
    {T : ℕ} {C : ℝ} {X D e : ℕ → Fin K → Ω → ℝ} {κ : ℕ → Ω → ℝ}
    (I : C37.Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t0 m t : ℕ) (L : ℝ)
    (hL : 0 ≤ L) (ht0m : t0 ≤ m) (hmt : m ≤ t) (htT : t ≤ T)
    (hburn : C37.HG d K ≤ ((t0 : ℝ) + 1) ^ ((C37.Pord K : ℝ) / 4)) (hCn : C ≤ (t0 : ℝ) + 1) :
    L * ∫ ω, (1 - C37.sv C κ X m L (t + 1) ω) ∂μ ≤ C37.HN d K * ((t : ℝ) + 1) ^ C37.nuP K +
      (64 * ((t0 : ℝ) + 1)) ^ C37.Pord K * (((t : ℝ) + 1) / ((t0 : ℝ) + 1)) ^ C37.qN K := by
  exact I.window t0 m t L hL ht0m hmt htT hburn hCn

end IAFTRL

