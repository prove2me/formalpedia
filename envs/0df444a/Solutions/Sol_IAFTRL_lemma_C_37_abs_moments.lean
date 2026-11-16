-- Prove2me | solution 1 for IAFTRL.lemma_C_37_abs_moments
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T15:54:04.744204+00:00
-- url     : https://prove2.me/submissions/92207760-c559-44ea-898f-2cca3348260f

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

/-- the two-branch curvature bound (C.238)–(C.239) -/
lemma abs_case (d K : ℕ) (hd : 1 ≤ d) (hK : 1 ≤ K) (n β A : ℝ) (hn : 1 ≤ n) (hβ16 : 16 ≤ β)
    (hβC : β ≤ Cb d K * Real.sqrt n) (hA : 0 ≤ A) :
    ((Pord K : ℝ) * (Pord K - 1) / 2) * kK K ^ 2 *
        (A + kK K * (2 * β + 3 * A / IAFTRL.Bc K)) ^ (Pord K - 2) *
        (4 * β + 10 * A ^ 2 / (IAFTRL.Bc K * n)) ≤
      cplus d K * Real.sqrt n * A ^ (Pord K - 2) + aplus K * A ^ Pord K / n +
        Dplus d K * n ^ (hP K - 1) * Real.sqrt n := by
  set P := Pord K with hPdef
  set k := kK K with hk
  set B := IAFTRL.Bc K with hB
  have hP512 := Pord_ge K hK
  have hPr : (512 : ℝ) ≤ P := by exact_mod_cast hP512
  have hk1 : 1 ≤ k := kfac_ge K hK
  have hk2 : k < 1.65 := kK_lt K hK
  have hBpos : 0 < B := Bc_pos K hK
  have hBbig : 12 * k * P ≤ B := Bc_big K hK
  have hsq : 1 ≤ Real.sqrt n := by
    have := Real.sqrt_le_sqrt hn; simpa using this
  have hn0 : 0 < n := by linarith
  have hCb := Cb_ge16 d K hd
  have hc0 : (0 : ℝ) ≤ (P : ℝ) * (P - 1) / 2 := by nlinarith
  have hcP : (P : ℝ) * (P - 1) / 2 * 2 ≤ (P : ℝ) ^ 2 := by linarith
  have hβ0 : 0 ≤ β := by linarith
  -- nonnegativity of the three right-hand terms
  have hT1 : 0 ≤ cplus d K * Real.sqrt n * A ^ (P - 2) := by unfold cplus; positivity
  have hT2 : 0 ≤ aplus K * A ^ P / n := by unfold aplus; positivity
  have hT3 : 0 ≤ Dplus d K * n ^ (hP K - 1) * Real.sqrt n := by
    unfold Dplus wplus; have : (0 : ℝ) ≤ (P : ℝ) * (P - 1) / 2 := hc0; positivity
  rcases le_or_gt (8 * P * k * β) A with hbig | hsmall
  · -- large branch
    have hd1 : k * (2 * β + 3 * A / B) ≤ A / (2 * P) := by
      have e1 : k * (2 * β) ≤ A / (4 * P) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have e2 : k * (3 * A / B) ≤ A / (4 * P) := by
        rw [mul_div_assoc', div_le_div_iff₀ hBpos (by positivity)]; nlinarith
      have e3 : A / (4 * P) + A / (4 * P) = A / (2 * P) := by field_simp; ring
      linarith
    have hbase : A + k * (2 * β + 3 * A / B) ≤ (1 + 1 / (2 * P)) * A := by
      have : (1 + 1 / (2 * P)) * A = A + A / (2 * P) := by field_simp
      linarith
    have hpow : (A + k * (2 * β + 3 * A / B)) ^ (P - 2) ≤ 2 * A ^ (P - 2) := by
      calc (A + k * (2 * β + 3 * A / B)) ^ (P - 2) ≤ ((1 + 1 / (2 * P)) * A) ^ (P - 2) :=
            pow_le_pow_left₀ (by positivity) hbase _
        _ = (1 + 1 / (2 * P)) ^ (P - 2) * A ^ (P - 2) := mul_pow _ _ _
        _ ≤ 2 * A ^ (P - 2) := mul_le_mul_of_nonneg_right (one_add_half_pow P (by omega))
            (by positivity)
    have hV : 4 * β + 10 * A ^ 2 / (B * n) ≤ 4 * Cb d K * Real.sqrt n + 10 * A ^ 2 / (B * n) := by
      linarith
    have hAP : A ^ (P - 2) * A ^ 2 = A ^ P := by rw [← pow_add]; congr 1; omega
    calc ((P : ℝ) * (P - 1) / 2) * k ^ 2 * (A + k * (2 * β + 3 * A / B)) ^ (P - 2) *
          (4 * β + 10 * A ^ 2 / (B * n))
        ≤ ((P : ℝ) * (P - 1) / 2) * k ^ 2 * (2 * A ^ (P - 2)) *
          (4 * Cb d K * Real.sqrt n + 10 * A ^ 2 / (B * n)) := by gcongr
      _ ≤ (P : ℝ) ^ 2 * k ^ 2 * A ^ (P - 2) * (4 * Cb d K * Real.sqrt n + 10 * A ^ 2 / (B * n)) := by
          have : ((P : ℝ) * (P - 1) / 2) * k ^ 2 * (2 * A ^ (P - 2)) ≤ (P : ℝ) ^ 2 * k ^ 2 * A ^ (P - 2) := by
            have h := mul_le_mul_of_nonneg_right hcP (by positivity : (0 : ℝ) ≤ k ^ 2 * A ^ (P - 2))
            linarith
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = cplus d K * Real.sqrt n * A ^ (P - 2) + aplus K * (A ^ (P - 2) * A ^ 2) / n := by
          have hcp : cplus d K = 4 * (P : ℝ) ^ 2 * k ^ 2 * Cb d K := rfl
          have hap : aplus K = 10 * (P : ℝ) ^ 2 * k ^ 2 / B := rfl
          rw [hcp, hap]; field_simp
      _ ≤ _ := by rw [hAP]; linarith
  · -- small branch
    have hbase : A + k * (2 * β + 3 * A / B) ≤ 18 * P * k * β := by
      have e1 : k * (3 * A / B) ≤ A := by
        have h3k : 3 * k ≤ B := by nlinarith
        rw [mul_div_assoc', div_le_iff₀ hBpos]
        linarith [mul_le_mul_of_nonneg_right h3k hA]
      have e2 : 2 * k * β ≤ 2 * P * k * β := by nlinarith
      linarith
    have hβn : 18 * P * k * β ≤ 18 * P * k * Cb d K * Real.sqrt n := by
      have := mul_le_mul_of_nonneg_left hβC (by positivity : (0 : ℝ) ≤ 18 * P * k)
      linarith
    have hpow : (A + k * (2 * β + 3 * A / B)) ^ (P - 2) ≤
        (18 * P * k * Cb d K) ^ (P - 2) * n ^ (hP K - 1) := by
      have hsqn : Real.sqrt n ^ (P - 2) = n ^ (hP K - 1) := by
        have : P - 2 = 2 * (hP K - 1) := by rw [hPdef, Pord_eq]; have := hP_ge K hK; omega
        rw [this, pow_mul, Real.sq_sqrt hn0.le]
      calc (A + k * (2 * β + 3 * A / B)) ^ (P - 2) ≤ (18 * P * k * Cb d K * Real.sqrt n) ^ (P - 2) :=
            pow_le_pow_left₀ (by positivity) (hbase.trans hβn) _
        _ = (18 * P * k * Cb d K) ^ (P - 2) * n ^ (hP K - 1) := by rw [mul_pow, hsqn]
    have hA2 : A ^ 2 ≤ 64 * P ^ 2 * k ^ 2 * Cb d K ^ 2 * n := by
      have h1 : A ≤ 8 * P * k * (Cb d K * Real.sqrt n) := by
        have := mul_le_mul_of_nonneg_left hβC (by positivity : (0 : ℝ) ≤ 8 * P * k)
        linarith
      have h2 := pow_le_pow_left₀ hA h1 2
      have e : (8 * P * k * (Cb d K * Real.sqrt n)) ^ 2 = 64 * P ^ 2 * k ^ 2 * Cb d K ^ 2 * n := by
        rw [show (8 * P * k * (Cb d K * Real.sqrt n)) ^ 2 =
          64 * P ^ 2 * k ^ 2 * Cb d K ^ 2 * (Real.sqrt n) ^ 2 by ring, Real.sq_sqrt hn0.le]
      linarith
    have hV : 4 * β + 10 * A ^ 2 / (B * n) ≤ wplus d K * Real.sqrt n := by
      unfold wplus
      have e1 : 10 * A ^ 2 / (B * n) ≤ 640 * P ^ 2 * k ^ 2 * Cb d K ^ 2 / B := by
        have h10 : 10 * A ^ 2 ≤ 640 * P ^ 2 * k ^ 2 * Cb d K ^ 2 * n := by linarith
        calc 10 * A ^ 2 / (B * n) ≤ (640 * P ^ 2 * k ^ 2 * Cb d K ^ 2 * n) / (B * n) :=
              div_le_div_of_nonneg_right h10 (by positivity)
          _ = 640 * P ^ 2 * k ^ 2 * Cb d K ^ 2 / B := by field_simp
      have e2 : 640 * P ^ 2 * k ^ 2 * Cb d K ^ 2 / B ≤
          640 * P ^ 2 * k ^ 2 * Cb d K ^ 2 / B * Real.sqrt n :=
        le_mul_of_one_le_right (by positivity) hsq
      have e3 : 4 * β ≤ 4 * Cb d K * Real.sqrt n := by linarith
      linarith
    have hmain : ((P : ℝ) * (P - 1) / 2) * k ^ 2 * (A + k * (2 * β + 3 * A / B)) ^ (P - 2) *
        (4 * β + 10 * A ^ 2 / (B * n)) ≤ Dplus d K * n ^ (hP K - 1) * Real.sqrt n := by
      calc ((P : ℝ) * (P - 1) / 2) * k ^ 2 * (A + k * (2 * β + 3 * A / B)) ^ (P - 2) *
            (4 * β + 10 * A ^ 2 / (B * n))
          ≤ ((P : ℝ) * (P - 1) / 2) * k ^ 2 * ((18 * P * k * Cb d K) ^ (P - 2) * n ^ (hP K - 1)) *
            (wplus d K * Real.sqrt n) := by gcongr
        _ = Dplus d K * n ^ (hP K - 1) * Real.sqrt n := by unfold Dplus; ring
    linarith

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

/-- the deterministic one-step absolute-moment inequality (C.240) with its linearization (C.233) -/
lemma abs_alg (d K : ℕ) (hd : 1 ≤ d) (hK : 1 ≤ K) (n β : ℝ) (hn : 1 ≤ n) (hβ16 : 16 ≤ β)
    (hβC : β ≤ Cb d K * Real.sqrt n) (x E Zv : Fin K → ℝ) (Zs : ℝ) (hE : ∀ a, |E a| ≤ 2)
    (hZv : ∀ a, 0 ≤ Zv a ∧ Zv a ≤ 2 * Aroot x) (hZs : 0 ≤ Zs ∧ Zs ≤ Aroot x) :
    ∑ a, x a ^ Pord K + ∑ a, ((Pord K : ℝ) * x a ^ (Pord K - 1) * E a +
        ((Pord K : ℝ) * (Pord K - 1) / 2) * (|x a| + (2 * β + 3 * Aroot x / IAFTRL.Bc K)) ^ (Pord K - 2) *
          (4 * β + 2 * (Zv a ^ 2 + Zs ^ 2) / (IAFTRL.Bc K * n))) ≤
      (1 + vG K / n) * ∑ a, x a ^ Pord K + (Pord K : ℝ) / 8 * Astar K * n ^ (Pord K - 1) +
        JG d K * n ^ (nuP K - 1) := by
  set P := Pord K with hPdef
  set k := kK K with hk
  set B := IAFTRL.Bc K with hB
  set A := Aroot x with hAdef
  have hP512 := Pord_ge K hK
  have hPr : (512 : ℝ) ≤ P := by exact_mod_cast hP512
  have hev := Pord_even K
  have hk1 : 1 ≤ k := kfac_ge K hK
  have hBpos : 0 < B := Bc_pos K hK
  have hn0 : 0 < n := by linarith
  have hA : 0 ≤ A := Aroot_nonneg x
  have hS : ∑ a, x a ^ P = A ^ P := (root_pow x P (by omega) hev).symm
  have hc0 : (0 : ℝ) ≤ (P : ℝ) * (P - 1) / 2 := by nlinarith
  set δ := 2 * β + 3 * A / B with hδ
  have hδ0 : 0 ≤ δ := by positivity
  -- split the sum
  rw [sum_add_distrib]
  -- drift
  have hdrift : ∑ a, (P : ℝ) * x a ^ (P - 1) * E a ≤ 2 * P * k * A ^ (P - 1) :=
    abs_drift K hK x E hE
  -- curvature
  have hVa : ∀ a, 4 * β + 2 * (Zv a ^ 2 + Zs ^ 2) / (B * n) ≤ 4 * β + 10 * A ^ 2 / (B * n) := by
    intro a
    have h1 : Zv a ^ 2 ≤ (2 * A) ^ 2 := pow_le_pow_left₀ (hZv a).1 (hZv a).2 2
    have h2 : Zs ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hZs.1 hZs.2 2
    have : 2 * (Zv a ^ 2 + Zs ^ 2) ≤ 10 * A ^ 2 := by linarith
    have := div_le_div_of_nonneg_right this (by positivity : (0 : ℝ) ≤ B * n)
    linarith
  have hcurv1 : ∑ a, ((P : ℝ) * (P - 1) / 2) * (|x a| + δ) ^ (P - 2) *
      (4 * β + 2 * (Zv a ^ 2 + Zs ^ 2) / (B * n)) ≤
      ((P : ℝ) * (P - 1) / 2) * (4 * β + 10 * A ^ 2 / (B * n)) * ∑ a, (|x a| + δ) ^ (P - 2) := by
    rw [mul_sum]
    exact sum_le_sum fun a _ => by
      have := mul_le_mul_of_nonneg_left (hVa a)
        (by positivity : (0 : ℝ) ≤ ((P : ℝ) * (P - 1) / 2) * (|x a| + δ) ^ (P - 2))
      linarith
  have hcurv2 : ∑ a, (|x a| + δ) ^ (P - 2) ≤ k ^ 2 * (A + k * δ) ^ (P - 2) :=
    abs_curv K hK x δ hδ0
  have hcurv : ∑ a, ((P : ℝ) * (P - 1) / 2) * (|x a| + δ) ^ (P - 2) *
      (4 * β + 2 * (Zv a ^ 2 + Zs ^ 2) / (B * n)) ≤
      ((P : ℝ) * (P - 1) / 2) * k ^ 2 * (A + k * δ) ^ (P - 2) * (4 * β + 10 * A ^ 2 / (B * n)) := by
    refine hcurv1.trans ?_
    have := mul_le_mul_of_nonneg_left hcurv2
      (by positivity : (0 : ℝ) ≤ ((P : ℝ) * (P - 1) / 2) * (4 * β + 10 * A ^ 2 / (B * n)))
    calc _ ≤ ((P : ℝ) * (P - 1) / 2) * (4 * β + 10 * A ^ 2 / (B * n)) *
          (k ^ 2 * (A + k * δ) ^ (P - 2)) := this
      _ = _ := by ring
  have hcase := abs_case d K hd hK n β A hn hβ16 hβC hA
  rw [← hPdef, ← hk, ← hB, ← hδ] at hcase
  -- linearizations
  have hlin1 : 2 * P * k * A ^ (P - 1) ≤ (P / (8 * n)) * A ^ P + (P : ℝ) / 8 * Astar K * n ^ (P - 1) := by
    have h := lin_pow (2 * P * k) A (16 * k * n) (P - 1) P (by positivity) hA (by positivity) (by omega)
    have e1 : P - (P - 1) = 1 := by omega
    rw [e1, pow_one] at h
    have e2 : 2 * (P : ℝ) * k / (16 * k * n) = P / (8 * n) := by field_simp; ring
    have e3 : 2 * (P : ℝ) * k * (16 * k * n) ^ (P - 1) = (P : ℝ) / 8 * Astar K * n ^ (P - 1) := by
      unfold Astar
      rw [← hk, ← hPdef, mul_pow]
      have : (16 * k) ^ P = (16 * k) * (16 * k) ^ (P - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [this]; ring
    rw [e2, e3] at h
    exact h
  have hcp : 0 < cplus d K := by
    unfold cplus; have := Cb_ge16 d K hd; rw [← hk, ← hPdef]; positivity
  have hlin2 : cplus d K * Real.sqrt n * A ^ (P - 2) ≤ (P / (8 * n)) * A ^ P +
      cplus d K * (8 * cplus d K / P) ^ (hP K - 1) * n ^ (nuP K - 1) := by
    set R2 := 8 * cplus d K / P * (n * Real.sqrt n) with hR2
    have hR2pos : 0 < R2 := by positivity
    have h := lin_pow (cplus d K * Real.sqrt n) A (Real.sqrt R2) (P - 2) P (by positivity) hA
      (Real.sqrt_pos.mpr hR2pos) (by omega)
    have e1 : P - (P - 2) = 2 := by omega
    rw [e1, Real.sq_sqrt hR2pos.le] at h
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have e2 : cplus d K * Real.sqrt n / R2 = P / (8 * n) := by
      rw [hR2]; field_simp
    have e3 : Real.sqrt R2 ^ (P - 2) = R2 ^ (hP K - 1) := by
      have : P - 2 = 2 * (hP K - 1) := by rw [hPdef, Pord_eq]; have := hP_ge K hK; omega
      rw [this, pow_mul, Real.sq_sqrt hR2pos.le]
    have e4 : cplus d K * Real.sqrt n * R2 ^ (hP K - 1) =
        cplus d K * (8 * cplus d K / P) ^ (hP K - 1) * n ^ (nuP K - 1) := by
      rw [hR2, mul_pow, ← nu_pow K hK n hn0]; ring
    rw [e2, e3, e4] at h
    exact h
  have hDn := nu_pow_le K hK n hn
  have hDp : 0 ≤ Dplus d K := by
    unfold Dplus wplus; rw [← hk, ← hPdef, ← hB]; have := Cb_ge16 d K hd; positivity
  have hD := mul_le_mul_of_nonneg_left hDn hDp
  -- assemble
  have hvG : vG K = (P : ℝ) / 4 + aplus K := rfl
  have hJG : JG d K = cplus d K * (8 * cplus d K / P) ^ (hP K - 1) + Dplus d K := rfl
  rw [hS, hvG, hJG]
  have e5 : aplus K * A ^ P / n = aplus K / n * A ^ P := by ring
  have e6 : (1 + ((P : ℝ) / 4 + aplus K) / n) * A ^ P =
      A ^ P + (P / (8 * n)) * A ^ P + (P / (8 * n)) * A ^ P + aplus K / n * A ^ P := by
    field_simp; ring
  rw [e6]
  have e7 : Dplus d K * n ^ (hP K - 1) * Real.sqrt n = Dplus d K * (n ^ (hP K - 1) * Real.sqrt n) := by
    ring
  rw [e7] at hcase
  linarith

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

/-- one step of the absolute-moment recursion -/
lemma Iface.abs_step [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ)
    (t : ℕ) (ht : t < T) :
    ∫ ω, Gsum X (t + 1) ω ∂μ ≤ (1 + vG K / ((t : ℝ) + 1)) * ∫ ω, Gsum X t ω ∂μ +
      (Pord K : ℝ) / 8 * Astar K * ((t : ℝ) + 1) ^ (Pord K - 1) +
        JG d K * ((t : ℝ) + 1) ^ (nuP K - 1) := by
  have hK := I.hK
  have hP := Pord_ge K hK
  have hev := Pord_even K
  have hB := Bc_pos K hK
  set P := Pord K with hPdef
  set β := IAFTRL.beta d K (t + 1) with hβ
  set n : ℝ := (t : ℝ) + 1 with hn
  have hn1 : (1 : ℝ) ≤ n := by simp only [n]; linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
  have hβ16 := beta_ge16 d K (t + 1) I.hd
  have hβC : β ≤ Cb d K * Real.sqrt n := by
    have := beta_le_Cb d K (t + 1) hK (by omega); push_cast at this; exact this
  set r := renv d K t
  have hr0 : 0 ≤ r := renv_nonneg d K hK I.hd t
  have henv := I.env t ht.le
  have hXm := I.Xmeas t ht.le
  have hXm' := I.Xmeas (t + 1) ht
  let A : Ω → ℝ := fun ω => Aroot (fun b => X t b ω)
  have hA0 : ∀ ω, 0 ≤ A ω := fun ω => Aroot_nonneg _
  have hAle : ∀ ω, A ω ≤ K * r := fun ω => Aroot_le _ r hr0 (henv ω) hK
  have hAm : Measurable[F t] A := Aroot_meas X t fun a => (hXm a).1
  -- integrability
  have hGint : ∀ s ≤ T, Integrable (Gsum X s) μ := fun s hs =>
    int_of_bdd μ _ (Finset.measurable_sum _ fun a _ => ((I.Xmeas s hs a).2.pow_const _)) _
      fun ω => by
        unfold Gsum
        rw [abs_of_nonneg (sum_nonneg fun a _ => hev.pow_nonneg _)]
        exact sum_le_sum fun a _ => by
          rw [← hev.pow_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (I.env s hs ω a) _
  -- coefficients
  let g1 : Fin K → Ω → ℝ := fun a ω => (P : ℝ) * X t a ω ^ (P - 1)
  let g2 : Fin K → Ω → ℝ := fun a ω => ((P : ℝ) * (P - 1) / 2) *
    (|X t a ω| + (2 * β + 3 * A ω / IAFTRL.Bc K)) ^ (P - 2)
  have hc0 : (0 : ℝ) ≤ (P : ℝ) * (P - 1) / 2 := by
    have : (512 : ℝ) ≤ P := by exact_mod_cast hP
    nlinarith
  have hstep := I.step t ht (Gsum X (t + 1)) (Gsum X t) g1 g2 (hGint (t + 1) ht) (hGint t ht.le)
    (fun a => (((hXm a).1.pow_const _).const_mul _).stronglyMeasurable)
    (fun _ => (P : ℝ) * r ^ (P - 1))
    (fun a ω => by
      simp only [g1, abs_mul, abs_pow, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (henv ω a) _) (by positivity))
    (fun a => by
      have hφ : Continuous (fun q : ℝ × ℝ => ((P : ℝ) * (P - 1) / 2) *
          (|q.1| + (2 * β + 3 * q.2 / IAFTRL.Bc K)) ^ (P - 2)) := by fun_prop
      have hm := hφ.measurable.comp ((hXm a).1.prodMk hAm)
      exact hm.stronglyMeasurable)
    (fun _ => ((P : ℝ) * (P - 1) / 2) * (r + (2 * β + 3 * (K * r) / IAFTRL.Bc K)) ^ (P - 2))
    (fun a ω => by
      simp only [g2]
      rw [abs_of_nonneg (by have := hA0 ω; positivity)]
      have hβ0 : 0 ≤ β := by linarith
      have h3 : 3 * A ω / IAFTRL.Bc K ≤ 3 * (K * r) / IAFTRL.Bc K :=
        div_le_div_of_nonneg_right (by linarith [hAle ω]) hB.le
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by have := hA0 ω; positivity) ?_ _) hc0
      linarith [henv ω a])
    (fun a ω => by simp only [g2]; have := hA0 ω; positivity)
    (Filter.Eventually.of_forall fun ω => by
      unfold Gsum
      rw [← sum_add_distrib]
      refine sum_le_sum fun a _ => ?_
      rw [I.Xs]
      have hT := pow_taylor (X t a ω) (D t a ω) P (by omega)
      have hD : |D t a ω| ≤ 2 * β + 3 * A ω / IAFTRL.Bc K := by
        have hm := I.mag t ht a ω
        have h1 := Zx_le_root X t a ω
        have h2 := Zx_star_le_root I t ω
        have : (Zx X t a ω + Zx X t jstar ω) / IAFTRL.Bc K ≤ 3 * A ω / IAFTRL.Bc K :=
          div_le_div_of_nonneg_right (by simp only [A]; linarith) hB.le
        linarith
      have h3 : (|X t a ω| + |D t a ω|) ^ (P - 2) ≤ (|X t a ω| + (2 * β + 3 * A ω / IAFTRL.Bc K)) ^ (P - 2) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      have h4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hc0) (sq_nonneg (D t a ω))
      simp only [g1, g2]
      linarith)
  -- bound the right-hand side pointwise
  have hpt : ∀ ω, Gsum X t ω + ∑ a, (g1 a ω * (Δ a + e t a ω) + g2 a ω * Venv d K X jstar t a ω) ≤
      (1 + vG K / n) * Gsum X t ω + (P : ℝ) / 8 * Astar K * n ^ (P - 1) + JG d K * n ^ (nuP K - 1) := by
    intro ω
    have h := abs_alg d K I.hd hK n β hn1 hβ16 hβC (fun b => X t b ω) (fun a => Δ a + e t a ω)
      (fun a => Zx X t a ω) (Zx X t jstar ω) (fun a => ((I.κb t ht ω).2.2 a).2)
      (fun a => ⟨Zx_nonneg X t a ω, Zx_le_root X t a ω⟩)
      ⟨Zx_nonneg X t jstar ω, Zx_star_le_root I t ω⟩
    unfold Gsum
    simp only [g1, g2, Venv, A]
    exact h
  have hbint : Integrable (fun ω => (1 + vG K / n) * Gsum X t ω + (P : ℝ) / 8 * Astar K * n ^ (P - 1) +
      JG d K * n ^ (nuP K - 1)) μ :=
    (((hGint t ht.le).const_mul _).add (integrable_const _)).add (integrable_const _)
  have hG0 : 0 ≤ ∫ ω, Gsum X t ω ∂μ :=
    integral_nonneg fun ω => sum_nonneg fun a _ => hev.pow_nonneg _
  have hvG0 : 0 ≤ vG K := by unfold vG aplus; positivity
  have hval : ∫ ω, ((1 + vG K / n) * Gsum X t ω + (P : ℝ) / 8 * Astar K * n ^ (P - 1) +
      JG d K * n ^ (nuP K - 1)) ∂μ = (1 + vG K / n) * ∫ ω, Gsum X t ω ∂μ +
      (P : ℝ) / 8 * Astar K * n ^ (P - 1) + JG d K * n ^ (nuP K - 1) := by
    have i1 : Integrable (fun ω => (1 + vG K / n) * Gsum X t ω) μ := (hGint t ht.le).const_mul _
    have i2 : Integrable (fun ω => (1 + vG K / n) * Gsum X t ω + (P : ℝ) / 8 * Astar K * n ^ (P - 1)) μ :=
      i1.add (integrable_const _)
    rw [integral_add i2 (integrable_const _), integral_add i1 (integrable_const _),
      integral_const_mul, integral_const, integral_const]
    simp
  have hJG0 : 0 ≤ JG d K := by
    unfold JG Dplus wplus cplus
    have := Cb_ge16 d K I.hd
    have := kK_pos K hK
    have : (512 : ℝ) ≤ P := by exact_mod_cast hP
    have : (0 : ℝ) ≤ (P : ℝ) * (P - 1) / 2 := hc0
    positivity
  have hAs0 : 0 ≤ Astar K := by unfold Astar; have := kK_pos K hK; positivity
  refine hstep.trans ?_
  rw [← hval]
  by_cases hf : Integrable (fun ω => Gsum X t ω + ∑ a, (g1 a ω * (Δ a + e t a ω) +
      g2 a ω * Venv d K X jstar t a ω)) μ
  · exact integral_mono hf hbint hpt
  · rw [integral_undef hf, hval]
    positivity

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

/-- (C.234): `E[G_t] ≤ A* n^P + H_G n^ν` with `n = t + 1` -/
lemma Iface.abs_bound [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) :
    ∀ t ≤ T, ∫ ω, Gsum X t ω ∂μ ≤ Astar K * ((t : ℝ) + 1) ^ Pord K + HG d K * ((t : ℝ) + 1) ^ nuP K := by
  have hK := I.hK
  have hP := Pord_ge K hK
  have hPr : (512 : ℝ) ≤ Pord K := by exact_mod_cast hP
  have hAs : 0 ≤ Astar K := by unfold Astar; have := kK_pos K hK; positivity
  have hH1 : 1 ≤ HG d K := le_max_left _ _
  have hνv := nu_sub_vG K hK
  have hvG := vG_le K hK
  have hvG0 : 0 ≤ vG K := by unfold vG aplus; have := Bc_pos K hK; positivity
  have hJ : JG d K ≤ (nuP K - vG K) * HG d K := by
    have h := le_max_right 1 (JG d K / (nuP K - vG K))
    rw [div_le_iff₀ (by linarith)] at h
    unfold HG; linarith
  have hν1 : 1 ≤ nuP K := by unfold nuP; linarith
  intro t
  induction t with
  | zero =>
    intro _
    have h0 : ∀ ω, Gsum X 0 ω = 0 := fun ω => by
      unfold Gsum; simp [I.X0, zero_pow (show Pord K ≠ 0 by omega)]
    simp only [h0, integral_zero, Nat.cast_zero, zero_add, one_pow, Real.one_rpow, mul_one]
    linarith
  | succ t ih =>
    intro ht
    have hstep := I.abs_step t (by omega)
    have ih' := ih (by omega)
    set n : ℝ := (t : ℝ) + 1 with hn
    have hn1 : (1 : ℝ) ≤ n := by simp only [n]; linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
    have hn0 : 0 < n := by linarith
    have hcast : ((t + 1 : ℕ) : ℝ) + 1 = n + 1 := by push_cast; ring
    rw [hcast]
    have h1 : (1 + vG K / n) * ∫ ω, Gsum X t ω ∂μ ≤
        (1 + vG K / n) * (Astar K * n ^ Pord K + HG d K * n ^ nuP K) :=
      mul_le_mul_of_nonneg_left ih' (by positivity)
    -- the two tangent inequalities
    have hpP := pow_succ_ge n hn0.le (Pord K) (by omega)
    have hpν := rpow_succ_ge n (nuP K) hn0 hν1
    have eP : n ^ Pord K / n = n ^ (Pord K - 1) := by
      rw [div_eq_iff hn0.ne']; rw [← pow_succ]; congr 1; omega
    have eν : n ^ nuP K / n = n ^ (nuP K - 1) := by rw [Real.rpow_sub_one hn0.ne']
    have hA2 : (1 + vG K / n) * (Astar K * n ^ Pord K) + (Pord K : ℝ) / 8 * Astar K * n ^ (Pord K - 1) ≤
        Astar K * (n + 1) ^ Pord K := by
      have e : (1 + vG K / n) * (Astar K * n ^ Pord K) =
          Astar K * n ^ Pord K + vG K * Astar K * (n ^ Pord K / n) := by ring
      rw [e, eP]
      have hnp : 0 ≤ n ^ (Pord K - 1) := by positivity
      have : vG K * Astar K * n ^ (Pord K - 1) + (Pord K : ℝ) / 8 * Astar K * n ^ (Pord K - 1) ≤
          Pord K * Astar K * n ^ (Pord K - 1) := by
        have := mul_le_mul_of_nonneg_right (show vG K + (Pord K : ℝ) / 8 ≤ Pord K by linarith)
          (mul_nonneg hAs hnp)
        linarith
      have := mul_le_mul_of_nonneg_left hpP hAs
      linarith
    have hH2 : (1 + vG K / n) * (HG d K * n ^ nuP K) + JG d K * n ^ (nuP K - 1) ≤
        HG d K * (n + 1) ^ nuP K := by
      have e : (1 + vG K / n) * (HG d K * n ^ nuP K) =
          HG d K * n ^ nuP K + vG K * HG d K * (n ^ nuP K / n) := by ring
      rw [e, eν]
      have hnp : 0 ≤ n ^ (nuP K - 1) := by positivity
      have h3 := mul_le_mul_of_nonneg_right hJ hnp
      have h4 := mul_le_mul_of_nonneg_left hpν (by linarith : (0 : ℝ) ≤ HG d K)
      linarith
    linarith

/-- after the burn-in `n^{P/4} ≥ H_G`: `E[G_t] ≤ ((16k + 1) n)^P` (C.235) -/
lemma Iface.abs_root [IsProbabilityMeasure μ] (I : Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ)
    (ht : t ≤ T) (hburn : HG d K ≤ ((t : ℝ) + 1) ^ ((Pord K : ℝ) / 4)) :
    ∫ ω, Gsum X t ω ∂μ ≤ ((16 * kK K + 1) * ((t : ℝ) + 1)) ^ Pord K := by
  have hK := I.hK
  have hP := Pord_ge K hK
  have hb := I.abs_bound t ht
  set n : ℝ := (t : ℝ) + 1 with hn
  have hn0 : 0 < n := by simp only [n]; positivity
  have hk := kK_pos K hK
  have h1 : HG d K * n ^ nuP K ≤ n ^ Pord K := by
    have e : n ^ ((Pord K : ℝ) / 4) * n ^ nuP K = n ^ Pord K := by
      rw [← Real.rpow_add hn0, ← Real.rpow_natCast]; congr 1; unfold nuP; ring
    rw [← e]
    exact mul_le_mul_of_nonneg_right hburn (by positivity)
  have h2 : Astar K * n ^ Pord K + n ^ Pord K ≤ ((16 * kK K + 1) * n) ^ Pord K := by
    have e1 : Astar K * n ^ Pord K = (16 * kK K * n) ^ Pord K := by unfold Astar; ring
    rw [e1, show (16 * kK K + 1) * n = 16 * kK K * n + n by ring]
    exact pow_add_pow_le (by positivity) hn0.le (by omega)
  linarith

end C37

namespace IAFTRL

open MeasureTheory

/-- **Absolute moments after the burn-in.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*,
arXiv:2611.01299v1, Lemmas C.36–C.37 ((C.234)–(C.235)), for the abstract scalar difference interface
`C37.Iface` ((C.226)–(C.228) of Lemma C.34): with `G_t = Σ_a X_{t,a}^P`, `n = t + 1`,
`k = K^{1/P}`, once `n^{P/4} ≥ H_G`, `E[G_t] ≤ ((16k + 1) n)^P`. -/
theorem _root_.solution {d K : ℕ} {jstar : Fin K} {Δ : Fin K → ℝ} {Δ₀ : ℝ} {Ω : Type*}
    [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {F : ℕ → MeasurableSpace Ω}
    {T : ℕ} {C : ℝ} {X D e : ℕ → Fin K → Ω → ℝ} {κ : ℕ → Ω → ℝ}
    (I : C37.Iface d K jstar Δ Δ₀ μ F T C X D e κ) (t : ℕ) (ht : t ≤ T)
    (hburn : C37.HG d K ≤ ((t : ℝ) + 1) ^ ((C37.Pord K : ℝ) / 4)) :
    ∫ ω, C37.Gsum X t ω ∂μ ≤ ((16 * C37.kK K + 1) * ((t : ℝ) + 1)) ^ C37.Pord K := by
  exact I.abs_root t ht hburn

end IAFTRL

