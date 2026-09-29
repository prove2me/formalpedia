-- Prove2me | solution 1 for Maldacena1999.near_horizon_AdS7S4_AdS4S7_AdS3S3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T13:57:02.556877+00:00
-- url     : https://prove2.me/submissions/a4484ac5-b99f-4cc2-bba2-86b21ab624b8

import Mathlib
import Definitions.Def_Maldacena1999_BraneDefs

open Filter Topology

open Maldacena1999 in
lemma malda_sign_zero (p : ℕ) : ambientSign p 0 = -1 := by
  simp [ambientSign]

open Maldacena1999 in
lemma malda_sign_last (p : ℕ) : ambientSign p (Fin.last (p + 2)) = 1 := by
  simp [ambientSign]

open Maldacena1999 in
lemma malda_sign_mid (p : ℕ) (k : Fin (p + 1)) :
    ambientSign p k.castSucc.succ = if k.val = 0 then (-1 : ℝ) else 1 := by
  have h1 : (k.castSucc.succ : Fin (p + 3)).val = k.val + 1 := by simp
  unfold ambientSign
  rw [h1]
  by_cases hk : k.val = 0
  · rw [if_pos (by omega), if_pos hk]
  · rw [if_neg (by omega), if_neg hk]

open Maldacena1999 in
lemma malda_ambientForm_split (p : ℕ) (X : Fin (p + 3) → ℝ) :
    ambientForm p X = -X 0 ^ 2 + X (Fin.last (p + 2)) ^ 2 +
      ∑ k : Fin (p + 1), (if k.val = 0 then (-1 : ℝ) else 1) * X k.castSucc.succ ^ 2 := by
  unfold ambientForm
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, Fin.succ_last]
  simp only [malda_sign_zero, malda_sign_last, malda_sign_mid]
  ring

open Maldacena1999 in
lemma malda_pe_zero (p : ℕ) (R : ℝ) (q : ℝ × (Fin (p + 1) → ℝ)) :
    poincareEmbedding p R q 0 =
      (q.1 + (minkowskiForm p q.2 * q.1 / R ^ 2 + R ^ 2 / q.1)) / 2 := by
  simp [poincareEmbedding]

open Maldacena1999 in
lemma malda_pe_mid (p : ℕ) (R : ℝ) (q : ℝ × (Fin (p + 1) → ℝ)) (k : Fin (p + 1)) :
    poincareEmbedding p R q k.castSucc.succ = q.2 k * q.1 / R := by
  have hk : ¬ p < k.val := Nat.not_lt.2 k.is_le
  simp [poincareEmbedding, hk]

open Maldacena1999 in
lemma malda_pe_last (p : ℕ) (R : ℝ) (q : ℝ × (Fin (p + 1) → ℝ)) :
    poincareEmbedding p R q (Fin.last (p + 2)) =
      (q.1 - (minkowskiForm p q.2 * q.1 / R ^ 2 + R ^ 2 / q.1)) / 2 := by
  simp [poincareEmbedding]

open Maldacena1999 in
lemma malda_pe_diff (p : ℕ) (R : ℝ) (q : ℝ × (Fin (p + 1) → ℝ)) (hq : q.1 ≠ 0) :
    DifferentiableAt ℝ (poincareEmbedding p R) q := by
  rw [differentiableAt_pi]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [malda_pe_zero]
    unfold minkowskiForm
    fun_prop (disch := assumption)
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [Fin.succ_last, malda_pe_last]
      unfold minkowskiForm
      fun_prop (disch := assumption)
    · simp only [malda_pe_mid]
      fun_prop

open Maldacena1999 in
lemma malda_line (p : ℕ) (R : ℝ) (q δ : ℝ × (Fin (p + 1) → ℝ)) (hq : q.1 ≠ 0) :
    HasDerivAt (fun t : ℝ => poincareEmbedding p R (q + t • δ))
      (fderiv ℝ (poincareEmbedding p R) q δ) 0 := by
  have hl : HasDerivAt (fun t : ℝ => q + t • δ) δ 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const δ).const_add q
  exact (malda_pe_diff p R q hq).hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) hl (by simp)

open Maldacena1999 in
lemma malda_mink_line (p : ℕ) (x d : Fin (p + 1) → ℝ) (t : ℝ) :
    minkowskiForm p (x + t • d) = minkowskiForm p x +
      2 * t * (∑ a : Fin (p + 1), (if a.val = 0 then (-1:ℝ) else 1) * (x a * d a)) +
      t ^ 2 * minkowskiForm p d := by
  unfold minkowskiForm
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma malda_lin (U d : ℝ) : HasDerivAt (fun t : ℝ => U + t * d) d 0 := by
  simpa using ((hasDerivAt_id' (0:ℝ)).mul_const d).const_add U

lemma malda_quad (A B C : ℝ) : HasDerivAt (fun t : ℝ => A + 2 * t * B + t ^ 2 * C) (2 * B) 0 := by
  have h := (((hasDerivAt_id' (0:ℝ)).const_mul (2 * B)).const_add A).add
    ((hasDerivAt_pow 2 (0:ℝ)).mul_const C)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => ?_))).congr_deriv ?_
  · simp only [Pi.add_apply]
    ring
  · simp

lemma malda_endcomp (U dU A B C R s : ℝ) (hU : U ≠ 0) :
    HasDerivAt (fun t : ℝ => ((U + t * dU) + s * ((A + 2 * t * B + t ^ 2 * C) * (U + t * dU) / R ^ 2
        + R ^ 2 / (U + t * dU))) / 2)
      ((dU + s * ((2 * B * U + A * dU) / R ^ 2 - R ^ 2 * dU / U ^ 2)) / 2) 0 := by
  have hl := malda_lin U dU
  have hl0 : U + 0 * dU ≠ 0 := by simpa using hU
  have h := (hl.add (((((malda_quad A B C).mul hl).div_const (R ^ 2)).add
    ((hl.inv hl0).const_mul (R ^ 2))).const_mul s)).div_const 2
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => ?_))).congr_deriv ?_
  · simp only [Pi.add_apply, Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv]
    try ring
  · simp only [zero_mul, add_zero, mul_zero]
    field_simp
    try ring

open Maldacena1999 in
theorem malda_induced_metric (p : ℕ) (R : ℝ) (hR : 0 < R)
    (U : ℝ) (hU : 0 < U) (x : Fin (p + 1) → ℝ) (δ : ℝ × (Fin (p + 1) → ℝ)) :
    ambientForm p (fderiv ℝ (poincareEmbedding p R) (U, x) δ) =
      U ^ 2 / R ^ 2 * minkowskiForm p δ.2 + R ^ 2 * δ.1 ^ 2 / U ^ 2 := by
  have hU0 : U ≠ 0 := hU.ne'
  have hR0 : R ≠ 0 := hR.ne'
  have hL := malda_line p R (U, x) δ hU0
  set L := fderiv ℝ (poincareEmbedding p R) (U, x) δ with hLdef
  have hcomp := hasDerivAt_pi.1 hL
  have hfst : ∀ t : ℝ, ((U, x) + t • δ).1 = U + t * δ.1 := fun t => by simp
  have hsnd : ∀ t : ℝ, ((U, x) + t • δ).2 = x + t • δ.2 := fun t => by simp
  set B : ℝ := ∑ a : Fin (p + 1), (if a.val = 0 then (-1:ℝ) else 1) * (x a * δ.2 a) with hB
  have h0 : L 0 = (δ.1 + 1 * ((2 * B * U + minkowskiForm p x * δ.1) / R ^ 2 - R ^ 2 * δ.1 / U ^ 2)) / 2 := by
    have e : (fun t : ℝ => poincareEmbedding p R ((U, x) + t • δ) 0) = fun t : ℝ =>
        ((U + t * δ.1) + 1 * ((minkowskiForm p x + 2 * t * B + t ^ 2 * minkowskiForm p δ.2) *
          (U + t * δ.1) / R ^ 2 + R ^ 2 / (U + t * δ.1))) / 2 := by
      funext t
      rw [malda_pe_zero, hfst, hsnd, malda_mink_line]
      ring
    have h1 := hcomp 0
    rw [e] at h1
    exact h1.unique (malda_endcomp U δ.1 _ B _ R 1 hU0)
  have hlast : L (Fin.last (p + 2)) = (δ.1 + (-1) * ((2 * B * U + minkowskiForm p x * δ.1) / R ^ 2 - R ^ 2 * δ.1 / U ^ 2)) / 2 := by
    have e : (fun t : ℝ => poincareEmbedding p R ((U, x) + t • δ) (Fin.last (p + 2))) = fun t : ℝ =>
        ((U + t * δ.1) + (-1) * ((minkowskiForm p x + 2 * t * B + t ^ 2 * minkowskiForm p δ.2) *
          (U + t * δ.1) / R ^ 2 + R ^ 2 / (U + t * δ.1))) / 2 := by
      funext t
      rw [malda_pe_last, hfst, hsnd, malda_mink_line]
      ring
    have h1 := hcomp (Fin.last (p + 2))
    rw [e] at h1
    exact h1.unique (malda_endcomp U δ.1 _ B _ R (-1) hU0)
  have hmid : ∀ k : Fin (p + 1), L k.castSucc.succ = (δ.2 k * U + x k * δ.1) / R := by
    intro k
    have e : (fun t : ℝ => poincareEmbedding p R ((U, x) + t • δ) k.castSucc.succ) = fun t : ℝ =>
        (x k + t * δ.2 k) * (U + t * δ.1) / R := by
      funext t
      rw [malda_pe_mid, hfst, hsnd]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := hcomp k.castSucc.succ
    rw [e] at h1
    have h2 := ((malda_lin (x k) (δ.2 k)).mul (malda_lin U δ.1)).div_const R
    have h3 := h1.unique h2
    rw [h3]
    ring
  rw [malda_ambientForm_split, h0, hlast]
  simp only [hmid]
  have hs : ∑ k : Fin (p + 1), (if k.val = 0 then (-1:ℝ) else 1) * ((δ.2 k * U + x k * δ.1) / R) ^ 2
      = (U ^ 2 * minkowskiForm p δ.2 + 2 * U * δ.1 * B + δ.1 ^ 2 * minkowskiForm p x) / R ^ 2 := by
    rw [hB]
    unfold minkowskiForm
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    ring
  rw [hs]
  field_simp
  try ring

lemma malda_tendsto_rpow (a : ℝ) (k : ℕ) (hk : k ≠ 0) (C : ℝ) (hC : 0 < C) :
    Tendsto (fun t : ℝ => (t ^ k + C) ^ a) (𝓝[>] 0) (𝓝 (C ^ a)) := by
  have hcont : Continuous (fun t : ℝ => t ^ k + C) := by fun_prop
  have h1 : Tendsto (fun t : ℝ => t ^ k + C) (𝓝 0) (𝓝 C) := by
    have := hcont.tendsto 0
    simpa [zero_pow hk] using this
  exact (h1.rpow_const (Or.inl hC.ne')).mono_left nhdsWithin_le_nhds

lemma malda_pow_rpow_nat (y : ℝ) (hy : 0 ≤ y) (n m : ℕ) (a : ℝ) (h : (n : ℝ) * a = m) :
    (y ^ n) ^ a = y ^ m := by
  rw [← Real.rpow_natCast_mul hy, h, Real.rpow_natCast]

lemma malda_pow_rpow_neg (y : ℝ) (hy : 0 ≤ y) (n m : ℕ) (a : ℝ) (h : (n : ℝ) * a = -m) :
    (y ^ n) ^ a = (y ^ m)⁻¹ := by
  rw [← Real.rpow_natCast_mul hy, h, Real.rpow_neg hy, Real.rpow_natCast]

open Maldacena1999 in
theorem malda_m5 (N : ℕ) (hN : 0 < N) (U : ℝ) (hU : 0 < U)
    (ω : EuclideanSpace ℝ (Fin 5)) (hω : ‖ω‖ = 1)
    (δU : ℝ) (δx : Fin 6 → ℝ) (δω : EuclideanSpace ℝ (Fin 5)) (hδω : inner ℝ ω δω = 0) :
    Tendsto
      (fun lp : ℝ => m5Metric N lp (U ^ 2 * lp ^ 3) δx (2 * U * lp ^ 3 * δU) δω / lp ^ 2)
      (𝓝[>] 0)
      (𝓝 (U ^ 2 / (Real.pi * N) ^ (1 / 3 : ℝ) * minkowskiForm 5 δx +
        4 * (Real.pi * N) ^ (2 / 3 : ℝ) * δU ^ 2 / U ^ 2 +
        (Real.pi * N) ^ (2 / 3 : ℝ) * ‖δω‖ ^ 2)) := by
  have hc : 0 < Real.pi * (N : ℝ) := by
    have : (0:ℝ) < N := by exact_mod_cast hN
    positivity
  have hU0 : U ≠ 0 := hU.ne'
  have hC : 0 < Real.pi * (N : ℝ) / U ^ 6 := by positivity
  have hT1 := malda_tendsto_rpow (-(1/3:ℝ)) 6 (by norm_num) _ hC
  have hT2 := malda_tendsto_rpow (2/3:ℝ) 6 (by norm_num) _ hC
  have hT := (hT1.mul_const (minkowskiForm 5 δx)).add
    (hT2.mul_const (4 * U ^ 2 * δU ^ 2 + U ^ 4 * ‖δω‖ ^ 2))
  have hval : (Real.pi * (N : ℝ) / U ^ 6) ^ (-(1/3:ℝ)) * minkowskiForm 5 δx +
      (Real.pi * (N : ℝ) / U ^ 6) ^ (2/3:ℝ) * (4 * U ^ 2 * δU ^ 2 + U ^ 4 * ‖δω‖ ^ 2) =
      U ^ 2 / (Real.pi * N) ^ (1 / 3 : ℝ) * minkowskiForm 5 δx +
        4 * (Real.pi * N) ^ (2 / 3 : ℝ) * δU ^ 2 / U ^ 2 +
        (Real.pi * N) ^ (2 / 3 : ℝ) * ‖δω‖ ^ 2 := by
    rw [Real.div_rpow hc.le (pow_nonneg hU.le 6), Real.div_rpow hc.le (pow_nonneg hU.le 6),
      malda_pow_rpow_neg U hU.le 6 2 (-(1/3)) (by norm_num),
      malda_pow_rpow_nat U hU.le 6 4 (2/3) (by norm_num), Real.rpow_neg hc.le]
    have h1 : 0 < (Real.pi * (N : ℝ)) ^ (1/3:ℝ) := Real.rpow_pos_of_pos hc _
    generalize (Real.pi * (N : ℝ)) ^ (1/3:ℝ) = a at h1 ⊢
    generalize (Real.pi * (N : ℝ)) ^ (2/3:ℝ) = b
    field_simp
    try ring
  have hev : (fun lp : ℝ => (lp ^ 6 + Real.pi * (N : ℝ) / U ^ 6) ^ (-(1/3:ℝ)) * minkowskiForm 5 δx +
      (lp ^ 6 + Real.pi * (N : ℝ) / U ^ 6) ^ (2/3:ℝ) * (4 * U ^ 2 * δU ^ 2 + U ^ 4 * ‖δω‖ ^ 2))
      =ᶠ[𝓝[>] 0]
      (fun lp : ℝ => m5Metric N lp (U ^ 2 * lp ^ 3) δx (2 * U * lp ^ 3 * δU) δω / lp ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with lp hlp
    have hlp : 0 < lp := hlp
    have hlp0 : lp ≠ 0 := hlp.ne'
    have hH : 0 < lp ^ 6 + Real.pi * (N : ℝ) / U ^ 6 := by positivity
    have hf : m5HarmonicFn N lp (U ^ 2 * lp ^ 3) =
        (lp ^ 6 + Real.pi * (N : ℝ) / U ^ 6) / (lp ^ 2) ^ 3 := by
      unfold m5HarmonicFn
      field_simp
      try ring
    unfold m5Metric
    rw [hf, Real.div_rpow hH.le (by positivity : (0:ℝ) ≤ (lp ^ 2) ^ 3),
      Real.div_rpow hH.le (by positivity : (0:ℝ) ≤ (lp ^ 2) ^ 3),
      malda_pow_rpow_neg (lp ^ 2) (by positivity) 3 1 (-(1/3)) (by norm_num),
      malda_pow_rpow_nat (lp ^ 2) (by positivity) 3 2 (2/3) (by norm_num)]
    generalize (lp ^ 6 + Real.pi * (N : ℝ) / U ^ 6) ^ (-(1/3:ℝ)) = A
    generalize (lp ^ 6 + Real.pi * (N : ℝ) / U ^ 6) ^ (2/3:ℝ) = B
    field_simp
    try ring
  rw [← hval]
  exact hT.congr' hev

open Maldacena1999 in
theorem malda_m2 (N : ℕ) (hN : 0 < N) (U : ℝ) (hU : 0 < U)
    (ω : EuclideanSpace ℝ (Fin 8)) (hω : ‖ω‖ = 1)
    (δU : ℝ) (δx : Fin 3 → ℝ) (δω : EuclideanSpace ℝ (Fin 8)) (hδω : inner ℝ ω δω = 0) :
    Tendsto
      (fun lp : ℝ => m2Metric N lp (Real.sqrt (U * lp ^ 3)) δx
        (lp ^ 3 / (2 * Real.sqrt (U * lp ^ 3)) * δU) δω / lp ^ 2)
      (𝓝[>] 0)
      (𝓝 (U ^ 2 / (2 ^ 5 * Real.pi ^ 2 * N) ^ (2 / 3 : ℝ) * minkowskiForm 2 δx +
        (2 ^ 5 * Real.pi ^ 2 * N) ^ (1 / 3 : ℝ) / 4 * δU ^ 2 / U ^ 2 +
        (2 ^ 5 * Real.pi ^ 2 * N) ^ (1 / 3 : ℝ) * ‖δω‖ ^ 2)) := by
  have hK : 0 < 2 ^ 5 * Real.pi ^ 2 * (N : ℝ) := by
    have : (0:ℝ) < N := by exact_mod_cast hN
    positivity
  have hU0 : U ≠ 0 := hU.ne'
  have hC : 0 < 2 ^ 5 * Real.pi ^ 2 * (N : ℝ) / U ^ 3 := by positivity
  have hT1 := malda_tendsto_rpow (-(2/3:ℝ)) 3 (by norm_num) _ hC
  have hT2 := malda_tendsto_rpow (1/3:ℝ) 3 (by norm_num) _ hC
  have hT := (hT1.mul_const (minkowskiForm 2 δx)).add
    (hT2.mul_const (δU ^ 2 / (4 * U) + U * ‖δω‖ ^ 2))
  have hval : (2 ^ 5 * Real.pi ^ 2 * (N : ℝ) / U ^ 3) ^ (-(2/3:ℝ)) * minkowskiForm 2 δx +
      (2 ^ 5 * Real.pi ^ 2 * (N : ℝ) / U ^ 3) ^ (1/3:ℝ) * (δU ^ 2 / (4 * U) + U * ‖δω‖ ^ 2) =
      U ^ 2 / (2 ^ 5 * Real.pi ^ 2 * N) ^ (2 / 3 : ℝ) * minkowskiForm 2 δx +
        (2 ^ 5 * Real.pi ^ 2 * N) ^ (1 / 3 : ℝ) / 4 * δU ^ 2 / U ^ 2 +
        (2 ^ 5 * Real.pi ^ 2 * N) ^ (1 / 3 : ℝ) * ‖δω‖ ^ 2 := by
    rw [Real.div_rpow hK.le (pow_nonneg hU.le 3), Real.div_rpow hK.le (pow_nonneg hU.le 3),
      malda_pow_rpow_neg U hU.le 3 2 (-(2/3)) (by norm_num),
      malda_pow_rpow_nat U hU.le 3 1 (1/3) (by norm_num), Real.rpow_neg hK.le]
    have h1 : 0 < (2 ^ 5 * Real.pi ^ 2 * (N : ℝ)) ^ (2/3:ℝ) := Real.rpow_pos_of_pos hK _
    generalize (2 ^ 5 * Real.pi ^ 2 * (N : ℝ)) ^ (2/3:ℝ) = a at h1 ⊢
    generalize (2 ^ 5 * Real.pi ^ 2 * (N : ℝ)) ^ (1/3:ℝ) = b
    field_simp
    try ring
  have hev : (fun lp : ℝ => (lp ^ 3 + 2 ^ 5 * Real.pi ^ 2 * (N : ℝ) / U ^ 3) ^ (-(2/3:ℝ)) *
      minkowskiForm 2 δx + (lp ^ 3 + 2 ^ 5 * Real.pi ^ 2 * (N : ℝ) / U ^ 3) ^ (1/3:ℝ) *
      (δU ^ 2 / (4 * U) + U * ‖δω‖ ^ 2))
      =ᶠ[𝓝[>] 0]
      (fun lp : ℝ => m2Metric N lp (Real.sqrt (U * lp ^ 3)) δx
        (lp ^ 3 / (2 * Real.sqrt (U * lp ^ 3)) * δU) δω / lp ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with lp hlp
    have hlp : 0 < lp := hlp
    have hlp0 : lp ≠ 0 := hlp.ne'
    have hH : 0 < lp ^ 3 + 2 ^ 5 * Real.pi ^ 2 * (N : ℝ) / U ^ 3 := by positivity
    have hs2 : Real.sqrt (U * lp ^ 3) ^ 2 = U * lp ^ 3 := Real.sq_sqrt (by positivity)
    have hf : m2HarmonicFn N lp (Real.sqrt (U * lp ^ 3)) =
        (lp ^ 3 + 2 ^ 5 * Real.pi ^ 2 * (N : ℝ) / U ^ 3) / lp ^ 3 := by
      unfold m2HarmonicFn
      rw [show Real.sqrt (U * lp ^ 3) ^ 6 = (Real.sqrt (U * lp ^ 3) ^ 2) ^ 3 by ring, hs2]
      field_simp
      try ring
    unfold m2Metric
    rw [hf, Real.div_rpow hH.le (pow_nonneg hlp.le 3), Real.div_rpow hH.le (pow_nonneg hlp.le 3),
      malda_pow_rpow_neg lp hlp.le 3 2 (-(2/3)) (by norm_num),
      malda_pow_rpow_nat lp hlp.le 3 1 (1/3) (by norm_num)]
    simp only [mul_pow, div_pow, hs2]
    generalize (lp ^ 3 + 2 ^ 5 * Real.pi ^ 2 * (N : ℝ) / U ^ 3) ^ (-(2/3:ℝ)) = A
    generalize (lp ^ 3 + 2 ^ 5 * Real.pi ^ 2 * (N : ℝ) / U ^ 3) ^ (1/3:ℝ) = B
    field_simp
    try ring
  rw [← hval]
  exact hT.congr' hev

open Maldacena1999 in
theorem malda_d1d5 (g v : ℝ) (hg : 0 < g) (hv : 0 < v)
    (Q1 Q5 : ℕ) (hQ1 : 0 < Q1) (hQ5 : 0 < Q5) (U : ℝ) (hU : 0 < U)
    (ω : EuclideanSpace ℝ (Fin 4)) (hω : ‖ω‖ = 1)
    (δU : ℝ) (δx : Fin 2 → ℝ) (δω : EuclideanSpace ℝ (Fin 4)) (hδω : inner ℝ ω δω = 0) :
    Tendsto
      (fun α' : ℝ => d1d5Metric g v Q1 Q5 α' (α' * U) δx (α' * δU) δω / α')
      (𝓝[>] 0)
      (𝓝 (U ^ 2 / (g / Real.sqrt v * Real.sqrt (Q1 * Q5)) * minkowskiForm 1 δx +
        g / Real.sqrt v * Real.sqrt (Q1 * Q5) * δU ^ 2 / U ^ 2 +
        g / Real.sqrt v * Real.sqrt (Q1 * Q5) * ‖δω‖ ^ 2)) := by
  have hq1 : (0:ℝ) < Q1 := by exact_mod_cast hQ1
  have hq5 : (0:ℝ) < Q5 := by exact_mod_cast hQ5
  have hU0 : U ≠ 0 := hU.ne'
  have hv0 : v ≠ 0 := hv.ne'
  have hC1 : 0 < g * Q1 / (v * U ^ 2) := by positivity
  have hC5 : 0 < g * Q5 / U ^ 2 := by positivity
  have hT1a := (malda_tendsto_rpow (-(1/2:ℝ)) 1 one_ne_zero _ hC1).congr (fun t => by rw [pow_one])
  have hT5a := (malda_tendsto_rpow (-(1/2:ℝ)) 1 one_ne_zero _ hC5).congr (fun t => by rw [pow_one])
  have hT1b := (malda_tendsto_rpow (1/2:ℝ) 1 one_ne_zero _ hC1).congr (fun t => by rw [pow_one])
  have hT5b := (malda_tendsto_rpow (1/2:ℝ) 1 one_ne_zero _ hC5).congr (fun t => by rw [pow_one])
  have hT := ((hT1a.mul hT5a).mul_const (minkowskiForm 1 δx)).add
    ((hT1b.mul hT5b).mul_const (δU ^ 2 + U ^ 2 * ‖δω‖ ^ 2))
  have hG : 0 < g / Real.sqrt v * Real.sqrt (Q1 * Q5) := by
    have : 0 < Real.sqrt ((Q1:ℝ) * Q5) := Real.sqrt_pos.2 (by positivity)
    have : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
    positivity
  have hprod : Real.sqrt (g * Q1 / (v * U ^ 2)) * Real.sqrt (g * Q5 / U ^ 2) =
      g / Real.sqrt v * Real.sqrt (Q1 * Q5) / U ^ 2 := by
    rw [← Real.sqrt_mul hC1.le]
    have e : g * Q1 / (v * U ^ 2) * (g * Q5 / U ^ 2) =
        (g / Real.sqrt v * Real.sqrt (Q1 * Q5) / U ^ 2) ^ 2 := by
      rw [div_pow, mul_pow, div_pow, Real.sq_sqrt hv.le, Real.sq_sqrt (by positivity)]
      field_simp
      try ring
    rw [e, Real.sqrt_sq (by positivity)]
  have hval : (g * Q1 / (v * U ^ 2)) ^ (-(1/2:ℝ)) * (g * Q5 / U ^ 2) ^ (-(1/2:ℝ)) *
      minkowskiForm 1 δx + (g * Q1 / (v * U ^ 2)) ^ (1/2:ℝ) * (g * Q5 / U ^ 2) ^ (1/2:ℝ) *
      (δU ^ 2 + U ^ 2 * ‖δω‖ ^ 2) =
      U ^ 2 / (g / Real.sqrt v * Real.sqrt (Q1 * Q5)) * minkowskiForm 1 δx +
        g / Real.sqrt v * Real.sqrt (Q1 * Q5) * δU ^ 2 / U ^ 2 +
        g / Real.sqrt v * Real.sqrt (Q1 * Q5) * ‖δω‖ ^ 2 := by
    rw [Real.rpow_neg hC1.le, Real.rpow_neg hC5.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
      ← mul_inv, hprod]
    generalize g / Real.sqrt v * Real.sqrt (Q1 * Q5) = G at hG ⊢
    field_simp
    try ring
  have hev : (fun a : ℝ => (a + g * Q1 / (v * U ^ 2)) ^ (-(1/2:ℝ)) *
      (a + g * Q5 / U ^ 2) ^ (-(1/2:ℝ)) * minkowskiForm 1 δx +
      (a + g * Q1 / (v * U ^ 2)) ^ (1/2:ℝ) * (a + g * Q5 / U ^ 2) ^ (1/2:ℝ) *
      (δU ^ 2 + U ^ 2 * ‖δω‖ ^ 2))
      =ᶠ[𝓝[>] 0]
      (fun α' : ℝ => d1d5Metric g v Q1 Q5 α' (α' * U) δx (α' * δU) δω / α') := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have ha : 0 < a := ha
    have ha0 : a ≠ 0 := ha.ne'
    have h1 : 0 < a + g * Q1 / (v * U ^ 2) := by positivity
    have h5 : 0 < a + g * Q5 / U ^ 2 := by positivity
    have hf1 : d1HarmonicFn g v Q1 a (a * U) = (a + g * Q1 / (v * U ^ 2)) / a := by
      unfold d1HarmonicFn
      field_simp
      try ring
    have hf5 : d5HarmonicFn g Q5 a (a * U) = (a + g * Q5 / U ^ 2) / a := by
      unfold d5HarmonicFn
      field_simp
      try ring
    unfold d1d5Metric
    rw [hf1, hf5, Real.div_rpow h1.le ha.le, Real.div_rpow h5.le ha.le,
      Real.div_rpow h1.le ha.le, Real.div_rpow h5.le ha.le, Real.rpow_neg ha.le,
      ← Real.sqrt_eq_rpow a]
    generalize (a + g * Q1 / (v * U ^ 2)) ^ (-(1/2:ℝ)) = A1
    generalize (a + g * Q5 / U ^ 2) ^ (-(1/2:ℝ)) = A5
    generalize (a + g * Q1 / (v * U ^ 2)) ^ (1/2:ℝ) = B1
    generalize (a + g * Q5 / U ^ 2) ^ (1/2:ℝ) = B5
    have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
    have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
    generalize Real.sqrt a = s at hsa hs ⊢
    subst hsa
    have hs0 : s ≠ 0 := hs.ne'
    field_simp
    try ring
  rw [← hval]
  exact hT.congr' hev

open Maldacena1999 Filter Topology in
theorem solution :
    -- M5-branes: `AdS₇ × S⁴` with `R_sph = R_AdS / 2 = l_p (π N)^{1/3}`
    (∀ (N : ℕ), 0 < N → ∀ (U : ℝ), 0 < U → ∀ (x : Fin 6 → ℝ)
      (ω : EuclideanSpace ℝ (Fin 5)), ‖ω‖ = 1 →
      ∀ (δU : ℝ) (δx : Fin 6 → ℝ) (δω : EuclideanSpace ℝ (Fin 5)), inner ℝ ω δω = 0 →
      Tendsto
        (fun lp : ℝ => m5Metric N lp (U ^ 2 * lp ^ 3) δx (2 * U * lp ^ 3 * δU) δω / lp ^ 2)
        (𝓝[>] 0)
        (𝓝 (ambientForm 5 (fderiv ℝ (poincareEmbedding 5 (2 * (Real.pi * N) ^ (1 / 3 : ℝ)))
              (2 * (Real.pi * N) ^ (1 / 6 : ℝ) * U, x)
              (2 * (Real.pi * N) ^ (1 / 6 : ℝ) * δU, δx)) +
          ‖(Real.pi * N) ^ (1 / 3 : ℝ) • δω‖ ^ 2))) ∧
    -- M2-branes: `AdS₄ × S⁷` with `R_sph = 2 R_AdS = l_p (2⁵ π² N)^{1/6}`
    (∀ (N : ℕ), 0 < N → ∀ (U : ℝ), 0 < U → ∀ (x : Fin 3 → ℝ)
      (ω : EuclideanSpace ℝ (Fin 8)), ‖ω‖ = 1 →
      ∀ (δU : ℝ) (δx : Fin 3 → ℝ) (δω : EuclideanSpace ℝ (Fin 8)), inner ℝ ω δω = 0 →
      Tendsto
        (fun lp : ℝ => m2Metric N lp (Real.sqrt (U * lp ^ 3)) δx
          (lp ^ 3 / (2 * Real.sqrt (U * lp ^ 3)) * δU) δω / lp ^ 2)
        (𝓝[>] 0)
        (𝓝 (ambientForm 2
              (fderiv ℝ (poincareEmbedding 2 ((2 ^ 5 * Real.pi ^ 2 * N) ^ (1 / 6 : ℝ) / 2))
                (U / (2 * (2 ^ 5 * Real.pi ^ 2 * N) ^ (1 / 6 : ℝ)), x)
                (δU / (2 * (2 ^ 5 * Real.pi ^ 2 * N) ^ (1 / 6 : ℝ)), δx)) +
          ‖(2 ^ 5 * Real.pi ^ 2 * N) ^ (1 / 6 : ℝ) • δω‖ ^ 2))) ∧
    -- D1–D5 system: `AdS₃ × S³` with `R_sph² = R_AdS² = α' g₆ √(Q₁ Q₅)`, `g₆ = g / √v`
    (∀ (g v : ℝ), 0 < g → 0 < v → ∀ (Q1 Q5 : ℕ), 0 < Q1 → 0 < Q5 →
      ∀ (U : ℝ), 0 < U → ∀ (x : Fin 2 → ℝ) (ω : EuclideanSpace ℝ (Fin 4)), ‖ω‖ = 1 →
      ∀ (δU : ℝ) (δx : Fin 2 → ℝ) (δω : EuclideanSpace ℝ (Fin 4)), inner ℝ ω δω = 0 →
      Tendsto
        (fun α' : ℝ => d1d5Metric g v Q1 Q5 α' (α' * U) δx (α' * δU) δω / α')
        (𝓝[>] 0)
        (𝓝 (ambientForm 1
              (fderiv ℝ (poincareEmbedding 1
                (Real.sqrt (g / Real.sqrt v * Real.sqrt (Q1 * Q5)))) (U, x) (δU, δx)) +
          ‖Real.sqrt (g / Real.sqrt v * Real.sqrt (Q1 * Q5)) • δω‖ ^ 2))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro N hN U hU x ω hω δU δx δω hδω
    have hc : 0 < Real.pi * (N : ℝ) := by
      have : (0:ℝ) < N := by exact_mod_cast hN
      positivity
    have hs : 0 < (Real.pi * (N : ℝ)) ^ (1/6:ℝ) := Real.rpow_pos_of_pos hc _
    have e1 : (Real.pi * (N : ℝ)) ^ (1/3:ℝ) = ((Real.pi * (N : ℝ)) ^ (1/6:ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast ((Real.pi * (N : ℝ)) ^ (1/6:ℝ)) 2, ← Real.rpow_mul hc.le]
      norm_num
    have e2 : (Real.pi * (N : ℝ)) ^ (2/3:ℝ) = ((Real.pi * (N : ℝ)) ^ (1/6:ℝ)) ^ 4 := by
      rw [← Real.rpow_natCast ((Real.pi * (N : ℝ)) ^ (1/6:ℝ)) 4, ← Real.rpow_mul hc.le]
      norm_num
    have hR5 : 0 < 2 * (Real.pi * (N : ℝ)) ^ (1/3:ℝ) := by rw [e1]; positivity
    have hU5 : 0 < 2 * (Real.pi * (N : ℝ)) ^ (1/6:ℝ) * U := by positivity
    have h := malda_m5 N hN U hU ω hω δU δx δω hδω
    convert h using 2
    rw [malda_induced_metric 5 _ hR5 _ hU5 x]
    dsimp only
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hc (1/3:ℝ)), e1, e2]
    generalize (Real.pi * (N : ℝ)) ^ (1/6:ℝ) = s at hs ⊢
    have hU0 : U ≠ 0 := hU.ne'
    have hs0 : s ≠ 0 := hs.ne'
    field_simp
    try ring
  · intro N hN U hU x ω hω δU δx δω hδω
    have hK : 0 < 2 ^ 5 * Real.pi ^ 2 * (N : ℝ) := by
      have : (0:ℝ) < N := by exact_mod_cast hN
      positivity
    have hs : 0 < (2 ^ 5 * Real.pi ^ 2 * (N : ℝ)) ^ (1/6:ℝ) := Real.rpow_pos_of_pos hK _
    have e1 : (2 ^ 5 * Real.pi ^ 2 * (N : ℝ)) ^ (1/3:ℝ) =
        ((2 ^ 5 * Real.pi ^ 2 * (N : ℝ)) ^ (1/6:ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast ((2 ^ 5 * Real.pi ^ 2 * (N : ℝ)) ^ (1/6:ℝ)) 2,
        ← Real.rpow_mul hK.le]
      norm_num
    have e2 : (2 ^ 5 * Real.pi ^ 2 * (N : ℝ)) ^ (2/3:ℝ) =
        ((2 ^ 5 * Real.pi ^ 2 * (N : ℝ)) ^ (1/6:ℝ)) ^ 4 := by
      rw [← Real.rpow_natCast ((2 ^ 5 * Real.pi ^ 2 * (N : ℝ)) ^ (1/6:ℝ)) 4,
        ← Real.rpow_mul hK.le]
      norm_num
    have hR2 : 0 < (2 ^ 5 * Real.pi ^ 2 * (N : ℝ)) ^ (1/6:ℝ) / 2 := by positivity
    have hU2 : 0 < U / (2 * (2 ^ 5 * Real.pi ^ 2 * (N : ℝ)) ^ (1/6:ℝ)) := by positivity
    have h := malda_m2 N hN U hU ω hω δU δx δω hδω
    convert h using 2
    rw [malda_induced_metric 2 _ hR2 _ hU2 x]
    dsimp only
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, e1, e2]
    generalize (2 ^ 5 * Real.pi ^ 2 * (N : ℝ)) ^ (1/6:ℝ) = s at hs ⊢
    have hU0 : U ≠ 0 := hU.ne'
    have hs0 : s ≠ 0 := hs.ne'
    field_simp
    try ring
  · intro g v hg hv Q1 Q5 hQ1 hQ5 U hU x ω hω δU δx δω hδω
    have hG : 0 < g / Real.sqrt v * Real.sqrt (Q1 * Q5) := by
      have hq1 : (0:ℝ) < Q1 := by exact_mod_cast hQ1
      have hq5 : (0:ℝ) < Q5 := by exact_mod_cast hQ5
      have : 0 < Real.sqrt ((Q1:ℝ) * Q5) := Real.sqrt_pos.2 (by positivity)
      have : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
      positivity
    have h := malda_d1d5 g v hg hv Q1 Q5 hQ1 hQ5 U hU ω hω δU δx δω hδω
    convert h using 2
    rw [malda_induced_metric 1 _ (Real.sqrt_pos.2 hG) _ hU x]
    dsimp only
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 hG), mul_pow,
      Real.sq_sqrt hG.le]
