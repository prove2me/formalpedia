-- Prove2me | solution 1 for Maldacena1999.near_horizon_limit_AdS5_S5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T13:15:05.385315+00:00
-- url     : https://prove2.me/submissions/0b94d537-6e68-4183-98f2-25ac7841c97d

import Mathlib
import Definitions.Def_Maldacena1999_Defs

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

lemma malda_sqrt_harm_mul (g : ℝ) (N : ℕ) (U : ℝ) (hU : 0 < U) (a : ℝ) (ha : 0 < a) :
    Real.sqrt (Maldacena1999.harmonicFn g N a (a * U)) * a =
      Real.sqrt (a ^ 2 + 4 * Real.pi * g * N / U ^ 4) := by
  unfold Maldacena1999.harmonicFn
  rw [← Real.sqrt_sq ha.le, ← Real.sqrt_mul' _ (sq_nonneg a), Real.sqrt_sq ha.le]
  congr 1
  field_simp

lemma malda_tendsto_H (c : ℝ) :
    Tendsto (fun a : ℝ => Real.sqrt (a ^ 2 + c)) (𝓝[>] 0) (𝓝 (Real.sqrt c)) := by
  have hc : Continuous (fun a : ℝ => Real.sqrt (a ^ 2 + c)) := by fun_prop
  have := hc.tendsto 0
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at this
  exact this.mono_left nhdsWithin_le_nhds

open Maldacena1999 Filter Topology in
theorem solution (g : ℝ) (hg : 0 < g) (N : ℕ) (hN : 0 < N)
    (R : ℝ) (hR : 0 < R) (hR4 : R ^ 4 = 4 * Real.pi * g * N)
    (U : ℝ) (hU : 0 < U) (x : Fin 4 → ℝ)
    (ω : EuclideanSpace ℝ (Fin 6)) (hω : ‖ω‖ = 1)
    (δU : ℝ) (δx : Fin 4 → ℝ) (δω : EuclideanSpace ℝ (Fin 6)) (hδω : inner ℝ ω δω = 0) :
    Tendsto (fun α' : ℝ => d3Metric g N α' (α' * U) δx (α' * δU) δω / α') (𝓝[>] 0)
      (𝓝 (ambientForm 3 (fderiv ℝ (poincareEmbedding 3 R) (U, x) (δU, δx)) +
        ‖R • δω‖ ^ 2)) := by
  rw [malda_induced_metric 3 R hR U hU x (δU, δx)]
  dsimp only
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  have hU0 : U ≠ 0 := hU.ne'
  have hR0 : R ≠ 0 := hR.ne'
  have hlim : Real.sqrt (4 * Real.pi * g * N / U ^ 4) = R ^ 2 / U ^ 2 := by
    rw [← hR4, show R ^ 4 / U ^ 4 = (R ^ 2 / U ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hT := malda_tendsto_H (4 * Real.pi * g * N / U ^ 4)
  rw [hlim] at hT
  have hT' := ((hT.inv₀ (by positivity)).mul_const (minkowskiForm 3 δx)).add
    (hT.mul_const (δU ^ 2 + U ^ 2 * ‖δω‖ ^ 2))
  have hval : (R ^ 2 / U ^ 2)⁻¹ * minkowskiForm 3 δx + R ^ 2 / U ^ 2 * (δU ^ 2 + U ^ 2 * ‖δω‖ ^ 2)
      = U ^ 2 / R ^ 2 * minkowskiForm 3 δx + R ^ 2 * δU ^ 2 / U ^ 2 + (R * ‖δω‖) ^ 2 := by
    field_simp
    try ring
  rw [← hval]
  refine hT'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  have ha : 0 < a := ha
  have e := malda_sqrt_harm_mul g N U hU a ha
  have hf : 0 < harmonicFn g N a (a * U) := by
    unfold harmonicFn
    have : (0:ℝ) < N := by exact_mod_cast hN
    positivity
  have hs : 0 < Real.sqrt (harmonicFn g N a (a * U)) := Real.sqrt_pos.2 hf
  unfold d3Metric
  rw [← e]
  generalize Real.sqrt (harmonicFn g N a (a * U)) = s at hs ⊢
  have ha0 : a ≠ 0 := ha.ne'
  have hs0 : s ≠ 0 := hs.ne'
  field_simp
  try ring
