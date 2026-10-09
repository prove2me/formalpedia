-- Prove2me | solution 1 for IntMul.HvdH.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T09:09:53.133983+00:00
-- url     : https://prove2.me/submissions/698e730b-a429-41aa-b030-8cbfb5129ea7

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

open scoped BigOperators

-- A principal nth root gives an additive character on the cyclic group ZMod n.
private def phase {R : Type*} [CommRing R] {n : ℕ} (ω : Rˣ) (a : ZMod n) : R :=
  ↑(ω ^ a.val)

private lemma phase_int {R : Type*} [CommRing R] {n : ℕ} [NeZero n]
    (ω : Rˣ) (hω : ω ^ n = 1) (a : ℤ) :
    phase ω (a : ZMod n) = ((ω ^ a : Rˣ) : R) := by
  unfold phase
  rw [← zpow_natCast, ZMod.val_intCast, ← zpow_eq_zpow_emod' a hω]

private lemma phase_add {R : Type*} [CommRing R] {n : ℕ} [NeZero n]
    (ω : Rˣ) (hω : ω ^ n = 1) (a b : ZMod n) :
    phase ω (a + b) = phase ω a * phase ω b := by
  unfold phase
  rw [ZMod.val_add, ← pow_eq_pow_mod (a.val + b.val) hω, pow_add]
  simp

private lemma sum_zmod_val {R : Type*} [AddCommMonoid R] {n : ℕ} [NeZero n]
    (f : ℕ → R) :
    (∑ k : ZMod n, f k.val) = ∑ k ∈ Finset.range n, f k := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact Fin.sum_univ_eq_sum_range f (n + 1)

-- Orthogonality follows from the supplied geometric-sum hypothesis, even over rings.
private lemma phase_orthogonal {R : Type*} [CommRing R] {n : ℕ} [NeZero n]
    (ω : Rˣ) (hω : ω ^ n = 1)
    (hsum : ∀ j : ℤ, ¬ (n : ℤ) ∣ j →
      ∑ k ∈ Finset.range n, ((ω ^ j : Rˣ) : R) ^ k = 0)
    (a : ZMod n) :
    (∑ k : ZMod n, phase ω (k * a)) = if a = 0 then (n : R) else 0 := by
  classical
  have hp (k : ZMod n) : phase ω (k * a) = ((ω ^ (a.val : ℤ) : Rˣ) : R) ^ k.val := by
    have hc : (((a.val : ℤ) * (k.val : ℤ) : ℤ) : ZMod n) = k * a := by
      simp [mul_comm]
    rw [← hc, phase_int ω hω, zpow_mul, zpow_natCast]
    simp
  simp_rw [hp]
  rw [sum_zmod_val]
  by_cases ha : a = 0
  · subst a
    simp
  · rw [if_neg ha]
    apply hsum
    intro hd
    have hz : ((a.val : ℤ) : ZMod n) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (a.val : ℤ) n).mpr hd
    exact ha (by simpa using hz)

private def minusTransform {R : Type*} [CommRing R] {n : ℕ} [NeZero n]
    (ω : Rˣ) (x : ZMod n → R) (j : ZMod n) : R :=
  ∑ k : ZMod n, phase ω (-j * k) * x k

private def plusTransform {R : Type*} [CommRing R] {n : ℕ} [NeZero n]
    (ω : Rˣ) (x : ZMod n → R) (j : ZMod n) : R :=
  ∑ k : ZMod n, phase ω (j * k) * x k

private def convolution {R : Type*} [CommRing R] {n : ℕ} [NeZero n]
    (u v : ZMod n → R) (j : ZMod n) : R :=
  ∑ k : ZMod n, u k * v (j - k)

-- The unnormalized transform takes convolution to pointwise multiplication.
private lemma transform_convolution {R : Type*} [CommRing R] {n : ℕ} [NeZero n]
    (ω : Rˣ) (hω : ω ^ n = 1) (u v : ZMod n → R) (j : ZMod n) :
    minusTransform ω (convolution u v) j =
      minusTransform ω u j * minusTransform ω v j := by
  classical
  unfold minusTransform convolution
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ b : ZMod n, ∑ a : ZMod n, phase ω (-j * a) * (u b * v (a - b))) =
        ∑ b : ZMod n, ∑ c : ZMod n,
          (phase ω (-j * b) * u b) * (phase ω (-j * c) * v c) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [← Equiv.sum_comp (Equiv.addLeft b)
        (fun a : ZMod n => phase ω (-j * a) * (u b * v (a - b)))]
      apply Finset.sum_congr rfl
      intro c _
      change phase ω (-j * (b + c)) * (u b * v (b + c - b)) = _
      simp only [add_sub_cancel_left, mul_add, phase_add ω hω]
      ring
    _ = _ := by simp_rw [← Finset.mul_sum]; rw [← Finset.sum_mul]

-- Applying the opposite-sign transform multiplies the input by n.
private lemma transform_inversion {R : Type*} [CommRing R] {n : ℕ} [NeZero n]
    (ω : Rˣ) (hω : ω ^ n = 1)
    (hsum : ∀ j : ℤ, ¬ (n : ℤ) ∣ j →
      ∑ k ∈ Finset.range n, ((ω ^ j : Rˣ) : R) ^ k = 0)
    (x : ZMod n → R) (j : ZMod n) :
    plusTransform ω (minusTransform ω x) j = (n : R) * x j := by
  classical
  unfold plusTransform minusTransform
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ t : ZMod n, ∑ s : ZMod n,
      phase ω (j * s) * (phase ω (-s * t) * x t)) =
        ∑ t : ZMod n, (∑ s : ZMod n, phase ω (s * (j - t))) * x t := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      rw [← mul_assoc, ← phase_add ω hω]
      congr 2
      ring
    _ = _ := by
      simp_rw [phase_orthogonal ω hω hsum, sub_eq_zero, ite_mul, zero_mul]
      simp

private lemma kernel_minus {R : Type*} [CommRing R] {n : ℕ} [NeZero n]
    (ω : Rˣ) (hω : ω ^ n = 1) (j k : ZMod n) :
    ((ω ^ (-((j.val * k.val : ℕ) : ℤ)) : Rˣ) : R) = phase ω (-j * k) := by
  have hc : ((-((j.val * k.val : ℕ) : ℤ) : ℤ) : ZMod n) = -j * k := by
    simp
  rw [← hc, phase_int ω hω]

private lemma kernel_plus {R : Type*} [CommRing R] {n : ℕ} [NeZero n]
    (ω : Rˣ) (hω : ω ^ n = 1) (j k : ZMod n) :
    (((ω⁻¹) ^ (-((j.val * k.val : ℕ) : ℤ)) : Rˣ) : R) = phase ω (j * k) := by
  have hc : (((j.val * k.val : ℕ) : ℤ) : ZMod n) = j * k := by
    simp
  rw [inv_zpow, zpow_neg, inv_inv, ← hc, phase_int ω hω]

private lemma plusTransform_mul {R : Type*} [CommRing R] {n : ℕ} [NeZero n]
    (ω : Rˣ) (c : R) (x : ZMod n → R) (j : ZMod n) :
    plusTransform ω (fun k => c * x k) j = c * plusTransform ω x j := by
  unfold plusTransform
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

-- Exact type of IntMul.HvdH.lemma_2_3; all auxiliary results above are proved.
theorem solution {R : Type*} [CommRing R] [Algebra ℂ R] (n : ℕ) [NeZero n] (ω : Rˣ)
    (hω : ω ^ n = 1)
    (hsum : ∀ j : ℤ, ¬ (n : ℤ) ∣ j → ∑ k ∈ Finset.range n, ((ω ^ j : Rˣ) : R) ^ k = 0)
    (u v : ZMod n → R) :
    let F : Rˣ → (ZMod n → R) → ZMod n → R := fun w x j =>
      (1 / (n : ℂ)) • ∑ k : ZMod n, ((w ^ (-((j.val * k.val : ℕ) : ℤ)) : Rˣ) : R) * x k
    (1 / (n : ℂ)) • (fun j => ∑ k : ZMod n, u k * v (j - k)) =
      (n : ℂ) • F ω⁻¹ (fun j => F ω u j * F ω v j) := by
  classical
  let F : Rˣ → (ZMod n → R) → ZMod n → R := fun w x j =>
    (1 / (n : ℂ)) • ∑ k : ZMod n, ((w ^ (-((j.val * k.val : ℕ) : ℤ)) : Rˣ) : R) * x k
  change (1 / (n : ℂ)) • convolution u v =
    (n : ℂ) • F ω⁻¹ (fun j => F ω u j * F ω v j)
  let a : R := algebraMap ℂ R (1 / (n : ℂ))
  let b : R := algebraMap ℂ R (n : ℂ)
  have hb : b = (n : R) := by simp [b]
  have hba : b * a = 1 := by
    dsimp [b, a]
    rw [← map_mul]
    have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
    simp [hn]
  have hF (x : ZMod n → R) : F ω x = fun j => a * minusTransform ω x j := by
    funext j
    simp only [F, Algebra.smul_def, kernel_minus ω hω, minusTransform, a]
  have hFi (x : ZMod n → R) : F ω⁻¹ x = fun j => a * plusTransform ω x j := by
    funext j
    simp only [F, Algebra.smul_def, kernel_plus ω hω, plusTransform, a]
  rw [hFi, hF u, hF v]
  funext j
  simp only [Pi.smul_apply, Algebra.smul_def]
  change a * convolution u v j = b * (a * plusTransform ω
    (fun k => (a * minusTransform ω u k) * (a * minusTransform ω v k)) j)
  have hp : (fun k => (a * minusTransform ω u k) * (a * minusTransform ω v k)) =
      fun k => (a * a) * minusTransform ω (convolution u v) k := by
    funext k
    rw [transform_convolution ω hω]
    ring
  rw [hp, plusTransform_mul, transform_inversion ω hω hsum, ← hb]
  calc
    a * convolution u v j = (b * a) * (b * a) * a * convolution u v j := by
      rw [hba]
      ring
    _ = b * (a * (a * a * (b * convolution u v j))) := by ring
