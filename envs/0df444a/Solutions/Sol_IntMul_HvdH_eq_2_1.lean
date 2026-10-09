-- Prove2me | solution 1 for IntMul.HvdH.eq_2_1
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T09:44:34.513652+00:00
-- url     : https://prove2.me/submissions/a867c6f5-1d0d-4e99-8319-9ace900ab602

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

-- The root-of-unity phase is well defined on each cyclic group.
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

private def multiPhase {R : Type*} [CommRing R] {d : ℕ}
    (n : Fin d → ℕ) (ω : Fin d → Rˣ) (a : (i : Fin d) → ZMod (n i)) : R :=
  ∏ i, phase (ω i) (a i)

private lemma multiPhase_add {R : Type*} [CommRing R] {d : ℕ}
    (n : Fin d → ℕ) [∀ i, NeZero (n i)] (ω : Fin d → Rˣ)
    (hω : ∀ i, ω i ^ n i = 1) (a b : (i : Fin d) → ZMod (n i)) :
    multiPhase n ω (a + b) = multiPhase n ω a * multiPhase n ω b := by
  unfold multiPhase
  calc
    (∏ i, phase (ω i) ((a + b) i)) =
        ∏ i, phase (ω i) (a i) * phase (ω i) (b i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact phase_add (ω i) (hω i) (a i) (b i)
    _ = _ := Finset.prod_mul_distrib

-- The multidimensional character sum factors into the one-dimensional sums.
private lemma multiPhase_orthogonal {R : Type*} [CommRing R] {d : ℕ}
    (n : Fin d → ℕ) [∀ i, NeZero (n i)] (ω : Fin d → Rˣ)
    (hω : ∀ i, ω i ^ n i = 1)
    (hsum : ∀ i, ∀ j : ℤ, ¬ (n i : ℤ) ∣ j →
      ∑ k ∈ Finset.range (n i), ((ω i ^ j : Rˣ) : R) ^ k = 0)
    (a : (i : Fin d) → ZMod (n i)) :
    (∑ k : (i : Fin d) → ZMod (n i), multiPhase n ω (k * a)) =
      if a = 0 then (∏ i, (n i : R)) else 0 := by
  classical
  unfold multiPhase
  change (∑ k : (i : Fin d) → ZMod (n i), ∏ i, phase (ω i) (k i * a i)) = _
  rw [← Fintype.prod_sum (fun (i : Fin d) (k : ZMod (n i)) => phase (ω i) (k * a i))]
  have ho (i : Fin d) : (∑ k : ZMod (n i), phase (ω i) (k * a i)) =
      if a i = 0 then (n i : R) else 0 :=
    phase_orthogonal (ω i) (hω i) (hsum i) (a i)
  simp_rw [ho]
  by_cases ha : a = 0
  · subst a
    simp
  · rw [if_neg ha]
    have he : ∃ i, a i ≠ 0 := by
      by_contra! h
      apply ha
      funext i
      exact h i
    obtain ⟨i, hi⟩ := he
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

-- The following finite-sum identities apply to the product ring of residues.
private def minusTransform {A R : Type*} [CommRing A] [Fintype A] [CommRing R]
    (χ : A → R) (x : A → R) (j : A) : R :=
  ∑ k : A, χ (-j * k) * x k

private def plusTransform {A R : Type*} [CommRing A] [Fintype A] [CommRing R]
    (χ : A → R) (x : A → R) (j : A) : R :=
  ∑ k : A, χ (j * k) * x k

private def convolution {A R : Type*} [CommRing A] [Fintype A] [CommRing R]
    (u v : A → R) (j : A) : R :=
  ∑ k : A, u k * v (j - k)

private lemma transform_convolution {A R : Type*} [CommRing A] [Fintype A] [CommRing R]
    (χ : A → R) (hχ : ∀ a b, χ (a + b) = χ a * χ b) (u v : A → R) (j : A) :
    minusTransform χ (convolution u v) j = minusTransform χ u j * minusTransform χ v j := by
  classical
  unfold minusTransform convolution
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ b : A, ∑ a : A, χ (-j * a) * (u b * v (a - b))) =
        ∑ b : A, ∑ c : A, (χ (-j * b) * u b) * (χ (-j * c) * v c) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [← Equiv.sum_comp (Equiv.addLeft b)
        (fun a : A => χ (-j * a) * (u b * v (a - b)))]
      apply Finset.sum_congr rfl
      intro c _
      change χ (-j * (b + c)) * (u b * v (b + c - b)) = _
      simp only [add_sub_cancel_left, mul_add, hχ]
      ring
    _ = _ := by simp_rw [← Finset.mul_sum]; rw [← Finset.sum_mul]

private lemma transform_inversion {A R : Type*} [CommRing A] [Fintype A] [DecidableEq A]
    [CommRing R]
    (χ : A → R) (hχ : ∀ a b, χ (a + b) = χ a * χ b) (B : R)
    (ho : ∀ a, (∑ k : A, χ (k * a)) = if a = 0 then B else 0)
    (x : A → R) (j : A) :
    plusTransform χ (minusTransform χ x) j = B * x j := by
  classical
  unfold plusTransform minusTransform
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ t : A, ∑ s : A, χ (j * s) * (χ (-s * t) * x t)) =
        ∑ t : A, (∑ s : A, χ (s * (j - t))) * x t := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      rw [← mul_assoc, ← hχ]
      congr 2
      ring
    _ = _ := by
      simp_rw [ho, sub_eq_zero, ite_mul, zero_mul]
      simp

private lemma plusTransform_mul {A R : Type*} [CommRing A] [Fintype A] [CommRing R]
    (χ : A → R) (c : R) (x : A → R) (j : A) :
    plusTransform χ (fun k => c * x k) j = c * plusTransform χ x j := by
  unfold plusTransform
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

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

private lemma multiKernel_minus {R : Type*} [CommRing R] {d : ℕ}
    (n : Fin d → ℕ) [∀ i, NeZero (n i)] (ω : Fin d → Rˣ)
    (hω : ∀ i, ω i ^ n i = 1) (j k : (i : Fin d) → ZMod (n i)) :
    (∏ i, ((ω i ^ (-(((j i).val * (k i).val : ℕ) : ℤ)) : Rˣ) : R)) =
      multiPhase n ω (-j * k) := by
  unfold multiPhase
  apply Finset.prod_congr rfl
  intro i _
  exact kernel_minus (ω i) (hω i) (j i) (k i)

private lemma multiKernel_plus {R : Type*} [CommRing R] {d : ℕ}
    (n : Fin d → ℕ) [∀ i, NeZero (n i)] (ω : Fin d → Rˣ)
    (hω : ∀ i, ω i ^ n i = 1) (j k : (i : Fin d) → ZMod (n i)) :
    (∏ i, (((ω i)⁻¹ ^ (-(((j i).val * (k i).val : ℕ) : ℤ)) : Rˣ) : R)) =
      multiPhase n ω (j * k) := by
  unfold multiPhase
  apply Finset.prod_congr rfl
  intro i _
  exact kernel_plus (ω i) (hω i) (j i) (k i)

-- Exact type of IntMul.HvdH.eq_2_1. All auxiliary theorems above are proved.
theorem solution {R : Type*} [CommRing R] [Algebra ℂ R] {d : ℕ} (n : Fin d → ℕ)
    [∀ i, NeZero (n i)] (ω : Fin d → Rˣ) (hω : ∀ i, ω i ^ n i = 1)
    (hsum : ∀ i, ∀ j : ℤ, ¬ (n i : ℤ) ∣ j →
      ∑ k ∈ Finset.range (n i), ((ω i ^ j : Rˣ) : R) ^ k = 0)
    (u v : ((i : Fin d) → ZMod (n i)) → R) :
    let N : ℂ := ∏ i, (n i : ℂ)
    let F : (Fin d → Rˣ) → (((i : Fin d) → ZMod (n i)) → R) → ((i : Fin d) → ZMod (n i)) → R :=
      fun w x j => (1 / N) • ∑ k : (i : Fin d) → ZMod (n i),
        (∏ i, ((w i ^ (-(((j i).val * (k i).val : ℕ) : ℤ)) : Rˣ) : R)) * x k
    (1 / N) • (fun j => ∑ k : (i : Fin d) → ZMod (n i), u k * v (j - k)) =
      N • F (fun i => (ω i)⁻¹) (fun j => F ω u j * F ω v j) := by
  classical
  let N : ℂ := ∏ i, (n i : ℂ)
  let F : (Fin d → Rˣ) → (((i : Fin d) → ZMod (n i)) → R) → ((i : Fin d) → ZMod (n i)) → R :=
    fun w x j => (1 / N) • ∑ k : (i : Fin d) → ZMod (n i),
      (∏ i, ((w i ^ (-(((j i).val * (k i).val : ℕ) : ℤ)) : Rˣ) : R)) * x k
  change (1 / N) • convolution u v =
    N • F (fun i => (ω i)⁻¹) (fun j => F ω u j * F ω v j)
  let χ : ((i : Fin d) → ZMod (n i)) → R := multiPhase n ω
  have hχ : ∀ a b, χ (a + b) = χ a * χ b := multiPhase_add n ω hω
  have ho : ∀ a, (∑ k : (i : Fin d) → ZMod (n i), χ (k * a)) =
      if a = 0 then (∏ i, (n i : R)) else 0 := multiPhase_orthogonal n ω hω hsum
  let a : R := algebraMap ℂ R (1 / N)
  let b : R := algebraMap ℂ R N
  have hb : b = ∏ i, (n i : R) := by simp [b, N, map_prod]
  have hN : N ≠ 0 := by
    dsimp [N]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact_mod_cast NeZero.ne (n i)
  have hba : b * a = 1 := by
    dsimp [b, a]
    rw [← map_mul]
    simp [hN]
  have hF (x : ((i : Fin d) → ZMod (n i)) → R) :
      F ω x = fun j => a * minusTransform χ x j := by
    funext j
    simp only [F, Algebra.smul_def, multiKernel_minus n ω hω, minusTransform, a, χ]
  have hFi (x : ((i : Fin d) → ZMod (n i)) → R) :
      F (fun i => (ω i)⁻¹) x = fun j => a * plusTransform χ x j := by
    funext j
    simp only [F, Algebra.smul_def, multiKernel_plus n ω hω, plusTransform, a, χ]
  rw [hFi, hF u, hF v]
  funext j
  simp only [Pi.smul_apply, Algebra.smul_def]
  change a * convolution u v j = b * (a * plusTransform χ
    (fun k => (a * minusTransform χ u k) * (a * minusTransform χ v k)) j)
  have hp : (fun k => (a * minusTransform χ u k) * (a * minusTransform χ v k)) =
      fun k => (a * a) * minusTransform χ (convolution u v) k := by
    funext k
    rw [transform_convolution χ hχ]
    ring
  rw [hp, plusTransform_mul, transform_inversion χ hχ _ ho, ← hb]
  calc
    a * convolution u v j = (b * a) * (b * a) * a * convolution u v j := by
      rw [hba]
      ring
    _ = b * (a * (a * a * (b * convolution u v j))) := by ring
