-- Prove2me | solution 1 for IntMul.GaussianNormalization.normalized_fourth_root
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T17:26:06.079721+00:00
-- url     : https://prove2.me/submissions/78799174-2721-495b-ba8e-d93d2485a550

import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Tactic

/-!
An arithmetic proof of the fourth-root scalar in the binary residual normal form.
The argument uses the Gaussian-integer norm, avoiding any orthonormal-basis
assumption on an alternating residual.
-/

namespace IntMul.GaussianNormalization

local notation "ℤ[i]" => GaussianInt

/-- A Gaussian integer of even norm is divisible by `1+i`. -/
theorem factor_one_add_i_of_even_norm (z : ℤ[i]) (hn : Even z.norm) :
    ∃ w : ℤ[i], z = (⟨1, 1⟩ : ℤ[i]) * w := by
  have he : Even (z.re ^ 2 + z.im ^ 2) := by
    simpa [Zsqrtd.norm, pow_two] using hn
  have hp : Even z.re ↔ Even z.im := by
    simpa [Int.even_pow] using Int.even_add.mp he
  obtain ⟨a, ha⟩ := Int.even_add.mpr hp
  obtain ⟨b, hb⟩ := Int.even_sub.mpr hp.symm
  refine ⟨⟨a, b⟩, ?_⟩
  apply Zsqrtd.ext
  · change z.re = 1 * a + (-1) * 1 * b
    omega
  · change z.im = 1 * b + 1 * a
    omega

/-- If a Gaussian integer has norm `2^r`, all of its ramified-prime factors
can be removed, leaving an element of norm one. -/
theorem norm_two_pow_factorization (r : ℕ) (z : ℤ[i]) (hz : z.norm = (2 : ℤ) ^ r) :
    ∃ u : ℤ[i], u.norm = 1 ∧ z = (⟨1, 1⟩ : ℤ[i]) ^ r * u := by
  induction r generalizing z with
  | zero =>
      exact ⟨z, by simpa using hz, by simp⟩
  | succ r ih =>
      have he : Even z.norm := by
        rw [hz, pow_succ]
        exact Even.mul_left (by decide : Even (2 : ℤ)) _
      obtain ⟨w, hw⟩ := factor_one_add_i_of_even_norm z he
      have hπ : Zsqrtd.norm (⟨1, 1⟩ : ℤ[i]) = 2 := by norm_num [Zsqrtd.norm]
      have hwn : w.norm = (2 : ℤ) ^ r := by
        rw [hw, Zsqrtd.norm_mul, hπ, pow_succ] at hz
        nlinarith
      obtain ⟨u, hu, hwu⟩ := ih w hwn
      refine ⟨u, hu, ?_⟩
      rw [hw, hwu, pow_succ]
      ring

/-- The only Gaussian integers of norm one are the four roots of unity. -/
theorem norm_one_fourth_root (z : ℤ[i]) (hz : z.norm = 1) :
    (z : ℂ) ^ 4 = 1 := by
  have hn : z.re ^ 2 + z.im ^ 2 = 1 := by simpa [Zsqrtd.norm, pow_two] using hz
  have hr : -1 ≤ z.re ∧ z.re ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg z.im]
  have hi : -1 ≤ z.im ∧ z.im ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg z.re]
  rcases z with ⟨a, b⟩
  dsimp at hn hr hi
  rcases hr with ⟨ha₁, ha₂⟩
  rcases hi with ⟨hb₁, hb₂⟩
  interval_cases a <;> interval_cases b <;>
    norm_num [GaussianInt.toComplex_def', Complex.I_sq, pow_succ] at *

/-- Normalizing a norm-`2^r` Gaussian integer by `((1-i)/2)^r` gives a fourth root
of unity.  Applied to the quadratic Gauss sum, this proves the scalar assertion
for both alternating and nonalternating residuals. -/
theorem normalized_fourth_root (r : ℕ) (z : ℤ[i]) (hz : z.norm = (2 : ℤ) ^ r) :
    ((z : ℂ) * ((1 - Complex.I) / 2) ^ r) ^ 4 = 1 := by
  obtain ⟨u, hu, hzu⟩ := norm_two_pow_factorization r z hz
  have hπ : ((⟨1, 1⟩ : ℤ[i]) : ℂ) * ((1 - Complex.I) / 2) = 1 := by
    rw [GaussianInt.toComplex_def']
    norm_num
    ring_nf
    simp [Complex.I_sq]
    norm_num
  have hnorm : (z : ℂ) * ((1 - Complex.I) / 2) ^ r = (u : ℂ) := by
    rw [hzu]
    simp only [GaussianInt.toComplex_mul, map_pow]
    calc
      _ = (((⟨1, 1⟩ : ℤ[i]) : ℂ) * ((1 - Complex.I) / 2)) ^ r * (u : ℂ) := by
        rw [mul_pow]
        ring
      _ = (u : ℂ) := by rw [hπ]; simp
  rw [hnorm]
  exact norm_one_fourth_root u hu

end IntMul.GaussianNormalization

#print axioms IntMul.GaussianNormalization.factor_one_add_i_of_even_norm
#print axioms IntMul.GaussianNormalization.norm_two_pow_factorization
#print axioms IntMul.GaussianNormalization.norm_one_fourth_root
#print axioms IntMul.GaussianNormalization.normalized_fourth_root

/-- Submission entry point, with exactly the public target's binders and type. -/
theorem solution (r : ℕ) (z : GaussianInt) (hz : z.norm = (2 : ℤ) ^ r) :
    ((z : ℂ) * ((1 - Complex.I) / 2) ^ r) ^ 4 = 1 := by
  exact IntMul.GaussianNormalization.normalized_fourth_root r z hz

#print axioms solution
