-- Prove2me | solution 1 for MasulloRH.quartic_two_window_centered_arithmetic_discriminator
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T08:52:45.06976+00:00
-- url     : https://prove2.me/submissions/3b97c9d9-4a32-4d50-9293-40bb582fd48d

import Mathlib
open ArithmeticFunction Complex
open scoped BigOperators
theorem solution :
    (∃ χ : DirichletCharacter ℂ 5, χ 2 = I) ∧
    ∃ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      (∀ x ≤ (1:ℝ), f x = 0) ∧ f 2 = 1 ∧ f 8 = 1 ∧
      (∀ n : ℕ, n ≠ 2 → n ≠ 8 → f n = 0) ∧
      ∀ (χ : DirichletCharacter ℂ 5), χ 2 = I →
        ∀ (S : Finset ℕ), 2 ∈ S → 8 ∈ S →
        let a : ℕ → ℂ := fun n => (vonMangoldt n * f n : ℝ) * (χ n - star (χ n))
        (∑ n ∈ S, a n) = 0 ∧
        (∑ n ∈ S, a n / Real.sqrt n) = I * Real.log 2 / Real.sqrt 2 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  constructor
  · let q : ZMod 5 → ℂ := fun a => ![0,1,I,-I,-1] a
    let χ : DirichletCharacter ℂ 5 := {
      toFun := q
      map_one' := by rfl
      map_mul' := by
        intro a b
        fin_cases a <;> fin_cases b <;>
          apply Complex.ext <;> norm_num [q, Complex.mul_re, Complex.mul_im] <;>
            first | rfl | exact (show (-I).re = 0 by simp) | exact (show (-1 : ℂ).im = 0 by simp)
      map_nonunit' := by
        intro a ha
        have hz : a = 0 := by simpa [isUnit_iff_ne_zero] using ha
        subst a
        rfl }
    exact ⟨χ, rfl⟩
  let B (j : ℕ) : ContDiffBump (j:ℝ) := ⟨1/8,1/4,by norm_num,by norm_num⟩
  let f (x : ℝ) := B 2 x + B 8 x
  have atc (j : ℕ) : B j j = 1 := (B j).one_of_mem_closedBall (by simp [Metric.mem_closedBall,B])
  have away (j k : ℕ) (hne : j ≠ k) : B j k = 0 := by
    apply (B j).zero_of_le_dist
    change (1/4:ℝ) ≤ dist (k:ℝ) (j:ℝ)
    rw [Real.dist_eq]
    rcases lt_or_gt_of_ne hne with h|h
    · have hh : (j:ℝ)+1 ≤ k := by exact_mod_cast (show j+1 ≤ k by omega)
      exact le_trans (by linarith) (le_abs_self ((k:ℝ)-j))
    · have hh : (k:ℝ)+1 ≤ j := by exact_mod_cast (show k+1 ≤ j by omega)
      exact le_trans (by linarith) (neg_le_abs ((k:ℝ)-j))
  have f2 : f 2 = 1 := by simpa [f] using congrArg₂ (·+·) (atc 2) (away 8 2 (by decide))
  have f8 : f 8 = 1 := by simpa [f] using congrArg₂ (·+·) (away 2 8 (by decide)) (atc 8)
  have f0 (n : ℕ) (h2 : n ≠ 2) (h8 : n ≠ 8) : f n = 0 := by
    simp [f,away 2 n h2.symm,away 8 n h8.symm]
  refine ⟨f,(B 2).contDiff.add (B 8).contDiff,(B 2).hasCompactSupport.add (B 8).hasCompactSupport,?_,f2,f8,f0,?_⟩
  · intro x hx
    have hz (j : ℕ) (hj : 2 ≤ j) : B j x = 0 := by
      apply (B j).zero_of_le_dist
      change 1/4 ≤ dist x (j:ℝ)
      rw [Real.dist_eq]
      have hjr : (2:ℝ) ≤ j := by exact_mod_cast hj
      exact le_trans (by linarith) (neg_le_abs (x-(j:ℝ)))
    simp [f,hz 2 (by decide),hz 8 (by decide)]
  intro χ hχ S hs2 hs8
  let a : ℕ → ℂ := fun n => (vonMangoldt n * f n : ℝ) * (χ n - star (χ n))
  change (∑ n ∈ S, a n) = 0 ∧ (∑ n ∈ S, a n / Real.sqrt n) = _
  have c8 : χ (8 : ZMod 5) = -I := by
    rw [show (8 : ZMod 5) = 2^3 by decide, map_pow, hχ, pow_succ, Complex.I_sq]
    ring
  have L2 : vonMangoldt 2 = Real.log 2 := by simpa using vonMangoldt_apply_prime Nat.prime_two
  have L8 : vonMangoldt 8 = Real.log 2 := by
    rw [show (8:ℕ) = 2^3 by decide,vonMangoldt_apply_pow (by norm_num : (3:ℕ) ≠ 0),L2]
  have a2 : a 2 = (Real.log 2 : ℂ) * (2*I) := by simp [a,L2,f2,hχ,Complex.conj_I] <;> ring <;> simp
  have a8 : a 8 = -(Real.log 2 : ℂ) * (2*I) := by simp [a,L8,f8,c8,Complex.conj_I] <;> ring <;> simp
  have sm (g : ℕ → ℂ) (hg : ∀ n, n ≠ 2 → n ≠ 8 → g n = 0) : ∑ n ∈ S, g n = g 2 + g 8 := by
    have hsub : ({2,8} : Finset ℕ) ⊆ S := by
      intro n hn
      simp only [Finset.mem_insert,Finset.mem_singleton] at hn
      rcases hn with rfl | rfl <;> assumption
    rw [← Finset.sum_subset hsub (by
      intro i hi h
      simp only [Finset.mem_insert,Finset.mem_singleton] at h
      exact hg i (fun he => h (Or.inl he)) (fun he => h (Or.inr he)))]
    norm_num
  have az (n : ℕ) (h2 : n ≠ 2) (h8 : n ≠ 8) : a n = 0 := by simp [a, f0 n h2 h8]
  have hr : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8:ℝ) = 4*2 by norm_num,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
    norm_num
  constructor
  · rw [sm _ az,a2,a8]; ring
  · rw [sm _ (by intro n h2 h8; simp [az n h2 h8])]
    simp only [Nat.cast_ofNat, a2,a8,hr,Complex.ofReal_mul,Complex.ofReal_ofNat]
    have hn : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show Real.sqrt 2 ≠ 0 by positivity)
    field_simp
    <;> ring
