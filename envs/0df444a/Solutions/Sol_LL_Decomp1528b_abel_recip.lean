-- Prove2me | solution 1 for LL_Decomp1528b.abel_recip
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:10.161943+00:00
-- url     : https://prove2.me/submissions/8cd37e74-42e9-47f3-8c52-283186afa913

import Mathlib

open Real Finset Filter Topology

theorem ChMeAux.hasDerivAt_inv_log {t : ℝ} (ht : 2 ≤ t) :
    HasDerivAt (fun t : ℝ => (Real.log t)⁻¹) (-(t⁻¹) / Real.log t ^ 2) t := by
  have ht0 : t ≠ 0 := by positivity
  have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
  exact (Real.hasDerivAt_log ht0).inv hl

theorem solution {x y : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    ∑ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p =
      (∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p) / log x -
        (∑ p ∈ Nat.primesLE ⌊y⌋₊, log p / p) / log y +
        ∫ t in y..x, (∑ p ∈ Nat.primesLE ⌊t⌋₊, log p / p) / (t * log t ^ 2) := by
  set c : ℕ → ℝ := fun k => if k.Prime then Real.log k / k else 0 with hc
  set f : ℝ → ℝ := fun t => (Real.log t)⁻¹ with hf
  have hA : ∀ n : ℕ, ∑ k ∈ Icc 0 n, c k = ∑ p ∈ Nat.primesLE n, Real.log p / p := by
    intro n
    rw [hc]
    simp only
    rw [← sum_filter]
    congr 1
    ext q
    simp only [mem_filter, mem_Icc, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h2, h3⟩
    · rintro ⟨h2, h3⟩; exact ⟨⟨Nat.zero_le _, h2⟩, h3⟩
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hdiff : ∀ t ∈ Set.Icc y x, DifferentiableAt ℝ f t := fun t ht =>
    (ChMeAux.hasDerivAt_inv_log (by linarith [ht.1])).differentiableAt
  have hderiv : ∀ t ∈ Set.Icc y x, deriv f t = -(t⁻¹) / Real.log t ^ 2 := fun t ht =>
    (ChMeAux.hasDerivAt_inv_log (by linarith [ht.1])).deriv
  have hint : MeasureTheory.IntegrableOn (deriv f) (Set.Icc y x) := by
    have hcont : ContinuousOn (fun t : ℝ => -(t⁻¹) / Real.log t ^ 2) (Set.Icc y x) := by
      intro t ht
      have ht2 : 2 ≤ t := by linarith [ht.1]
      have ht0 : t ≠ 0 := by positivity
      have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
      have : ContinuousAt (fun t : ℝ => -(t⁻¹) / Real.log t ^ 2) t := by
        apply ContinuousAt.div
        · exact (continuousAt_inv₀ ht0).neg
        · exact (Real.continuousAt_log ht0).pow 2
        · exact pow_ne_zero 2 hl
      exact this.continuousWithinAt
    exact (hcont.congr fun t ht => hderiv t ht).integrableOn_Icc
  have key := sum_mul_eq_sub_sub_integral_mul c hy0 hyx hdiff hint
  have hL : ∑ k ∈ Ioc ⌊y⌋₊ ⌊x⌋₊, f k * c k =
      ∑ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p := by
    rw [sum_filter]
    refine sum_congr rfl fun k hk => ?_
    simp only [hc, hf]
    split_ifs with hkp
    · have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hkp.two_le
      have hl : Real.log k ≠ 0 := (Real.log_pos (by linarith)).ne'
      have : (k : ℝ) ≠ 0 := by positivity
      field_simp
    · simp
  rw [hL] at key
  simp only [hA] at key
  rw [key, intervalIntegral.integral_of_le hyx]
  have hI : ∫ t in Set.Ioc y x, deriv f t * ∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log p / p =
      -∫ t in Set.Ioc y x, (∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log p / p) / (t * Real.log t ^ 2) := by
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have ht2 : 2 ≤ t := by linarith [ht.1]
    have := hderiv t ⟨ht.1.le, ht.2⟩
    rw [this]
    have ht0 : t ≠ 0 := by positivity
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
    field_simp
  simp only [hf]
  rw [hI]
  simp only [div_eq_mul_inv]
  ring
