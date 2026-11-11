-- Prove2me | solution 1 for HermiteLaptop.MaxAgree.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T21:29:16.674986+00:00
-- url     : https://prove2.me/submissions/6ad25067-2b44-452f-86f2-d547c06d4f2d

import Mathlib

/-- Lemma 4.3 (Bernstein certificate): if `q` has degree at most `d` and
`q(ρ) = Σ_{i=0}^{d} β_i binom(d,i) ((ρ−u)/(v−u))ⁱ ((v−ρ)/(v−u))^{d−i}` with all `β_i ≥ 0`, then
`q ≥ 0` on `[u, v]`. -/
theorem solution (q : Polynomial ℝ) (d : ℕ) (hdeg : q.natDegree ≤ d) (u v : ℝ) (huv : u < v)
    (β : ℕ → ℝ)
    (hrep : ∀ ρ : ℝ, q.eval ρ = ∑ i ∈ Finset.range (d + 1),
      β i * (d.choose i : ℝ) * ((ρ - u) / (v - u)) ^ i * ((v - ρ) / (v - u)) ^ (d - i))
    (hβ : ∀ i ≤ d, 0 ≤ β i) :
    ∀ ρ ∈ Set.Icc u v, 0 ≤ q.eval ρ := by
  intro ρ hρ
  rw [hrep]
  have hvu : 0 < v - u := by linarith
  apply Finset.sum_nonneg
  intro i hi
  have hid : i ≤ d := by have := Finset.mem_range.mp hi; omega
  have h1 : 0 ≤ (ρ - u) / (v - u) := div_nonneg (by linarith [hρ.1]) hvu.le
  have h2 : 0 ≤ (v - ρ) / (v - u) := div_nonneg (by linarith [hρ.2]) hvu.le
  have := hβ i hid
  positivity
