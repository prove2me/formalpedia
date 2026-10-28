-- Prove2me | solution 1 for GeomDL.Filters.polynomial_filter_localised
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T06:05:36.807764+00:00
-- url     : https://prove2.me/submissions/d0e68c34-7c6b-4d9d-8d41-f0b5263f83e4

import Mathlib
import Definitions.Def_GeomDL_Filters_Defs

open GeomDL.Filters Matrix

theorem pf_lap_ne {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : ∀ u v, u ≠ v → W u v ≠ 0 → G.Adj u v)
    {u w : Fin n} (h : lap W u w ≠ 0) (huw : u ≠ w) : G.Adj u w := by
  apply hW u w huw
  intro h0
  apply h
  simp [lap, SpectralSparsify.Sampling.lapMat, SpectralSparsify.Sampling.degMat,
    SpectralSparsify.Sampling.adjMat, Matrix.diagonal_apply_ne _ huw]
  exact h0

theorem pf_hops {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : ∀ u v, u ≠ v → W u v ≠ 0 → G.Adj u v) :
    ∀ k : ℕ, ∀ u v : Fin n, (lap W ^ k) u v ≠ 0 → ∃ p : G.Walk u v, p.length ≤ k := by
  intro k
  induction k with
  | zero =>
    intro u v h
    rw [pow_zero] at h
    by_cases huv : u = v
    · subst huv; exact ⟨SimpleGraph.Walk.nil, le_refl _⟩
    · exact absurd (Matrix.one_apply_ne huv) h
  | succ k ih =>
    intro u v h
    rw [pow_succ', Matrix.mul_apply] at h
    obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 : lap W u w ≠ 0 := left_ne_zero_of_mul hw
    have h2 : (lap W ^ k) w v ≠ 0 := right_ne_zero_of_mul hw
    obtain ⟨p, hp⟩ := ih w v h2
    by_cases huw : u = w
    · subst huw; exact ⟨p, by omega⟩
    · exact ⟨SimpleGraph.Walk.cons (pf_lap_ne G W hW h1 huw) p, by simp; omega⟩

theorem solution {n d : ℕ} (G : SimpleGraph (Fin n))
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : ∀ u v, u ≠ v → W u v ≠ 0 → G.Adj u v)
    (r : ℕ) (α : Fin (r + 1) → ℝ) (X X' : Matrix (Fin n) (Fin d) ℝ) (u : Fin n)
    (hX : ∀ v, WithinHops G r u v → X v = X' v) :
    (polyFilter W r α * X) u = (polyFilter W r α * X') u := by
  funext j
  simp only [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hP : polyFilter W r α u v = 0
  · rw [hP, zero_mul, zero_mul]
  · have : ∃ k : Fin (r + 1), (lap W ^ (k : ℕ)) u v ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hP
      simp [polyFilter, Matrix.sum_apply, hc]
    obtain ⟨k, hk⟩ := this
    obtain ⟨p, hp⟩ := pf_hops G W hW k u v hk
    rw [hX v ⟨p, by omega⟩]
