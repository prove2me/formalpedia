-- Prove2me | solution 1 for MatrixTail.Bernstein.bennettH_ge
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:01:12.492021+00:00
-- url     : https://prove2.me/submissions/1cb7574d-c37e-4f6d-a464-cd5b4e989d14

import Mathlib
import Definitions.Def_MatrixTail_Bernstein_Model

set_option autoImplicit false

namespace MTBAux

theorem psi_nonneg (u : ℝ) (hu : 0 ≤ u) :
    3 * u * (u + 6) / (2 * (u + 3) ^ 2) ≤ Real.log (1 + u) := by
  let ψ : ℝ → ℝ := fun u => Real.log (1 + u) - 3 * u * (u + 6) / (2 * (u + 3) ^ 2)
  have hder : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt ψ (t ^ 2 * (t + 9) / ((1 + t) * (t + 3) ^ 3)) t := by
    intro t ht
    have h1 : HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + t)) t := by
      have := ((hasDerivAt_id t).const_add 1).log (by simp; positivity)
      simpa using this
    have hn : HasDerivAt (fun u : ℝ => 3 * u * (u + 6)) (3 * (t + 6) + 3 * t) t := by
      have := (((hasDerivAt_id t).const_mul 3).mul ((hasDerivAt_id t).add_const 6))
      exact this.congr_deriv (by first | (simp only [id]; ring1) | ring1 | (simp; ring1) | rfl)
    have hdn : HasDerivAt (fun u : ℝ => 2 * (u + 3) ^ 2) (2 * (2 * (t + 3))) t := by
      have := ((((hasDerivAt_id t).add_const 3).pow 2).const_mul 2)
      exact this.congr_deriv (by first | (simp only [id]; ring1) | ring1 | (simp; ring1) | rfl)
    have hq := hn.div hdn (by positivity)
    refine (h1.sub hq).congr_deriv ?_
    have h3 : (t + 3) ≠ 0 := by positivity
    have h4 : (1 + t) ≠ 0 := by positivity
    field_simp
    ring
  have hmono : MonotoneOn ψ (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro t ht; exact (hder t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hder t (le_of_lt ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hder t (le_of_lt ht)).deriv]
      have : 0 < t := ht
      positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hu) hu
  simp only [ψ] at this
  norm_num at this
  linarith

end MTBAux

theorem solution (u : ℝ) (hu : 0 ≤ u) :
    (u ^ 2 / 2) / (1 + u / 3) ≤ MatrixTail.Bernstein.bennettH u := by
  let φ : ℝ → ℝ := fun u => (1 + u) * Real.log (1 + u) - u - 3 * u ^ 2 / (2 * (u + 3))
  have hder : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt φ (Real.log (1 + t) - 3 * t * (t + 6) / (2 * (t + 3) ^ 2)) t := by
    intro t ht
    have h1 : HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + t)) t := by
      have := ((hasDerivAt_id t).const_add 1).log (by simp; positivity)
      simpa using this
    have h2 : HasDerivAt (fun u : ℝ => (1 + u) * Real.log (1 + u))
        (1 * Real.log (1 + t) + (1 + t) * (1 / (1 + t))) t := by
      have := ((hasDerivAt_id t).const_add 1).mul h1
      exact this.congr_deriv (by first | rfl | (simp only [id]; ring1) | ring1 | simp)
    have hn : HasDerivAt (fun u : ℝ => 3 * u ^ 2) (3 * (2 * t)) t := by
      have := ((hasDerivAt_pow 2 t).const_mul 3)
      exact this.congr_deriv (by first | (simp only [id]; ring1) | ring1 | (simp; ring1) | rfl)
    have hdn : HasDerivAt (fun u : ℝ => 2 * (u + 3)) 2 t := by
      have := (((hasDerivAt_id t).add_const 3).const_mul 2)
      exact this.congr_deriv (by first | (simp only [id]; ring1) | ring1 | (simp; ring1) | rfl)
    have hq := hn.div hdn (by positivity)
    refine ((h2.sub (hasDerivAt_id t)).sub hq).congr_deriv ?_
    have h3 : (t + 3) ≠ 0 := by positivity
    have h4 : (1 + t) ≠ 0 := by positivity
    field_simp
    ring
  have hmono : MonotoneOn φ (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro t ht; exact (hder t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hder t (le_of_lt ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hder t (le_of_lt ht)).deriv]
      have := MTBAux.psi_nonneg t (le_of_lt ht)
      linarith
  have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hu) hu
  simp only [φ] at h
  norm_num at h
  unfold MatrixTail.Bernstein.bennettH
  have e : (u ^ 2 / 2) / (1 + u / 3) = 3 * u ^ 2 / (2 * (u + 3)) := by
    field_simp
    ring
  rw [e]
  linarith
