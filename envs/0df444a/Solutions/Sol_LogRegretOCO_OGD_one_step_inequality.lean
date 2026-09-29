-- Prove2me | solution 1 for LogRegretOCO.OGD.one_step_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T06:03:00.281985+00:00
-- url     : https://prove2.me/submissions/b12c929f-2822-4871-abab-69761e486c6f

import Mathlib
import Definitions.Def_LogRegretOCO_OGD_Model

open LogRegretOCO.OGD

/-- A small-`t` helper: if `0 ≤ X + t*c` for all small `t > 0` and `c ≥ 0`, then `0 ≤ X`. -/
private theorem nonneg_of_small (X c : ℝ)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ X + t * c) : 0 ≤ X := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hden : (0:ℝ) < c ^ 2 + 1 := by positivity
  have ht0 : 0 < min 1 (ε / (c ^ 2 + 1)) := lt_min one_pos (by positivity)
  have ht1 : min 1 (ε / (c ^ 2 + 1)) ≤ 1 := min_le_left _ _
  have hc : c ≤ c ^ 2 + 1 := by nlinarith [sq_nonneg (c - 1)]
  have htb : min 1 (ε / (c ^ 2 + 1)) * c ≤ ε := by
    rcases le_or_gt c 0 with hc0 | hc0
    · have : min 1 (ε / (c ^ 2 + 1)) * c ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ht0.le hc0
      linarith
    · have h1 : min 1 (ε / (c ^ 2 + 1)) ≤ ε / (c ^ 2 + 1) := min_le_right _ _
      calc min 1 (ε / (c ^ 2 + 1)) * c ≤ (ε / (c ^ 2 + 1)) * c :=
            mul_le_mul_of_nonneg_right h1 hc0.le
        _ ≤ ε := by
            rw [div_mul_eq_mul_div, div_le_iff₀ hden]
            nlinarith [hε.le, hc]
  have := h _ ht0 ht1
  linarith

/-- The variational inequality characterising a Euclidean projection. -/
private theorem proj_vi {n : ℕ} (P : Set (E n)) (hPc : Convex ℝ P) (y z : E n)
    (hz : IsProj P y z) (u : E n) (hu : u ∈ P) : inner ℝ (y - z) (u - z) ≤ 0 := by
  have hstep : ∀ t : ℝ, 0 < t → t ≤ 1 →
      0 ≤ 2 * inner ℝ (z - y) (u - z) + t * ‖u - z‖ ^ 2 := by
    intro t ht0 ht1
    have hw : (1 - t) • z + t • u ∈ P := hPc hz.1 hu (by linarith) ht0.le (by ring)
    have h1 := hz.2 _ hw
    have he : (1 - t) • z + t • u - y = (z - y) + t • (u - z) := by
      rw [sub_smul, one_smul, smul_sub]; abel
    rw [he] at h1
    have h2 : ‖(z - y) + t • (u - z)‖ ^ 2
        = ‖z - y‖ ^ 2 + 2 * t * inner ℝ (z - y) (u - z) + t ^ 2 * ‖u - z‖ ^ 2 := by
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      ring
    have h3 : ‖z - y‖ ^ 2 ≤ ‖(z - y) + t • (u - z)‖ ^ 2 := by
      nlinarith [h1, norm_nonneg (z - y), norm_nonneg ((z - y) + t • (u - z))]
    rw [h2] at h3
    have hmul : t * 0 ≤ t * (2 * inner ℝ (z - y) (u - z) + t * ‖u - z‖ ^ 2) := by
      rw [mul_zero]; nlinarith [h3]
    exact le_of_mul_le_mul_left hmul ht0
  have h0 : 0 ≤ 2 * inner ℝ (z - y) (u - z) :=
    nonneg_of_small _ _ hstep
  have hneg : inner ℝ (y - z) (u - z) = -inner ℝ (z - y) (u - z) := by
    rw [show y - z = -(z - y) from by abel, inner_neg_left]
  rw [hneg]
  linarith

/-- The projection is closer to every point of `P` than the original point is. -/
private theorem proj_dist {n : ℕ} (P : Set (E n)) (hPc : Convex ℝ P) (y z : E n)
    (hz : IsProj P y z) (u : E n) (hu : u ∈ P) : ‖z - u‖ ^ 2 ≤ ‖y - u‖ ^ 2 := by
  have hvi := proj_vi P hPc y z hz u hu
  have he : y - u = (y - z) + (z - u) := by abel
  rw [he, norm_add_sq_real]
  have h2 : inner ℝ (y - z) (z - u) = -inner ℝ (y - z) (u - z) := by
    rw [show z - u = -(u - z) from by abel, inner_neg_right]
  rw [h2]
  nlinarith [sq_nonneg ‖y - z‖, norm_nonneg (y - z)]

theorem solution {n : ℕ} (P : Set (E n)) (hPc : Convex ℝ P) (x g z u : E n)
    (η G : ℝ) (hη : 0 < η) (hg : ‖g‖ ≤ G) (hz : IsProj P (x - η • g) z) (hu : u ∈ P) :
    ‖z - u‖ ^ 2 ≤ ‖x - u‖ ^ 2 + η ^ 2 * ‖g‖ ^ 2 - 2 * η * inner ℝ g (x - u) ∧
      2 * inner ℝ g (x - u) ≤ (‖x - u‖ ^ 2 - ‖z - u‖ ^ 2) / η + η * G ^ 2 := by
  have h1 := proj_dist P hPc (x - η • g) z hz u hu
  have hexp : ‖x - η • g - u‖ ^ 2
      = ‖x - u‖ ^ 2 - 2 * η * inner ℝ g (x - u) + η ^ 2 * ‖g‖ ^ 2 := by
    have he : x - η • g - u = (x - u) - η • g := by abel
    rw [he, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hη, real_inner_comm (x - u) g]
    ring
  rw [hexp] at h1
  refine ⟨by linarith, ?_⟩
  have hG : ‖g‖ ^ 2 ≤ G ^ 2 := by nlinarith [norm_nonneg g, hg]
  have hdiv : (‖x - u‖ ^ 2 - ‖z - u‖ ^ 2) / η + η * G ^ 2
      = ((‖x - u‖ ^ 2 - ‖z - u‖ ^ 2) + η ^ 2 * G ^ 2) / η := by
    field_simp
  rw [hdiv, le_div_iff₀ hη]
  nlinarith [h1, hG, hη]
