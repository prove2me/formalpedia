-- Prove2me | solution 1 for McFadden1974.Asymptotics.prob_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T14:23:16.004023+00:00
-- url     : https://prove2.me/submissions/0a9a2bfb-2375-42ef-a213-69bb0c332940

import Mathlib
import Definitions.Def_McFadden1974_Asymptotics_LogitSample

open MeasureTheory ProbabilityTheory Filter Topology McFadden1974.Asymptotics in
theorem solution {K : ℕ} (D : SerialData K) (Jstar : ℕ) (M : ℝ)
    (hB : IsBounded D Jstar M) (m : ℕ) (i : Fin (D.J m)) (θ : EuclideanSpace ℝ (Fin K)) :
    1 / ((Jstar : ℝ) * Real.exp (2 * M * ‖θ‖)) ≤ prob D m i θ := by
  have hb : ∀ j : Fin (D.J m), |inner ℝ (D.z m j) θ| ≤ M * ‖θ‖ := fun j =>
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hB.norm_z_le m j) (norm_nonneg _))
  have hJ : (1:ℝ) ≤ (D.J m : ℝ) := by exact_mod_cast D.one_le_J m
  have hJs : (D.J m : ℝ) ≤ Jstar := by exact_mod_cast hB.J_le m
  have hS : ∑ j : Fin (D.J m), Real.exp (inner ℝ (D.z m j) θ)
      ≤ (Jstar : ℝ) * Real.exp (M * ‖θ‖) := by
    calc _ ≤ ∑ _j : Fin (D.J m), Real.exp (M * ‖θ‖) :=
          Finset.sum_le_sum fun j _ => Real.exp_le_exp.2 (le_of_abs_le (hb j))
      _ = (D.J m : ℝ) * Real.exp (M * ‖θ‖) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hJs (Real.exp_pos _).le
  have hSpos : 0 < ∑ j : Fin (D.J m), Real.exp (inner ℝ (D.z m j) θ) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) ⟨i, Finset.mem_univ _⟩
  have hnum : Real.exp (-(M * ‖θ‖)) ≤ Real.exp (inner ℝ (D.z m i) θ) :=
    Real.exp_le_exp.2 (neg_le_of_abs_le (hb i))
  have hJpos : (0:ℝ) < Jstar := by linarith
  have h1 : Real.exp (-(M * ‖θ‖)) * Real.exp (M * ‖θ‖) = 1 := by
    rw [← Real.exp_add]; simp
  have h2 : Real.exp (2 * M * ‖θ‖) = Real.exp (M * ‖θ‖) * Real.exp (M * ‖θ‖) := by
    rw [← Real.exp_add]; ring_nf
  have he : 0 < Real.exp (M * ‖θ‖) := Real.exp_pos _
  have hea : 1 ≤ Real.exp (inner ℝ (D.z m i) θ) * Real.exp (M * ‖θ‖) := by
    rw [← h1]; exact mul_le_mul_of_nonneg_right hnum he.le
  unfold prob
  rw [h2, div_le_div_iff₀ (by positivity) hSpos]
  have hJe : 0 < (Jstar : ℝ) * Real.exp (M * ‖θ‖) := by positivity
  calc 1 * ∑ j : Fin (D.J m), Real.exp (inner ℝ (D.z m j) θ)
      ≤ (Jstar : ℝ) * Real.exp (M * ‖θ‖) * 1 := by rw [one_mul, mul_one]; exact hS
    _ ≤ (Jstar : ℝ) * Real.exp (M * ‖θ‖) *
        (Real.exp (inner ℝ (D.z m i) θ) * Real.exp (M * ‖θ‖)) :=
          mul_le_mul_of_nonneg_left hea hJe.le
    _ = _ := by ring
