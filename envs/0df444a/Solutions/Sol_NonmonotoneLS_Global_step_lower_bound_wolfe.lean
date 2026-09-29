-- Prove2me | solution 1 for NonmonotoneLS.Global.step_lower_bound_wolfe
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:31:59.649706+00:00
-- url     : https://prove2.me/submissions/35bedba6-8e31-4e93-83b2-d67ea840f09c

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_Global_Run
import Definitions.Def_NonmonotoneLS_Global_Regions

open scoped InnerProductSpace NNReal Topology
open Filter

namespace NonmonotoneLS.Global

theorem aux_slbw_key {n : ℕ} (p : Shared.Params) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : EuclideanSpace ℝ (Fin n)) (C α L : ℝ)
    (hdesc : ⟪gradient f x, d⟫_ℝ ≤ 0)
    (hstep : Shared.IsWolfeStep p f x d C α)
    (hLip : ‖gradient f (x + α • d) - gradient f x‖ ≤ L * ‖(x + α • d) - x‖) :
    (1 - p.σ) * |⟪gradient f x, d⟫_ℝ| ≤ L * α * ‖d‖ ^ 2 := by
  obtain ⟨hα, -, hcurv⟩ := hstep
  have habs : |⟪gradient f x, d⟫_ℝ| = -⟪gradient f x, d⟫_ℝ := abs_of_nonpos hdesc
  have h1 : (1 - p.σ) * |⟪gradient f x, d⟫_ℝ| ≤
      ⟪gradient f (x + α • d) - gradient f x, d⟫_ℝ := by
    rw [habs, inner_sub_left]; linarith
  have h2 : ⟪gradient f (x + α • d) - gradient f x, d⟫_ℝ ≤
      ‖gradient f (x + α • d) - gradient f x‖ * ‖d‖ := real_inner_le_norm _ _
  have h3 : ‖(x + α • d) - x‖ = α * ‖d‖ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hα]
  have h4 : ‖gradient f (x + α • d) - gradient f x‖ * ‖d‖ ≤ L * (α * ‖d‖) * ‖d‖ := by
    rw [← h3]
    exact mul_le_mul_of_nonneg_right hLip (norm_nonneg _)
  nlinarith

end NonmonotoneLS.Global

open NonmonotoneLS NonmonotoneLS.Global

theorem solution {n : ℕ} (p : Shared.Params) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x d : EuclideanSpace ℝ (Fin n)) (C α L : ℝ) (hL : 0 < L)
    (hdesc : ⟪gradient f x, d⟫_ℝ ≤ 0)
    (hstep : Shared.IsWolfeStep p f x d C α)
    (hLip : ‖gradient f (x + α • d) - gradient f x‖ ≤ L * ‖(x + α • d) - x‖) :
    (1 - p.σ) / L * (|⟪gradient f x, d⟫_ℝ| / ‖d‖ ^ 2) ≤ α := by
  have hα : 0 < α := hstep.1
  have key := aux_slbw_key p f x d C α L hdesc hstep hLip
  rcases eq_or_ne d 0 with hd | hd
  · subst hd
    simp only [norm_zero]
    norm_num
    exact hα.le
  · have hdn : 0 < ‖d‖ ^ 2 := by positivity
    rw [div_mul_div_comm, div_le_iff₀ (mul_pos hL hdn)]
    linarith
