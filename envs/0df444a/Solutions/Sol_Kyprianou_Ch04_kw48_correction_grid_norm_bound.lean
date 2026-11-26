-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_correction_grid_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:34:20.079974+00:00
-- url     : https://prove2.me/submissions/0362ec6a-b112-41c9-b401-0abf076a4959

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_cell_correction_norm_bound
import Theorems.Thm_Kyprianou_Ch04_kw48_log_weight_grid_variation
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A deterministic real-part cap and the log-weight's grid variation
bound the total complex correction uniformly on a finite horizon. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (T : NNReal) (u : Nat → NNReal) (N : Nat)
    (hu : Monotone u) (hT : ∀ i, u i ≤ T) (w : Ω) :
    ‖C L Psi alpha beta u N w‖ ≤
      2*Real.exp (‖Psi alpha‖*(T:Real))*
        (|beta-alpha| * runningSup L T w+‖Psi alpha‖*(T:Real)) := by
  let K := ‖Psi alpha‖*(T:Real)
  let V := |beta-alpha| * runningSup L T w+K
  have hUm := (runningSup_monotone_and_path_le L w).1
  have hU0 : 0 ≤ runningSup L 0 w := by
    simpa only [L.X_zero] using (runningSup_monotone_and_path_le L w).2 0
  have hUs := hU0.trans (hUm (show 0 ≤ u 0 from zero_le))
  have hUt := hUm (hT N)
  have htN : (u N:Real) ≤ (T:Real) := by exact_mod_cast hT N
  have hVar : (∑ i ∈ Finset.range N,
      ‖G L Psi alpha beta (u (i+1)) w-G L Psi alpha beta (u i) w‖) ≤ V := by
    refine (Kyprianou.Ch04.kw48_log_weight_grid_variation L Psi alpha beta w u N hu).trans ?_
    unfold V K
    exact add_le_add
      (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (by linarith [NNReal.coe_nonneg (u 0)])
        (norm_nonneg _))
  unfold C
  calc
    _ ≤ ∑ i ∈ Finset.range N,
        ‖E L Psi alpha (u (i+1)) w*
          (H L Psi alpha beta (u (i+1)) w-H L Psi alpha beta (u i) w)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range N,
        2*Real.exp K*‖G L Psi alpha beta (u (i+1)) w-
          G L Psi alpha beta (u i) w‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact Kyprianou.Ch04.kw48_cell_correction_norm_bound L Psi alpha beta
        (u i) (u (i+1)) T (hu (Nat.le_succ i)) (hT (i+1)) w
    _ = 2*Real.exp K*(∑ i ∈ Finset.range N,
        ‖G L Psi alpha beta (u (i+1)) w-G L Psi alpha beta (u i) w‖) := by
      rw [Finset.mul_sum]
    _ ≤ 2*Real.exp K*V :=
      mul_le_mul_of_nonneg_left hVar (by positivity)
