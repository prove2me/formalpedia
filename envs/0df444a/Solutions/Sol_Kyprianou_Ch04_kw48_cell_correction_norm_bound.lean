-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_cell_correction_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:55:05.621056+00:00
-- url     : https://prove2.me/submissions/abee377e-5eec-4881-8d8a-84b833cfff39

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_grid_correction_cell
import Theorems.Thm_Kyprianou_Ch04_kw48_exp_increment_norm_bound
import Theorems.Thm_Kyprianou_Ch04_kw48_norm_Z
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The complex product correction is controlled by the log increment
and a deterministic real-part bound on the time horizon. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (a b T : NNReal) (hab : a ≤ b) (hbT : b ≤ T)
    (w : Ω) :
    ‖E L Psi alpha b w*(H L Psi alpha beta b w-H L Psi alpha beta a w)‖ ≤
      2*Real.exp (‖Psi alpha‖*(T:Real))*
        ‖G L Psi alpha beta b w-G L Psi alpha beta a w‖ := by
  have hRe : (-(G L Psi alpha beta b w-G L Psi alpha beta a w)).re =
      ((b:Real)-(a:Real))*(Psi alpha).re := by
    unfold G
    simp [Complex.mul_re,Complex.mul_im]
    ring
  have hdt : 0 ≤ (b:Real)-(a:Real) := sub_nonneg.mpr (by exact_mod_cast hab)
  have hPsi : (Psi alpha).re ≤ ‖Psi alpha‖ :=
    (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hCap : (-(G L Psi alpha beta b w-G L Psi alpha beta a w)).re ≤
      ‖Psi alpha‖*(T:Real) := by
    rw [hRe]
    calc
      _ ≤ ((b:Real)-(a:Real))*‖Psi alpha‖ :=
        mul_le_mul_of_nonneg_left hPsi hdt
      _ ≤ ‖Psi alpha‖*(T:Real) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left
          (by linarith [show (b:Real) ≤ T by exact_mod_cast hbT,NNReal.coe_nonneg a])
          (norm_nonneg _)
  rw [Kyprianou.Ch04.kw48_grid_correction_cell L Psi alpha beta a b w,
    norm_mul,Kyprianou.Ch04.kw48_norm_Z,one_mul]
  exact Kyprianou.Ch04.kw48_exp_increment_norm_bound _ _
    (mul_nonneg (norm_nonneg _) (NNReal.coe_nonneg T)) hCap
