-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_M_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:55:39.60223+00:00
-- url     : https://prove2.me/submissions/a01c6aaa-cd0f-46db-8b40-a92be8b4d56f

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_J_bound
import Theorems.Thm_Kyprianou_Ch04_kw48_S_adapted_bound
import Theorems.Thm_Kyprianou_Ch04_kw48_norm_Z
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The target complex martingale has a linear integrable envelope. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (t : NNReal) (w : Ω) :
    ‖M L Psi alpha beta t w‖ ≤
      ‖Psi alpha‖*(t:Real)+2+|alpha-beta| * runningSup L t w := by
  have hJ := Kyprianou.Ch04.kw48_J_bound L alpha beta t w
  have hS := (Kyprianou.Ch04.kw48_S_adapted_bound L beta).2 t w
  have hZ := Kyprianou.Ch04.kw48_norm_Z L alpha beta t w
  let A := -Psi alpha*J L alpha beta t w
  let B := Complex.I*((alpha-beta:Real):Complex)*S L beta t w
  change ‖A+1-Z L alpha beta t w-B‖ ≤ _
  calc
    _ ≤ ‖A+1-Z L alpha beta t w‖+‖B‖ := norm_sub_le _ _
    _ ≤ ‖A+1‖+‖Z L alpha beta t w‖+‖B‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ ‖A‖+‖(1:Complex)‖+‖Z L alpha beta t w‖+‖B‖ :=
      add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ ≤ _ := by
      dsimp only [A,B]
      rw [norm_mul,norm_neg,norm_one,hZ,norm_mul,norm_mul,
        Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
      have h1 := mul_le_mul_of_nonneg_left hJ (norm_nonneg (Psi alpha))
      have h2 := mul_le_mul_of_nonneg_left hS (abs_nonneg (alpha-beta))
      linarith
