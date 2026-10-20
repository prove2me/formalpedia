-- Prove2me | solution 1 for OAI.Cotype.cubeNoise_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:40:49.490388+00:00
-- url     : https://prove2.me/submissions/0b01041d-8485-4169-8936-b8f7e60a13d5

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise

open OAI OAI.Cotype
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
theorem t_noise {n : ℕ} (f : Cube n → X) (u : Cube n) :
    ‖cubeNoise f u‖ ≤ cubeNoise (fun v => ‖f v‖) u := by
  induction n with
  | zero => simp [cubeNoise]
  | succ n ih =>
    rw [← Fin.cons_self_tail u]
    cases u 0
    · rw [cubeNoise_cons_false, cubeNoise_cons_false]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by norm_num),
        abs_of_pos (by norm_num)]
      have h1 := ih (fun v => f (Fin.cons false v)) (Fin.tail u)
      have h2 := ih (fun v => f (Fin.cons true v)) (Fin.tail u)
      simp only [smul_eq_mul]
      linarith
    · rw [cubeNoise_cons_true, cubeNoise_cons_true]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by norm_num),
        abs_of_pos (by norm_num)]
      have h1 := ih (fun v => f (Fin.cons false v)) (Fin.tail u)
      have h2 := ih (fun v => f (Fin.cons true v)) (Fin.tail u)
      simp only [smul_eq_mul]
      linarith

theorem solution {n : ℕ} (f : Cube n → X) (u : Cube n) :
    ‖cubeNoise f u‖ ≤ cubeNoise (fun v => ‖f v‖) u := by
  exact t_noise f u

