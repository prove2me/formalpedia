-- Prove2me | solution 1 for Hintz2026.invPos_yPos
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T15:53:26.746044+00:00
-- url     : https://prove2.me/submissions/3a6cfc8f-72f3-4c29-96d9-18b76612179d

import Definitions.Def_Hintz2026_Chiral

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (F : PosFields) {z : Fin 2 -> ℝ} (hz : z ∈ U p) : (invPos p (yPos p 1 F) (yPos p (-1) F)).psi2 z = F.psi2 z ∧ (invPos p (yPos p 1 F) (yPos p (-1) F)).psi1 z = F.psi1 z ∧ (invPos p (yPos p 1 F) (yPos p (-1) F)).k z = F.k z ∧ (invPos p (yPos p 1 F) (yPos p (-1) F)).s z = F.s z :=
  by
    have hpre : (↑(prePos p z) : ℂ) ≠ 0 := by exact_mod_cast (prePos_pos p hz).ne'
    have hsD : (↑(Real.sqrt (Del p (z 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (Del_pos p hz.1)).ne'
    have hQ : (↑p.Q : ℂ) ≠ 0 := by exact_mod_cast p.hQ
    simp only [invPos, yPos, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> push_cast <;> ring

end
