-- Prove2me | solution 1 for Hintz2026.yPos_invPos
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T15:53:34.211876+00:00
-- url     : https://prove2.me/submissions/2e88f59e-e280-40e0-a200-b9db02084a50

import Definitions.Def_Hintz2026_Chiral

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) {z : Fin 2 -> ℝ} (hz : z ∈ U p) : yPos p 1 (invPos p yplus yminus) z = yplus z ∧ yPos p (-1) (invPos p yplus yminus) z = yminus z :=
  by
    have hpre : (↑(prePos p z) : ℂ) ≠ 0 := by exact_mod_cast (prePos_pos p hz).ne'
    have hsD : (↑(Real.sqrt (Del p (z 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (Del_pos p hz.1)).ne'
    have hQ : (↑p.Q : ℂ) ≠ 0 := by exact_mod_cast p.hQ
    constructor <;> (funext i; fin_cases i) <;> simp only [yPos, invPos] <;>
      field_simp <;> push_cast <;> ring

end
