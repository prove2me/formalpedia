-- Prove2me | solution 1 for Hintz2026.yNeg_invNeg
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T15:53:32.022033+00:00
-- url     : https://prove2.me/submissions/d9af3916-eff7-418b-84e1-3feefe584912

import Definitions.Def_Hintz2026_Chiral

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) {z : Fin 2 -> ℝ} (hz : z ∈ U p) : yNeg p 1 (invNeg p yplus yminus) z = yplus z ∧ yNeg p (-1) (invNeg p yplus yminus) z = yminus z :=
  by
    have hpre : (↑(preNeg p z) : ℂ) ≠ 0 := by exact_mod_cast (preNeg_pos p hz).ne'
    have hsD : (↑(Real.sqrt (Del p (z 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (Del_pos p hz.1)).ne'
    have hQ : (↑p.Q : ℂ) ≠ 0 := by exact_mod_cast p.hQ
    constructor <;> (funext i; fin_cases i) <;> simp only [yNeg, invNeg] <;>
      field_simp <;> push_cast <;> ring

end
