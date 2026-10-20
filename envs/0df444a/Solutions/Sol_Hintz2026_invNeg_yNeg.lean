-- Prove2me | solution 1 for Hintz2026.invNeg_yNeg
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T15:53:24.289988+00:00
-- url     : https://prove2.me/submissions/9ccc963b-3b31-44e7-b6a4-0e424be54bfd

import Definitions.Def_Hintz2026_Chiral

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (G : NegFields) {z : Fin 2 -> ℝ} (hz : z ∈ U p) : (invNeg p (yNeg p 1 G) (yNeg p (-1) G)).psim2 z = G.psim2 z ∧ (invNeg p (yNeg p 1 G) (yNeg p (-1) G)).psim1 z = G.psim1 z ∧ (invNeg p (yNeg p 1 G) (yNeg p (-1) G)).n z = G.n z ∧ (invNeg p (yNeg p 1 G) (yNeg p (-1) G)).l z = G.l z :=
  by
    have hpre : (↑(preNeg p z) : ℂ) ≠ 0 := by exact_mod_cast (preNeg_pos p hz).ne'
    have hsD : (↑(Real.sqrt (Del p (z 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (Del_pos p hz.1)).ne'
    have hQ : (↑p.Q : ℂ) ≠ 0 := by exact_mod_cast p.hQ
    simp only [invNeg, yNeg, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> push_cast <;> ring

end
