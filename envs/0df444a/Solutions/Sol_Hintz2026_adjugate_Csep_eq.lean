-- Prove2me | solution 1 for Hintz2026.adjugate_Csep_eq
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T14:56:18.06587+00:00
-- url     : https://prove2.me/submissions/280cae15-437f-4027-a6f6-c85ce95b120c

import Definitions.Def_Hintz2026_System4

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (sg om mm : ℝ) (x : Fin 2 -> ℝ) : adjugate (Csep p sg om mm x) = (Rmat p sg om mm (x 0)).transpose - I • Thmat p sg om mm (x 1) :=
  by
    rw [adjugate_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Csep, Rmat, Thmat, Matrix.smul_apply, Matrix.transpose_apply] <;> ring

end
