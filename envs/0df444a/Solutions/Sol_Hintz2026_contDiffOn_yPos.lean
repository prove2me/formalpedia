-- Prove2me | solution 1 for Hintz2026.contDiffOn_yPos
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T15:53:21.203981+00:00
-- url     : https://prove2.me/submissions/5d6e96ef-5f9c-4030-bbbc-e3afd7b8784a

import Definitions.Def_Hintz2026_Chiral

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) {F : PosFields} (hF : PosSmooth p F) (e : ℝ) (j : Fin 2) : ContDiffOn ℝ ∞ (fun x => yPos p e F x j) (U p) :=
  by
    fin_cases j
    · show ContDiffOn ℝ ∞ (fun x => yPos p e F x 0) (U p)
      simp only [yPos_0, g1]
      refine (contDiffOn_prePos p).mul (hF.psi2.add ?_)
      simp only [div_eq_mul_inv]
      exact (contDiffOn_const.mul hF.psi1).mul (contDiffOn_inv_sqrtDel_c p)
    · show ContDiffOn ℝ ∞ (fun x => yPos p e F x 1) (U p)
      simp only [yPos_1, g2]
      refine (contDiffOn_prePos p).mul (contDiffOn_const.mul (hF.k.add ?_))
      simp only [div_eq_mul_inv]
      exact (contDiffOn_const.mul hF.s).mul (contDiffOn_inv_sqrtDel_c p)

end
