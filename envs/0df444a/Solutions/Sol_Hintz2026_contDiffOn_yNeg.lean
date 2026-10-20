-- Prove2me | solution 1 for Hintz2026.contDiffOn_yNeg
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T15:53:19.127813+00:00
-- url     : https://prove2.me/submissions/b91eaa05-d44d-45fb-8193-f52634d94db8

import Definitions.Def_Hintz2026_Chiral

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) {G : NegFields} (hG : NegSmooth p G) (e : ℝ) (j : Fin 2) : ContDiffOn ℝ ∞ (fun x => yNeg p e G x j) (U p) :=
  by
    fin_cases j
    · show ContDiffOn ℝ ∞ (fun x => yNeg p e G x 0) (U p)
      simp only [yNeg_0, g1N]
      exact (contDiffOn_preNeg p).mul (hG.psim2.sub ((contDiffOn_const.mul (contDiffOn_sqrtDel_c p)).mul hG.psim1))
    · show ContDiffOn ℝ ∞ (fun x => yNeg p e G x 1) (U p)
      simp only [yNeg_1, g2N]
      exact (contDiffOn_preNeg p).mul (contDiffOn_const.mul (hG.n.sub ((contDiffOn_const.mul (contDiffOn_sqrtDel_c p)).mul hG.l)))

end
