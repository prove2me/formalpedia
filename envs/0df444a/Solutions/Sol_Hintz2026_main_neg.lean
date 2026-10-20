-- Prove2me | solution 1 for Hintz2026.main_neg
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T16:05:32.035971+00:00
-- url     : https://prove2.me/submissions/1c648e74-0095-4244-8d59-795423952aa7

import Definitions.Def_Hintz2026_Chiral
import Theorems.Thm_Hintz2026_contDiffOn_yNeg
import Theorems.Thm_Hintz2026_sys1_iff_sys4_neg
import Theorems.Thm_Hintz2026_sys4_iff_sys7

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (om mm : ℝ) (G : NegFields) (hG : NegSmooth p G) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : Sys1NegAt p om mm G x ↔ Sys7At p (-1) om mm (yNeg p 1 G) (yNeg p (-1) G) x :=
  (sys1_iff_sys4_neg p om mm hx G (negDiff_of_smooth p hG hx)).trans
      (sys4_iff_sys7 p (-1) om mm _ _ (contDiffOn_yNeg p hG 1) (contDiffOn_yNeg p hG (-1)) hx)

end
