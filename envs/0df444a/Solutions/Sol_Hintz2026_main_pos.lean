-- Prove2me | solution 1 for Hintz2026.main_pos
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T16:05:33.93698+00:00
-- url     : https://prove2.me/submissions/1f97cb5e-e1b0-4a37-8cd0-fdc6d795df93

import Definitions.Def_Hintz2026_Chiral
import Theorems.Thm_Hintz2026_contDiffOn_yPos
import Theorems.Thm_Hintz2026_sys1_iff_sys4_pos
import Theorems.Thm_Hintz2026_sys4_iff_sys7

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (om mm : ℝ) (F : PosFields) (hF : PosSmooth p F) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : Sys1PosAt p om mm F x ↔ Sys7At p 1 om mm (yPos p 1 F) (yPos p (-1) F) x :=
  (sys1_iff_sys4_pos p om mm hx F (posDiff_of_smooth p hF hx)).trans
      (sys4_iff_sys7 p 1 om mm _ _ (contDiffOn_yPos p hF 1) (contDiffOn_yPos p hF (-1)) hx)

end
