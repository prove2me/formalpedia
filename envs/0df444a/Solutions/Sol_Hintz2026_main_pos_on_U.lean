-- Prove2me | solution 1 for Hintz2026.main_pos_on_U
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T16:07:46.615212+00:00
-- url     : https://prove2.me/submissions/acedd42e-a7bc-4351-9361-9bc8d5dc006a

import Definitions.Def_Hintz2026_Chiral
import Theorems.Thm_Hintz2026_main_pos

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (om mm : ℝ) (F : PosFields) (hF : PosSmooth p F) : (∀ x ∈ U p, Sys1PosAt p om mm F x) ↔ (∀ x ∈ U p, Sys7At p 1 om mm (yPos p 1 F) (yPos p (-1) F) x) :=
  forall₂_congr (fun x hx => main_pos p om mm F hF hx)

end
