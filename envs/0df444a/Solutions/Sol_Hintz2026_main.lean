-- Prove2me | solution 1 for Hintz2026.main
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T16:09:09.662298+00:00
-- url     : https://prove2.me/submissions/333e0f0c-b2e9-447c-a1ce-6f0dace161dc

import Definitions.Def_Hintz2026_Chiral
import Theorems.Thm_Hintz2026_main_pos
import Theorems.Thm_Hintz2026_main_neg

open Hintz2026 Complex Function Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (om mm : ℝ) :
    (∀ F : PosFields, PosSmooth p F → ∀ x ∈ U p,
        (Sys1PosAt p om mm F x ↔ Sys7At p 1 om mm (yPos p 1 F) (yPos p (-1) F) x)) ∧
    (∀ G : NegFields, NegSmooth p G → ∀ x ∈ U p,
        (Sys1NegAt p om mm G x ↔ Sys7At p (-1) om mm (yNeg p 1 G) (yNeg p (-1) G) x)) :=
  ⟨fun F hF x hx => main_pos p om mm F hF hx, fun G hG x hx => main_neg p om mm G hG hx⟩

end
