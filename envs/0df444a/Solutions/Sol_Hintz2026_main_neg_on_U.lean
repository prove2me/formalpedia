-- Prove2me | solution 1 for Hintz2026.main_neg_on_U
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T16:07:44.607988+00:00
-- url     : https://prove2.me/submissions/ae2a2d1f-c994-456d-8c55-f64a6baf1552

import Definitions.Def_Hintz2026_Chiral
import Theorems.Thm_Hintz2026_main_neg

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (om mm : ℝ) (G : NegFields) (hG : NegSmooth p G) : (∀ x ∈ U p, Sys1NegAt p om mm G x) ↔ (∀ x ∈ U p, Sys7At p (-1) om mm (yNeg p 1 G) (yNeg p (-1) G) x) :=
  forall₂_congr (fun x hx => main_neg p om mm G hG hx)

end
