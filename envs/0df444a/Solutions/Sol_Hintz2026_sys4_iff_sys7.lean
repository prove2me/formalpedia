-- Prove2me | solution 1 for Hintz2026.sys4_iff_sys7
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T15:53:29.940987+00:00
-- url     : https://prove2.me/submissions/361f1ee4-4b89-47ca-9b29-4e8e37fca8a6

import Definitions.Def_Hintz2026_Chiral
import Theorems.Thm_Hintz2026_system4_iff_system7

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (sg om mm : ℝ) (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) (hyp : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => yplus x j) (U p)) (hym : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => yminus x j) (U p)) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : Sys4At p sg om mm yplus yminus x ↔ Sys7At p sg om mm yplus yminus x :=
  system4_iff_system7 p yplus yminus sg om mm hyp hym hx

end
