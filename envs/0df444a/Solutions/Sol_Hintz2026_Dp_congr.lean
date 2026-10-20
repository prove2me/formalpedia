-- Prove2me | solution 1 for Hintz2026.Dp_congr
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T13:53:13.468569+00:00
-- url     : https://prove2.me/submissions/44983ce0-1709-4292-b7a6-b720f2a1c59a

import Definitions.Def_Hintz2026_AnalysisV2

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) {f g : (Fin 2 → ℝ) → ℂ} {x : Fin 2 → ℝ} (hU : x ∈ U p) (h : Set.EqOn f g (U p)) : Dp p f x = Dp p g x :=
  by
    unfold Dp; rw [cpd_congr p 0 hU h, cpd_congr p 1 hU h]

end
