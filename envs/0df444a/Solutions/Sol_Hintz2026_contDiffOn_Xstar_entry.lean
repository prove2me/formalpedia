-- Prove2me | solution 1 for Hintz2026.contDiffOn_Xstar_entry
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T13:53:20.371028+00:00
-- url     : https://prove2.me/submissions/4b687c39-9686-4c17-b56e-afed8a53e848

import Definitions.Def_Hintz2026_AnalysisV2

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (i j : Fin 2) : ContDiffOn ℝ ⊤ (fun x => (X p x)ᴴ i j) (U p) :=
  by
    simp_rw [fun x => show (X p x)ᴴ i j = starRingEnd ℂ (X p x j i) from conjTranspose_apply _ _ _]
    exact Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_X_entry p j i)

end
