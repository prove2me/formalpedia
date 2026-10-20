-- Prove2me | solution 1 for Hintz2026.contDiffOn_X_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T13:53:15.320828+00:00
-- url     : https://prove2.me/submissions/57de77e4-a1a8-426a-a8cb-0365b8186f79

import Definitions.Def_Hintz2026_AnalysisV2

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) {v : (Fin 2 → ℝ) → Fin 2 → ℂ} (hv : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => v x j) (U p)) (i : Fin 2) : ContDiffOn ℝ ∞ (fun x => (X p x *ᵥ v x) i) (U p) :=
  by
    simp only [mulVec, dotProduct, Fin.sum_univ_two]
    exact (((contDiffOn_X_entry p i 0).of_le le_top).mul (hv 0)).add
      (((contDiffOn_X_entry p i 1).of_le le_top).mul (hv 1))

end
