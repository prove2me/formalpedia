-- Prove2me | solution 1 for Hintz2026.contDiffOn_Xstar_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T13:56:29.854616+00:00
-- url     : https://prove2.me/submissions/c46836da-0826-4e33-bba0-f0886e585c43

import Definitions.Def_Hintz2026_AnalysisV2
import Theorems.Thm_Hintz2026_contDiffOn_Xstar_entry

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) {v : (Fin 2 → ℝ) → Fin 2 → ℂ} (hv : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => v x j) (U p)) (i : Fin 2) : ContDiffOn ℝ ∞ (fun x => ((X p x)ᴴ *ᵥ v x) i) (U p) :=
  by
    simp only [mulVec, dotProduct, Fin.sum_univ_two]
    exact (((contDiffOn_Xstar_entry p i 0).of_le le_top).mul (hv 0)).add
      (((contDiffOn_Xstar_entry p i 1).of_le le_top).mul (hv 1))

end
