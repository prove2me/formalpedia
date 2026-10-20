-- Prove2me | solution 1 for Hintz2026.contDiffOn_Y_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T13:53:22.192236+00:00
-- url     : https://prove2.me/submissions/9bdaebbb-b037-4ca8-addb-ae4b9a6a65c4

import Definitions.Def_Hintz2026_AnalysisV2

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) {v : (Fin 2 → ℝ) → Fin 2 → ℂ} (hv : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => v x j) (U p)) (i : Fin 2) : ContDiffOn ℝ ∞ (fun x => (((X p x)ᴴ)⁻¹ *ᵥ v x) i) (U p) :=
  by
    simp only [mulVec, dotProduct, Fin.sum_univ_two]
    exact (((contDiffOn_Y_entry p i 0).of_le le_top).mul (hv 0)).add
      (((contDiffOn_Y_entry p i 1).of_le le_top).mul (hv 1))

end
