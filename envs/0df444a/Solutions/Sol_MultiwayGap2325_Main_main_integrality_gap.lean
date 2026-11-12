-- Prove2me | solution 1 for MultiwayGap2325.Main.main_integrality_gap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T21:38:46.244757+00:00
-- url     : https://prove2.me/submissions/d0d7a41d-d89c-4ff2-93cd-5b90cb102f2a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MultiwayGap2325_Main_FiniteGap
import Theorems.Thm_MultiwayGap2325_Main_non_opposite_reduction
import Theorems.Thm_MultiwayGap2325_Main_beta_le_approximationFactor_eleven

section
set_option autoImplicit false

namespace MultiwayGap2325.Main

theorem chk_main_integrality_gap :
    ∃ g : ℝ, Filter.Tendsto gapSequence Filter.atTop (nhds g) ∧
      beta ≤ g ∧ (12325 : ℝ) / 10000 < beta ∧
      ∀ η : ℝ, 0 < η → ∃ K : ℕ, 2 ≤ K ∧ ∀ k : ℕ, K ≤ k →
        ∃ n : ℕ, ∃ I : MultiwayCut.Instance (Fin n) k,
          beta - η ≤ instanceGap I := by
  have hbeta : (12325 : ℝ) / 10000 < beta := by norm_num [beta]
  have h := non_opposite_reduction 11 (by norm_num) beta (by linarith)
    (fun Ξ _ P _ C α hα => beta_le_approximationFactor_eleven Ξ P C α hα)
  obtain ⟨g, hg, hbg, hη⟩ := h
  exact ⟨g, hg, hbg, hbeta, hη⟩

end MultiwayGap2325.Main
end

theorem solution : type_of% @MultiwayGap2325.Main.chk_main_integrality_gap := @MultiwayGap2325.Main.chk_main_integrality_gap
