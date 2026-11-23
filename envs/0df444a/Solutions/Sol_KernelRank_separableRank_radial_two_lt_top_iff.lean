-- Prove2me | solution 1 for KernelRank.separableRank_radial_two_lt_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:29:55.06913+00:00
-- url     : https://prove2.me/submissions/f43a6eba-bcb2-4666-b7bd-ea9fa4591b6b

import Definitions.Def_KernelRankLean_RowSpan
import Definitions.Def_KernelRankLean_Translations
import Theorems.Thm_KernelRank_separableRank_radial_eq_hankel
import Theorems.Thm_KernelRank_rowSpan_hankelTwo
import Theorems.Thm_KernelRank_separableRank_lt_top_iff


set_option autoImplicit true
open NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {𝕜 : Type*} [Field 𝕜] (φ : ℝ → 𝕜) :
    separableRank (fun x : Fin 2 → ℝ => φ (∑ i, x i ^ 2)) < ⊤ ↔
      FiniteDimensional 𝕜 (translateSpan φ) := by
  rw [separableRank_radial_eq_hankel, separableRank_lt_top_iff, rowSpan_hankelTwo]
end KernelRank
