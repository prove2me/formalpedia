-- Prove2me | solution 1 for KernelRank.separableRank_radial_two_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:31:05.856799+00:00
-- url     : https://prove2.me/submissions/176ebaad-596e-42ed-bacf-0c40c4698262

import Definitions.Def_KernelRankLean_RowSpan
import Definitions.Def_KernelRankLean_Translations
import Theorems.Thm_KernelRank_separableRank_radial_eq_hankel
import Theorems.Thm_KernelRank_rowSpan_hankelTwo
import Theorems.Thm_KernelRank_separableRank_eq_finrank_rowSpan


set_option autoImplicit true
open NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {𝕜 : Type*} [Field 𝕜] (φ : ℝ → 𝕜)
    [FiniteDimensional 𝕜 (translateSpan φ)] :
    separableRank (fun x : Fin 2 → ℝ => φ (∑ i, x i ^ 2)) =
      Module.finrank 𝕜 (translateSpan φ) := by
  have : FiniteDimensional 𝕜 (rowSpan (fun s : Fin 2 → ℝ≥0 => φ (∑ i, (s i : ℝ)))) := by
    rwa [rowSpan_hankelTwo]
  rw [separableRank_radial_eq_hankel, separableRank_eq_finrank_rowSpan, rowSpan_hankelTwo]
end KernelRank
