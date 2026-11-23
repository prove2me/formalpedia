-- Prove2me | solution 1 for KernelRank.rowSpan_hankelTwo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:51:31.578631+00:00
-- url     : https://prove2.me/submissions/638d8e2d-5765-441d-a50d-af9ca0cf4c05

import Definitions.Def_KernelRankLean_RowSpan
import Definitions.Def_KernelRankLean_Translations
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero



set_option autoImplicit true
open NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {𝕜 : Type*} [Field 𝕜] (φ : ℝ → 𝕜) :
    rowSpan (fun s : Fin 2 → ℝ≥0 => φ (∑ i, (s i : ℝ))) = translateSpan φ := by
  unfold rowSpan translateSpan
  apply congrArg (Submodule.span 𝕜)
  ext f
  simp [Fin.sum_univ_two]
end KernelRank
