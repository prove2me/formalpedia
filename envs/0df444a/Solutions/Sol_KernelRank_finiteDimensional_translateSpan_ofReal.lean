-- Prove2me | solution 1 for KernelRank.finiteDimensional_translateSpan_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:05:52.971601+00:00
-- url     : https://prove2.me/submissions/489e8248-174d-4de4-aa8f-3dc447742ec4

import Definitions.Def_ImportCompatibility_Normability
import Definitions.Def_KernelRankLean_Translations
import Definitions.Def_KernelRankLean_Semigroup
import Definitions.Def_KernelRankLean_Complexification
import Definitions.Def_KernelRankLean_TranslationSemigroup
import Theorems.Thm_KernelRank_IsSumOfProducts_ofReal
import Theorems.Thm_KernelRank_finiteDimensional_rowSpan_of_isSumOfProducts
import Theorems.Thm_KernelRank_isSumOfProducts_finrank_rowSpan
import Theorems.Thm_KernelRank_rowSpan_hankelTwo


set_option autoImplicit true
open NNReal
open KernelRank
variable {𝕜 : Type*} [Field 𝕜]
variable (φ : ℝ → 𝕜)
namespace KernelRank
theorem _root_.solution (φ : ℝ → ℝ)
    [FiniteDimensional ℝ (translateSpan φ)] :
    FiniteDimensional ℂ (translateSpan (fun t => (φ t : ℂ))) := by
  let K (s : Fin 2 → ℝ≥0) := φ (∑ i, (s i : ℝ))
  have hKR : rowSpan K = translateSpan φ := rowSpan_hankelTwo φ
  have hKC : rowSpan (fun s => (K s : ℂ)) = translateSpan (fun t => (φ t : ℂ)) :=
    rowSpan_hankelTwo (fun t => (φ t : ℂ))
  let : FiniteDimensional ℝ (rowSpan K) := hKR.symm ▸ inferInstance
  rw [← hKC]
  exact finiteDimensional_rowSpan_of_isSumOfProducts
    (isSumOfProducts_finrank_rowSpan K).ofReal
end KernelRank
