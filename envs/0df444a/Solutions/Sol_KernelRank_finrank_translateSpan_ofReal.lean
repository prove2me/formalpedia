-- Prove2me | solution 1 for KernelRank.finrank_translateSpan_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:32:11.673943+00:00
-- url     : https://prove2.me/submissions/7f3ef552-cfb9-4467-b042-33c587e276e1

import Definitions.Def_ImportCompatibility_Normability
import Definitions.Def_KernelRankLean_Translations
import Definitions.Def_KernelRankLean_Semigroup
import Definitions.Def_KernelRankLean_Complexification
import Definitions.Def_KernelRankLean_TranslationSemigroup
import Theorems.Thm_KernelRank_finiteDimensional_translateSpan_ofReal
import Theorems.Thm_KernelRank_finrank_rowSpan_ofReal
import Theorems.Thm_KernelRank_rowSpan_hankelTwo


set_option autoImplicit true
open NNReal
open KernelRank
variable {𝕜 : Type*} [Field 𝕜]
variable (φ : ℝ → 𝕜)
namespace KernelRank
theorem _root_.solution (φ : ℝ → ℝ)
    [FiniteDimensional ℝ (translateSpan φ)] :
    Module.finrank ℂ (translateSpan (fun t => (φ t : ℂ))) =
      Module.finrank ℝ (translateSpan φ) := by
  let := finiteDimensional_translateSpan_ofReal φ
  let K (s : Fin 2 → ℝ≥0) := φ (∑ i, (s i : ℝ))
  have hKR : rowSpan K = translateSpan φ := rowSpan_hankelTwo φ
  have hKC : rowSpan (fun s => (K s : ℂ)) = translateSpan (fun t => (φ t : ℂ)) :=
    rowSpan_hankelTwo (fun t => (φ t : ℂ))
  let : FiniteDimensional ℂ (rowSpan (fun s => (K s : ℂ))) := hKC.symm ▸ inferInstance
  rw [← hKR, ← hKC]
  exact (finrank_rowSpan_ofReal K).symm
end KernelRank
