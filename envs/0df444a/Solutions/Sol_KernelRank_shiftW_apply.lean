-- Prove2me | solution 1 for KernelRank.shiftW_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:06:11.232601+00:00
-- url     : https://prove2.me/submissions/132d6622-5931-44a2-b194-32b87841ab53

import Definitions.Def_ImportCompatibility_Normability
import Definitions.Def_KernelRankLean_Translations
import Definitions.Def_KernelRankLean_Semigroup
import Definitions.Def_KernelRankLean_Complexification
import Definitions.Def_KernelRankLean_TranslationSemigroup

set_option autoImplicit true
open NNReal
open KernelRank
variable {𝕜 : Type*} [Field 𝕜]
variable (φ : ℝ → 𝕜)
namespace KernelRank
theorem _root_.solution (t : ℝ≥0) (g : translateSpan φ) (u : ℝ≥0) :
    (shiftW φ t g : ℝ≥0 → 𝕜) u = (g : ℝ≥0 → 𝕜) (u + t) := rfl
end KernelRank
