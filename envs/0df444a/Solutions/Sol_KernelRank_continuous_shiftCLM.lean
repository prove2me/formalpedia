-- Prove2me | solution 1 for KernelRank.continuous_shiftCLM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:29:50.069137+00:00
-- url     : https://prove2.me/submissions/c329aef7-f47c-47ee-bbfb-c8cc2dbfdb07

import Definitions.Def_ImportCompatibility_Normability
import Definitions.Def_KernelRankLean_Translations
import Definitions.Def_KernelRankLean_Semigroup
import Definitions.Def_KernelRankLean_Complexification
import Definitions.Def_KernelRankLean_TranslationSemigroup
import Theorems.Thm_KernelRank_continuous_of_mem_translateSpan
import Theorems.Thm_KernelRank_IsSumOfProducts_add
import Theorems.Thm_KernelRank_IsSumOfProducts_comp


set_option autoImplicit true
open NNReal
open KernelRank
variable {𝕜 : Type*} [Field 𝕜]
variable (φ : ℝ → 𝕜)
variable (ψ : ℝ → ℂ) [FiniteDimensional ℂ (translateSpan ψ)]
attribute [local instance] translateNormedAddCommGroup translateNormedSpace translateUniformSpace
attribute [local instance] translateCompleteSpace
namespace KernelRank
theorem _root_.solution (hψ : ContinuousOn ψ (Set.Ici 0)) : Continuous (shiftCLM ψ) := by
  apply continuous_clm_apply.mpr
  intro g
  apply Continuous.subtype_mk
  refine continuous_pi fun u => ?_
  exact (continuous_of_mem_translateSpan ψ hψ g.2).comp
    (continuous_const.add continuous_real_toNNReal)
end KernelRank
