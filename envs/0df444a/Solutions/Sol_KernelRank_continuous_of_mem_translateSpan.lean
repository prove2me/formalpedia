-- Prove2me | solution 1 for KernelRank.continuous_of_mem_translateSpan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:27:29.702639+00:00
-- url     : https://prove2.me/submissions/075c37f9-8c26-49c5-91b8-4c5e80cf4ff8

import Definitions.Def_ImportCompatibility_Normability
import Definitions.Def_KernelRankLean_Translations
import Definitions.Def_KernelRankLean_Semigroup
import Definitions.Def_KernelRankLean_Complexification
import Definitions.Def_KernelRankLean_TranslationSemigroup
import Theorems.Thm_KernelRank_IsSumOfProducts_add


set_option autoImplicit true
open NNReal
open KernelRank
variable {𝕜 : Type*} [Field 𝕜]
variable (φ : ℝ → 𝕜)
variable (ψ : ℝ → ℂ) [FiniteDimensional ℂ (translateSpan ψ)]
attribute [local instance] translateNormedAddCommGroup translateNormedSpace translateUniformSpace
attribute [local instance] translateCompleteSpace
omit [FiniteDimensional ℂ (translateSpan ψ)]
namespace KernelRank
theorem _root_.solution (hψ : ContinuousOn ψ (Set.Ici 0))
    {g : ℝ≥0 → ℂ} (hg : g ∈ translateSpan ψ) : Continuous g := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    exact hψ.comp_continuous (NNReal.continuous_coe.add continuous_const)
      fun u => Set.mem_Ici.mpr (add_nonneg u.2 s.2)
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact continuous_const.smul hx
end KernelRank
