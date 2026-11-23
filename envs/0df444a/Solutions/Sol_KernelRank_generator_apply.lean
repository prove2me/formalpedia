-- Prove2me | solution 1 for KernelRank.generator_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:27:34.733904+00:00
-- url     : https://prove2.me/submissions/c3a97750-870f-44d1-ae8e-4ef5d7a1347d

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
variable (ψ : ℝ → ℂ) [FiniteDimensional ℂ (translateSpan ψ)]
attribute [local instance] translateNormedAddCommGroup translateNormedSpace translateUniformSpace
attribute [local instance] translateCompleteSpace
namespace KernelRank
theorem _root_.solution (A : translateSpan ψ →L[ℂ] translateSpan ψ)
    (hA : ∀ t : ℝ, 0 ≤ t → shiftCLM ψ t = NormedSpace.exp ((t : ℂ) • A))
    (g : translateSpan ψ) {t : ℝ} (ht : 0 ≤ t) (u : ℝ≥0) :
    (NormedSpace.exp ((t : ℂ) • A) g).1 u = g.1 (u + t.toNNReal) := by
  rw [← hA t ht]
  rfl
end KernelRank
