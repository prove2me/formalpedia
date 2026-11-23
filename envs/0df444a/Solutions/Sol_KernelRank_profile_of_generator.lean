-- Prove2me | solution 1 for KernelRank.profile_of_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:30:06.644043+00:00
-- url     : https://prove2.me/submissions/ece3901e-f600-44f3-ae4b-0a6c316485f4

import Definitions.Def_ImportCompatibility_Normability
import Definitions.Def_KernelRankLean_Translations
import Definitions.Def_KernelRankLean_Semigroup
import Definitions.Def_KernelRankLean_Complexification
import Definitions.Def_KernelRankLean_TranslationSemigroup
import Theorems.Thm_KernelRank_generator_apply
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero



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
    {t : ℝ} (ht : 0 ≤ t) :
    ψ t = evalW ψ 0 (NormedSpace.exp ((t : ℂ) • A) (initialProfile ψ)) := by
  change ψ t = (NormedSpace.exp ((t : ℂ) • A) (initialProfile ψ)).1 0
  rw [generator_apply ψ A hA _ ht]
  simp [initialProfile, Real.coe_toNNReal t ht]
end KernelRank
