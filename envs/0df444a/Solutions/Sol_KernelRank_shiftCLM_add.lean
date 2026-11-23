-- Prove2me | solution 1 for KernelRank.shiftCLM_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:08:12.231981+00:00
-- url     : https://prove2.me/submissions/8c95cd74-77d8-4139-9b20-497c5de4cd8c

import Definitions.Def_ImportCompatibility_Normability
import Definitions.Def_KernelRankLean_Translations
import Definitions.Def_KernelRankLean_Semigroup
import Definitions.Def_KernelRankLean_Complexification
import Definitions.Def_KernelRankLean_TranslationSemigroup
import Theorems.Thm_KernelRank_shiftW_apply
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
theorem _root_.solution {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    shiftCLM ψ (s + t) = shiftCLM ψ s * shiftCLM ψ t := by
  ext g u
  simp [shiftCLM, shiftW_apply, Real.toNNReal_add hs ht, add_assoc]
end KernelRank
