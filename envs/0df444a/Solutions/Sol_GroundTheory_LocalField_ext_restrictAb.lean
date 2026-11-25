-- Prove2me | solution 1 for GroundTheory.LocalField.ext_restrictAb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:45:19.438627+00:00
-- url     : https://prove2.me/submissions/7801d168-8eeb-41f3-9c63-12038c8e6b10

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalAbelianExtension
import Theorems.Thm_GroundTheory_LocalField_restrictAb_apply
import Theorems.Thm_GroundTheory_LocalField_exists_finite_abelian_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open IntermediateField
open scoped commutatorElement
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
namespace GroundTheory.LocalField
theorem _root_.solution {σ τ : maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω}
    (h : ∀ (L : IntermediateField F Ω) [FiniteDimensional F L] [IsAbelianGalois F L],
      restrictAb L (le_maximalAbelianExtension L) σ = restrictAb L (le_maximalAbelianExtension L) τ) :
    σ = τ := by
  ext x
  obtain ⟨L, hL1, hL2, hxL⟩ := exists_finite_abelian_mem x.2
  have := congrArg (fun ρ : L ≃ₐ[F] L => ((ρ ⟨x, hxL⟩ : L) : Ω)) (h L)
  simpa only [restrictAb_apply] using this
end GroundTheory.LocalField
