-- Prove2me | solution 1 for GroundTheory.LocalField.continuous_iff_restrictAb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:50:41.478812+00:00
-- url     : https://prove2.me/submissions/f10767ae-b8c9-42fe-9adb-f63bc3b16321

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalAbelianExtension
import Theorems.Thm_GroundTheory_LocalField_continuous_restrictAb
import Theorems.Thm_GroundTheory_LocalField_isClosedEmbedding_restrictAbPi

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
theorem _root_.solution {X : Type*} [TopologicalSpace X]
    {f : X → maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω} :
    Continuous f ↔ ∀ (L : IntermediateField F Ω) [FiniteDimensional F L] [IsAbelianGalois F L],
      Continuous fun x => restrictAb L (le_maximalAbelianExtension L) (f x) := by
  constructor
  · intro hf L _ _
    exact (continuous_restrictAb _ _).comp hf
  · intro h
    rw [isClosedEmbedding_restrictAbPi.isInducing.continuous_iff, continuous_pi_iff]
    intro L
    have := L.2.1
    have := L.2.2
    exact h (L : IntermediateField F Ω)
end GroundTheory.LocalField
