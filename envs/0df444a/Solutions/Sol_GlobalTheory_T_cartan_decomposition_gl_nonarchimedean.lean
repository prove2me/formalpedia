-- Prove2me | solution 1 for GlobalTheory.T.cartan_decomposition_gl_nonarchimedean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:27:40.981557+00:00
-- url     : https://prove2.me/submissions/e965846e-5394-4763-96ca-0edb58f5d744

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecompositionGlNonarchimedean
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecompositionGlNonarchimedeanStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_cartan_unitBall


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] (n : ℕ) (p : Lˣ), GlobalTheory.CompanionTheory.CartGL.IsUnif p → ∀ g : GL (Fin n) L, ∃ a : Fin n → ℤ, Antitone a ∧ ∃ k₁ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n 1 zero_le_one le_rfl, ∃ k₂ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n 1 zero_le_one le_rfl, g = k₁ * GlobalTheory.CompanionTheory.CartGL.dPow p a * k₂ := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.cartan_unitBall | exact GlobalTheory.CompanionTheory.CartGL.cartan_unitBall | (intros; apply GlobalTheory.CompanionTheory.CartGL.cartan_unitBall <;> assumption)
end _root_.GlobalTheory.T
