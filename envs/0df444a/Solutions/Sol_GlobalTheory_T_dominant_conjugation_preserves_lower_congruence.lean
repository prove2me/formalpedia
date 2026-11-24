-- Prove2me | solution 1 for GlobalTheory.T.dominant_conjugation_preserves_lower_congruence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:06:49.281304+00:00
-- url     : https://prove2.me/submissions/a308c9fd-0887-4cec-a3da-1804909dc938

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DominantConjugationPreservesLowerCongruence
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DominantConjugationPreservesLowerCongruenceStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_Lower_conj_lower_contract


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
theorem _root_.solution : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ), ‖(p : L)‖ < 1 → ∀ (a : Fin n → ℤ), Antitone a → ∀ (r : ℝ) (w : GL (Fin n) L), (∀ i j, i < j → (w : Matrix (Fin n) (Fin n) L) i j = 0) → (∀ i j, ‖((w : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r) → ∀ i j, ‖((((GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ * w * GlobalTheory.CompanionTheory.CartGL.dPow p a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.Lower.conj_lower_contract | exact GlobalTheory.CompanionTheory.CartGL.Lower.conj_lower_contract | (intros; apply GlobalTheory.CompanionTheory.CartGL.Lower.conj_lower_contract <;> assumption)
end _root_.GlobalTheory.T
