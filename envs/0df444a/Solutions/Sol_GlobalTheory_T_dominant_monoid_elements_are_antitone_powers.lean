-- Prove2me | solution 1 for GlobalTheory.T.dominant_monoid_elements_are_antitone_powers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:06:51.880524+00:00
-- url     : https://prove2.me/submissions/04c16621-4efa-4036-91de-3657a2be05db

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DominantMonoidElementsAreAntitonePowers
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DominantMonoidElementsAreAntitonePowersStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_closure_tGen_antitone


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
theorem _root_.solution : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ) (s : GL (Fin n) L), s ∈ Submonoid.closure (Set.range (GlobalTheory.CompanionTheory.CartGL.tGen p : Fin (n + 2) → GL (Fin n) L)) → ∃ a : Fin n → ℤ, Antitone a ∧ s = GlobalTheory.CompanionTheory.CartGL.dPow p a := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.closure_tGen_antitone | exact GlobalTheory.CompanionTheory.CartGL.closure_tGen_antitone | (intros; apply GlobalTheory.CompanionTheory.CartGL.closure_tGen_antitone <;> assumption)
end _root_.GlobalTheory.T
