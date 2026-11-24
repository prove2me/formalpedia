-- Prove2me | solution 1 for GlobalTheory.T.antitone_powers_in_dominant_monoid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:02:45.724857+00:00
-- url     : https://prove2.me/submissions/afbf119d-8fe2-44ca-b32e-d39523190bf5

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AntitonePowersInDominantMonoid
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AntitonePowersInDominantMonoidStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_dPow_antitone_mem_closure


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
theorem _root_.solution : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ) (a : Fin n → ℤ), Antitone a → GlobalTheory.CompanionTheory.CartGL.dPow p a ∈ Submonoid.closure (Set.range (GlobalTheory.CompanionTheory.CartGL.tGen p : Fin (n + 2) → GL (Fin n) L)) := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.dPow_antitone_mem_closure | exact GlobalTheory.CompanionTheory.CartGL.dPow_antitone_mem_closure | (intros; apply GlobalTheory.CompanionTheory.CartGL.dPow_antitone_mem_closure <;> assumption)
end _root_.GlobalTheory.T
