-- Prove2me | solution 1 for GlobalTheory.T.congruence_subgroup_is_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:05:34.61866+00:00
-- url     : https://prove2.me/submissions/ea3a1988-9b58-4f18-a0c1-2358d9e3c9f2

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceSubgroupIsCompact
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceSubgroupIsCompactStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_isCompact_congK


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
theorem _root_.solution : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), IsCompact (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.isCompact_congK | exact GlobalTheory.CompanionTheory.CartGL.isCompact_congK | (intros; apply GlobalTheory.CompanionTheory.CartGL.isCompact_congK <;> assumption)
end _root_.GlobalTheory.T
