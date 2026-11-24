-- Prove2me | solution 1 for GlobalTheory.T.congruence_subgroup_is_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:05:35.591783+00:00
-- url     : https://prove2.me/submissions/ebfe92a5-700a-40d5-a64e-4d92cddc73a4

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceSubgroupIsOpen
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceSubgroupIsOpenStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_isOpen_congK


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
theorem _root_.solution : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), 0 < r → IsOpen (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.isOpen_congK | exact GlobalTheory.CompanionTheory.CartGL.isOpen_congK | (intros; apply GlobalTheory.CompanionTheory.CartGL.isOpen_congK <;> assumption)
end _root_.GlobalTheory.T
