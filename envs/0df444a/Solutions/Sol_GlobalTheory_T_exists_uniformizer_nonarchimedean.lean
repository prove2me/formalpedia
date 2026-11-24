-- Prove2me | solution 1 for GlobalTheory.T.exists_uniformizer_nonarchimedean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:08:09.405888+00:00
-- url     : https://prove2.me/submissions/492489dc-cc7e-405b-a164-f4adcb221f75

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsUniformizerNonarchimedean
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsUniformizerNonarchimedeanStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_exists_isUnif


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
theorem _root_.solution : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L], ∃ p : Lˣ, GlobalTheory.CompanionTheory.CartGL.IsUnif p := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.exists_isUnif | exact GlobalTheory.CompanionTheory.CartGL.exists_isUnif | (intros; apply GlobalTheory.CompanionTheory.CartGL.exists_isUnif <;> assumption)
end _root_.GlobalTheory.T
