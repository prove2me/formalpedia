-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSNormLt.tt_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:31.685145+00:00
-- url     : https://prove2.me/submissions/5c83be33-aa90-487d-a0ca-4f644bd35def

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IndOfNot
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_sig_anti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSNormLt
open CompanionTheory.D.DSIC
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSNormLt
theorem _root_.solution {ε : Fin n → Bool} (A : Finset (NC ε)) (a b : Fin n) : tt A b a = - tt A a b := by
  unfold tt; rw [sig_anti a b]; ring
end GlobalTheory.CompanionTheory.DSNormLt
