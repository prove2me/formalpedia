-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeCx.cxSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:44:40.76505+00:00
-- url     : https://prove2.me/submissions/78b48c74-4466-4068-b408-f02e829dd22b

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DnCompDn
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeCx_dn_comp_dn
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeCx_pulln_dn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory GlobalTheory.CatCoh MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeCx
variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]
namespace GlobalTheory.CompanionTheory.HodgeCx
theorem _root_.solution : CxSt := by
  intro R _ C _ F
  exact ⟨GlobalTheory.CompanionTheory.HodgeCx.dn_comp_dn F, fun D _ G m n => GlobalTheory.CompanionTheory.HodgeCx.pulln_dn m n⟩
end GlobalTheory.CompanionTheory.HodgeCx
