-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeCx.cof_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:42:42.798241+00:00
-- url     : https://prove2.me/submissions/9f85a93b-ecbb-4a93-a036-df162b0d07e3

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DnCompDn

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
variable (F : C ⥤ CommAlgCat.{0} R)
namespace GlobalTheory.CompanionTheory.HodgeCx
theorem _root_.solution (n : ℕ) (i : Fin (n + 2)) :
    cof F n i = act F (Fin.succAboveOrderEmb i).toOrderHom := rfl
end GlobalTheory.CompanionTheory.HodgeCx
