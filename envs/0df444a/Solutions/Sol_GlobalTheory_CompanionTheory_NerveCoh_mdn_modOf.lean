-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NerveCoh.mdn_modOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:34:36.280299+00:00
-- url     : https://prove2.me/submissions/e0597976-3c6b-4c6d-86b8-cac44a957e96

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConeExOfAcyclic

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
open CategoryTheory Opposite
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NerveCoh
variable {R : Type} [CommRing R]
open GlobalTheory.CatCoh MainStatements.Hodge
variable {C D : Type} [Category.{0} C] [Category.{0} D]
namespace GlobalTheory.CompanionTheory.NerveCoh
theorem _root_.solution (F : C ⥤ CommAlgCat.{0} R) (n : ℕ) (f : Cn F n) : mdn (modOf F) n f = dn F n f := rfl
end GlobalTheory.CompanionTheory.NerveCoh
