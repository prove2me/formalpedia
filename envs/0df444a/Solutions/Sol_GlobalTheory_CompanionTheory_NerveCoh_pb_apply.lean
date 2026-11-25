-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NerveCoh.pb_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:34:39.47597+00:00
-- url     : https://prove2.me/submissions/0193faaf-08cf-43d0-b4a2-9ea5f04a9234

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
variable {C C' D : Type} [Category.{0} C] [Category.{0} C'] [Category.{0} D]
namespace GlobalTheory.CompanionTheory.NerveCoh
theorem _root_.solution (Φ : C' ⥤ C) {F : C ⥤ ModuleCat.{0} R} {G : C' ⥤ ModuleCat.{0} R} (α : Φ ⋙ F ⟶ G) (n : ℕ)
    (f : MCn F n) (c : Fin (n + 1) ⥤ C') : pb Φ α n f c = (α.app (c.obj (Fin.last n))).hom (f (c ⋙ Φ)) := rfl
end GlobalTheory.CompanionTheory.NerveCoh
