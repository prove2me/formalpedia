-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Descent.rm_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:34:44.136091+00:00
-- url     : https://prove2.me/submissions/638d8a76-e773-4e9c-8b7d-834659573752

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteCover

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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Descent
variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
variable {C D E : Type} [Category.{0} C] [Category.{0} D] [Category.{0} E]
namespace GlobalTheory.CompanionTheory.Descent
theorem _root_.solution (f : C ⥤ AffOp X) (g : D ⥤ AffOp X) (σ : D ⥤ C) (h) (i : ℕ) (z : Cn (f ⋙ OAff s) i)
    (c : Fin (i + 1) ⥤ D) :
    pulln (rm s f g σ h) i z c = Sec.res s (h (c.obj (Fin.last i))) (z (c ⋙ σ)) := rfl
end GlobalTheory.CompanionTheory.Descent
