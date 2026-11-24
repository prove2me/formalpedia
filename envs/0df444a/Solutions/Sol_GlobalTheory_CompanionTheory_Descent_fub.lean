-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Descent.fub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:37:03.985334+00:00
-- url     : https://prove2.me/submissions/5fa61321-f4d3-4576-a8c1-e3df797e81b2

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
theorem _root_.solution (hFub : FubiniSt) [Quiver.IsThin C] [Quiver.IsThin D] (f : C ⥤ AffOp X) (w : C × D ⥤ AffOp X)
    (h : ∀ T, (w.obj T).unop.1 ≤ (f.obj T.1).unop.1)
    (A : ∀ c, Acyc s (CategoryTheory.Prod.sectR c D ⋙ w) (f.obj c).unop.1 (fun T ↦ h (c, T))) :
    AllQIso (rm s f w (CategoryTheory.Prod.fst C D) h) :=
  hFub R C (f ⋙ OAff s) D (w ⋙ OAff s) (pj s f w h) (fun T ↦ A T)
end GlobalTheory.CompanionTheory.Descent
