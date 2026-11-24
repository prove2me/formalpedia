-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Descent.Acyc.congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:28:20.162893+00:00
-- url     : https://prove2.me/submissions/00cf6da6-fc22-40f0-9233-6fe4a9d64db1

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
namespace Acyc
theorem _root_.solution {f f' : E ⥤ AffOp X} (e : f = f') {W : X.Opens} {hle} {hle'}
    (h : Acyc s f W hle) : Acyc s f' W hle' := by
  subst e; exact h
end Acyc
end GlobalTheory.CompanionTheory.Descent
