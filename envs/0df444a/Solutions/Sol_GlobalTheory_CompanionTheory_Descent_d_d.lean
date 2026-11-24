-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Descent.d_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:28:13.647504+00:00
-- url     : https://prove2.me/submissions/ff4e998a-51e5-4b6f-badd-da23cebde01b

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
variable {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.Descent
theorem _root_.solution (hCx : CxSt) (n : ℕ) (z : Cn F n) : dn F (n + 1) (dn F n z) = 0 :=
  LinearMap.congr_fun ((hCx R C F).1 n) z
end GlobalTheory.CompanionTheory.Descent
