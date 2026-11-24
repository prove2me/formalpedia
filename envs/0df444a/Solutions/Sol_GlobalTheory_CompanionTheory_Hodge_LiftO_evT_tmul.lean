-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.LiftO.evT_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:25:56.550092+00:00
-- url     : https://prove2.me/submissions/4e876f9d-57e4-4b49-a581-ad72b94c3f07

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorPairingIotaTwo

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge GlobalTheory.CompanionTheory.Hodge.LiftO
variable {R : Type} [CommRing R] {C E : Type} [Category.{0} C] [Category.{0} E]
  {F : C ⥤ CommAlgCat.{0} R} {G : E ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.Hodge.LiftO
theorem _root_.solution (g : C0 F) (ω : Glob1 F) (T : C) : evT (g ⊗ₜ ω) T = g T • ω.1 T := rfl
end GlobalTheory.CompanionTheory.Hodge.LiftO
