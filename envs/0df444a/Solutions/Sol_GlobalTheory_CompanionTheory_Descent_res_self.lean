-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Descent.res_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:29:06.000344+00:00
-- url     : https://prove2.me/submissions/1e34d281-953c-47e7-83c7-e6a1fa29dad5

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
namespace GlobalTheory.CompanionTheory.Descent
theorem _root_.solution {U : X.Opens} (h : U ≤ U) (b : Sec s U) : Sec.res s h b = b :=
  congrArg (fun q ↦ q.hom b) (X.presheaf.map_id (op U))
end GlobalTheory.CompanionTheory.Descent
