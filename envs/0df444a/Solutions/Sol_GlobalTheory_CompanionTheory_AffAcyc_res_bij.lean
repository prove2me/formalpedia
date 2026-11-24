-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AffAcyc.res_bij
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:28:18.726209+00:00
-- url     : https://prove2.me/submissions/381b8f1c-84ca-46f1-940b-6aa48a1669ae

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExactOfSpan

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AffAcyc
variable {R : Type} [CommRing R] {X : Scheme.{0}} {P : Type} [SemilatticeInf P]
namespace GlobalTheory.CompanionTheory.AffAcyc
theorem _root_.solution (s : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (e : U = V) :
    Function.Bijective (Sec.res s h) := by
  subst e
  have : ⇑(Sec.res s h) = id := funext fun b ↦
    congrArg (fun q ↦ q.hom b) (X.presheaf.map_id (op U))
  rw [this]
  exact Function.bijective_id
end GlobalTheory.CompanionTheory.AffAcyc
