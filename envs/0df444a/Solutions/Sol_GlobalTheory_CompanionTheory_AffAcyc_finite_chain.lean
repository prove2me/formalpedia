-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AffAcyc.finite_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:28:08.73948+00:00
-- url     : https://prove2.me/submissions/2f88eb2f-b7b4-4dc6-b7b6-fcc87196c1f3

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
theorem _root_.solution [Finite P] (m : ℕ) : Finite (Fin m ⥤ Pᵒᵖ) :=
  haveI : Finite Pᵒᵖ := Finite.of_equiv P Opposite.equivToOpposite
  Finite.of_injective (fun c i ↦ c.obj i) fun _ _ h ↦
    CategoryTheory.Functor.ext (congrFun h) fun _ _ _ ↦ Quiver.Hom.unop_inj (Subsingleton.elim _ _)
end GlobalTheory.CompanionTheory.AffAcyc
