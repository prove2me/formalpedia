-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AffAcyc.chain_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:28:07.968871+00:00
-- url     : https://prove2.me/submissions/e4d8f420-d919-4394-9394-60fabf36ba51

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
variable {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R)
namespace GlobalTheory.CompanionTheory.AffAcyc
theorem _root_.solution (c : Fin 1 ⥤ Pᵒᵖ) : c = (Functor.const (Fin 1)).obj (c.obj 0) :=
  CategoryTheory.Functor.ext (fun i ↦ by rw [Subsingleton.elim i 0]; rfl)
    fun _ _ _ ↦ Quiver.Hom.unop_inj (Subsingleton.elim _ _)
end GlobalTheory.CompanionTheory.AffAcyc
