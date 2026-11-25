-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HopfSys.appLE_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:36:04.335878+00:00
-- url     : https://prove2.me/submissions/eb95719d-313f-434a-9134-0d6edfdc863b

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechTripleRestrictCompositeInjectiveCohomologyFo

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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge Limits
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HopfSys
variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {P : Type} [SemilatticeInf P] (S : Sys A.left P)
  [IsSeparated A.hom]
namespace GlobalTheory.CompanionTheory.HopfSys
theorem _root_.solution {X Y Z : Scheme.{0}} (ψ : X ⟶ Y) (φ : Y ⟶ Z) (χ : X ⟶ Z) (hχ : ψ ≫ φ = χ) {U : Z.Opens}
    {V : Y.Opens} {W : X.Opens} (e1 : V ≤ φ ⁻¹ᵁ U) (e2 : W ≤ ψ ⁻¹ᵁ V) (e3 : W ≤ χ ⁻¹ᵁ U) (x : Γ(Z, U)) :
    (ψ.appLE V W e2).hom ((φ.appLE U V e1).hom x) = (χ.appLE U W e3).hom x := by
  subst hχ
  exact congrArg (fun t ↦ t.hom x) (Scheme.Hom.appLE_comp_appLE ψ φ U V W e1 e2)
end GlobalTheory.CompanionTheory.HopfSys
