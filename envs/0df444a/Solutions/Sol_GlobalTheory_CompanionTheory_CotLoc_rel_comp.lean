-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CotLoc.rel_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:51:14.100106+00:00
-- url     : https://prove2.me/submissions/a4843e95-f4ca-41cc-a61b-c3f08017f116

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExists
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_CotLoc_spMap_comp__c7aa3ec5f5b7
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_tsz_comp
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotLoc
variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} {e : Sp R ⟶ X}
  {W : Type} [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W] [IsCentralScalar R W]
  {y₀ : Sp (TrivSqZeroExt R W) ⟶ X}
  {R' : Type} [CommRing R'] [Algebra R R'] {A C : Type} [CommRing A] [CommRing C] [Algebra C A]
  [Algebra A R'] {j : Sp A ⟶ X} {k : Sp C ⟶ Sp R}
variable {M : Type} [AddCommGroup M] [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]
  [Module R M] [IsScalarTower R R' M]
variable {N : Type} [AddCommGroup N] [Module R' N] [Module R'ᵐᵒᵖ N] [IsCentralScalar R' N]
  [Module R N] [IsScalarTower R R' N]
namespace GlobalTheory.CompanionTheory.CotLoc
theorem _root_.solution {ψ : A →+* TrivSqZeroExt R' M} {u : W →ₗ[R] M} (v : M →ₗ[R'] N)
    (h : spMap ψ ≫ j = spMap (tsz u) ≫ y₀) :
    spMap ((tsz (R := R') (B := R') v).comp ψ) ≫ j =
      spMap (tsz ((v.restrictScalars R).comp u)) ≫ y₀ := by
  rw [spMap_comp', Category.assoc, h, ← tsz_comp, spMap_comp', Category.assoc]
end GlobalTheory.CompanionTheory.CotLoc
