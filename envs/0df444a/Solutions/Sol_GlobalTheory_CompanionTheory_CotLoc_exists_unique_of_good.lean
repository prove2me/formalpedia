-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CotLoc.exists_unique_of_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:11:08.256557+00:00
-- url     : https://prove2.me/submissions/c5cc443c-5c13-4ada-986f-e301e6929059

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExists
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_CotLoc_spMap_comp__c7aa3ec5f5b7
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_base_eq

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
namespace GlobalTheory.CompanionTheory.CotLoc
theorem _root_.solution (hcot : IsCot s e W y₀) (hes : e ≫ s = 𝟙 _)
    (hjs : j ≫ s = spMap (algebraMap C A) ≫ k)
    (hje : spMap (algebraMap A R') ≫ j = spMap (algebraMap R R') ≫ e)
    (ψ : A →+* TrivSqZeroExt R' M) (hψ : Good (C := C) ψ) :
    ∃! u : W →ₗ[R] M, spMap ψ ≫ j = spMap (tsz u) ≫ y₀ := by
  refine hcot.2.2 R' M (spMap ψ ≫ j) ?_ ?_
  · rw [Category.assoc, hjs, ← Category.assoc, ← spMap_comp', hψ.2, spMap_comp', Category.assoc,
      ← base_eq hes hjs hje, ← spMap_comp']
  · rw [← Category.assoc, ← spMap_comp', hψ.1, hje]
end GlobalTheory.CompanionTheory.CotLoc
