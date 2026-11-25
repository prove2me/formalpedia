-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CotLoc.exists_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:58:28.887945+00:00
-- url     : https://prove2.me/submissions/c1df4439-285f-4ffd-b2ac-725740461cd1

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExists
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_CotLoc_spMap_comp__c7aa3ec5f5b7
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_spMap_injective
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_landing
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_base_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_fst_tsz
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_tsz_inl
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



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
    [IsOpenImmersion j] [Mono k]
    (hjs : j ≫ s = spMap (algebraMap C A) ≫ k)
    (hje : spMap (algebraMap A R') ≫ j = spMap (algebraMap R R') ≫ e)
    (u : W →ₗ[R] M) :
    ∃ ψ : A →+* TrivSqZeroExt R' M, Good (C := C) ψ ∧ spMap ψ ≫ j = spMap (tsz u) ≫ y₀ := by
  have hy : spMap (TrivSqZeroExt.fstHom R' R' M).toRingHom ≫ spMap (tsz u) ≫ y₀ =
      spMap (algebraMap A R') ≫ j := by
    rw [← Category.assoc, ← spMap_comp', fst_tsz, spMap_comp', Category.assoc, hcot.2.1, hje]
  obtain ⟨ψ, hψ⟩ := landing j (algebraMap A R') (TrivSqZeroExt.fstHom R' R' M).toRingHom
    (fun x => ⟨TrivSqZeroExt.inl x, by simp⟩)
    (fun x hx => ⟨2, by
      have hx' : x.fst = 0 := hx
      ext <;> simp [pow_two, hx']⟩) _ hy
  refine ⟨ψ, ⟨?_, ?_⟩, hψ.symm⟩
  · apply spMap_injective
    rw [← cancel_mono j, spMap_comp', Category.assoc, ← hψ, hy]
  · apply spMap_injective
    rw [← cancel_mono k, spMap_comp', Category.assoc, ← hjs, ← Category.assoc (spMap ψ), ← hψ,
      Category.assoc, hcot.1, ← spMap_comp', tsz_inl, spMap_comp' (algebraMap R R'), base_eq hes hjs hje,
      spMap_comp' ((algebraMap A R').comp (algebraMap C A)), Category.assoc]
end GlobalTheory.CompanionTheory.CotLoc
