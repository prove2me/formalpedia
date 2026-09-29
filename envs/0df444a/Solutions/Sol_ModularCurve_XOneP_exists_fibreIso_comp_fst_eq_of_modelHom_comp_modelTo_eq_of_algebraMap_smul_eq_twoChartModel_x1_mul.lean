-- Prove2me | solution 1 for ModularCurve.XOneP.exists_fibreIso_comp_fst_eq_of_modelHom_comp_modelTo_eq_of_algebraMap_smul_eq_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/307fc067-216a-5317-8736-741b7f6541c1

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_fibreIso_comp_fst_eq_of_modelHom_comp_modelTo_eq_of_algebraMap_smul_eq_twoChartModel_x1_mul

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))
    (hsk : ∀ (s' : L ≃ₐ[ℚ] L) (a : A), algebraMap A k (s' • a) = algebraMap A k a)
    (s : L ≃ₐ[ℚ] L)
    (u v : ModularCurve.TwoChartModel A (↥K) j ⟶ ModularCurve.TwoChartModel A (↥K) j)
    (hu : u ≫ (ModularCurve.TwoChart.modelTo A (↥K) j) = (ModularCurve.TwoChart.modelTo A (↥K) j) ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))))
    (hv : v ≫ (ModularCurve.TwoChart.modelTo A (↥K) j) = (ModularCurve.TwoChart.modelTo A (↥K) j) ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹))))
    (huv : u ≫ v = 𝟙 _) (hvu : v ≫ u = 𝟙 _) :
    ∃ uk : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≅ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k),
      uk.hom ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
        pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≫ u ∧
      uk.hom ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
        pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ∧
      uk.inv ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
        pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≫ v := by
  classical

  set σ := Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)) with hσ
  set σ' := Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹)) with hσ'
  have hbase : ∀ s' : L ≃ₐ[ℚ] L, specMap A k ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s')) = specMap A k := by
    intro s'
    show Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s')) =
      Spec.map (CommRingCat.ofHom (algebraMap A k))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    exact hsk s' a

  let f : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) :=
    pullback.map (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) u (𝟙 _) σ hu.symm (by rw [Category.id_comp, hbase])
  let g : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) :=
    pullback.map (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) v (𝟙 _) σ' hv.symm (by rw [Category.id_comp, hbase])
  have hf₁ : f ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≫ u := pullback.lift_fst _ _ _
  have hf₂ : f ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) := by
    simp only [f, pullback.lift_snd, Category.comp_id]
  have hg₁ : g ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≫ v := pullback.lift_fst _ _ _
  have hg₂ : g ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) := by
    simp only [g, pullback.lift_snd, Category.comp_id]
  have hfg : f ≫ g = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hg₁, ← Category.assoc, hf₁, Category.assoc, huv, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hg₂, hf₂, Category.id_comp]
  have hgf : g ≫ f = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hf₁, ← Category.assoc, hg₁, Category.assoc, hvu, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hf₂, hg₂, Category.id_comp]
  exact ⟨⟨f, g, hfg, hgf⟩, hf₁, hf₂, hg₁⟩

end S_ModularCurve_XOneP_exists_fibreIso_comp_fst_eq_of_modelHom_comp_modelTo_eq_of_algebraMap_smul_eq_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_fibreIso_comp_fst_eq_of_modelHom_comp_modelTo_eq_of_algebraMap_smul_eq_twoChartModel_x1_mul (solution)
