-- Prove2me | solution 1 for ModularCurve.XOneP.exists_galoisModelHom_comp_modelTo_eq_and_iotaFin_comp_eq_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/da0483a2-2ca0-586f-9592-d0c0fe92aaa3

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_hom_comp_toBase_eq_and_iotaFin_comp_eq_of_mulSemiringAction_of_smul_eq
import Theorems.Thm_ModularCurve_TwoChart_exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo
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

namespace P2MW.S_ModularCurve_XOneP_exists_galoisModelHom_comp_modelTo_eq_and_iotaFin_comp_eq_twoChartModel_x1_mul

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

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))
    :
    ∃ (wX : (L ≃ₐ[ℚ] L) → (ModularCurve.TwoChartModel A (↥K) j ⟶ ModularCurve.TwoChartModel A (↥K) j))
      (ρX : (L ≃ₐ[ℚ] L) → (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ≃+* ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)))
      (ρX' : (L ≃ₐ[ℚ] L) → (↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j) ≃+* ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j))),

      (∀ s : L ≃ₐ[ℚ] L, wX s ≫ (ModularCurve.TwoChart.modelTo A (↥K) j) =
        (ModularCurve.TwoChart.modelTo A (↥K) j) ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)))) ∧

      wX 1 = 𝟙 (ModularCurve.TwoChartModel A (↥K) j) ∧
      (∀ s s' : L ≃ₐ[ℚ] L, wX (s * s') = wX s ≫ wX s') ∧

      (∀ (s : L ≃ₐ[ℚ] L) (b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)),
        (((ρX s b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) =
          ModularCurve.coeffMap (s.toAlgHom.toRingHom) (((b : ↥K)) : LaurentSeries L)) ∧
      (∀ (s : L ≃ₐ[ℚ] L) (b : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j)),
        (((ρX' s b : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j)) : ↥K) : LaurentSeries L) =
          ModularCurve.coeffMap (s.toAlgHom.toRingHom) (((b : ↥K)) : LaurentSeries L)) ∧

      (∀ s : L ≃ₐ[ℚ] L, ModularCurve.TwoChart.ιFin A (↥K) j ≫ wX s = Spec.map (CommRingCat.ofHom (ρX s).toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j) ∧
      (∀ s : L ≃ₐ[ℚ] L, ModularCurve.TwoChart.ιInf A (↥K) j ≫ wX s = Spec.map (CommRingCat.ofHom (ρX' s).toRingHom) ≫ ModularCurve.TwoChart.ιInf A (↥K) j) ∧
      (∀ s : L ≃ₐ[ℚ] L, (wX s) ⁻¹ᵁ (ModularCurve.TwoChart.ιFin A (↥K) j).opensRange = (ModularCurve.TwoChart.ιFin A (↥K) j).opensRange) := by
  classical
  subst hK

  letI act : MulSemiringAction (L ≃ₐ[ℚ] L) ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) := MulSemiringAction.compHom ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) (ModularCurve.arithmeticGalois (ModularCurve.x1FunctionField (M * p)))
  have hsmul : ∀ (s : L ≃ₐ[ℚ] L) (x : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))), ((s • x : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L) = ModularCurve.coeffMap (s : L →+* L) (x : LaurentSeries L) :=
    fun s x => ModularCurve.coe_arithmeticGalois_smul (ModularCurve.x1FunctionField (M * p)) s x
  have hsmul' : ∀ (s : L ≃ₐ[ℚ] L) (x : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))), (s • x : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) = ModularCurve.arithmeticRingAut (ModularCurve.x1FunctionField (M * p)) s x :=
    fun s x => Subtype.ext (by rw [hsmul, ModularCurve.coe_arithmeticRingAut_apply])

  have hΓF : ∀ (s : L ≃ₐ[ℚ] L) (r : A), s • algebraMap A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) r = algebraMap A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) (s • r) := by
    intro s r
    calc s • algebraMap A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) r = ModularCurve.arithmeticRingAut (ModularCurve.x1FunctionField (M * p)) s (algebraMap L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) (algebraMap A L r)) := by
            rw [hsmul', IsScalarTower.algebraMap_apply A L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) r]
      _ = algebraMap L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) (s (algebraMap A L r)) := ModularCurve.arithmeticRingAut_algebraMap (ModularCurve.x1FunctionField (M * p)) s _
      _ = algebraMap A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) (s • r) := by rw [← hΓA, ← IsScalarTower.algebraMap_apply A L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))]

  have hΓj : ∀ s : L ≃ₐ[ℚ] L, s • j = j := by
    intro s
    apply Subtype.ext
    rw [hsmul]
    have hj' : ((j : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L) = ModularCurve.coeffEmb L ModularCurve.jq := hj
    rw [hj']
    exact ModularCurve.coeffMap_coeffEmb (L := L) s ModularCurve.jq

  obtain ⟨w, θ, θ', hw_over, hw_one, hw_mul, hθ, hθ', hwθ, hwθ', hwU⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_hom_comp_toBase_eq_and_iotaFin_comp_eq_of_mulSemiringAction_of_smul_eq
      A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j (L ≃ₐ[ℚ] L) hΓF hΓj
  obtain ⟨e, he, heFin, heInf⟩ := ModularCurve.TwoChart.exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j
  have he' : e.inv ≫ ModularCurve.TwoChart.modelTo A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j = AlgebraicCurve.TwoChartIntegralModel.toBase A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j := by
    rw [← he, e.inv_hom_id_assoc]
  have heFin' : AlgebraicCurve.TwoChartIntegralModel.ιFin A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j ≫ e.inv = ModularCurve.TwoChart.ιFin A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j := by
    rw [← heFin]
    erw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have heInf' : AlgebraicCurve.TwoChartIntegralModel.ιInf A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j ≫ e.inv = ModularCurve.TwoChart.ιInf A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j := by
    rw [← heInf]
    erw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hcoe : ∀ s : L ≃ₐ[ℚ] L, (s : L →+* L) = s.toAlgHom.toRingHom := fun s => RingHom.ext fun _ => rfl
  refine ⟨fun s => e.hom ≫ w s ≫ e.inv, θ, θ', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    show (e.hom ≫ w s ≫ e.inv) ≫ _ = _
    rw [Category.assoc, Category.assoc, he', hw_over, ← Category.assoc, he]
  · show e.hom ≫ w 1 ≫ e.inv = 𝟙 _
    rw [hw_one, Category.id_comp, e.hom_inv_id]
  · intro s s'
    show e.hom ≫ w (s * s') ≫ e.inv = (e.hom ≫ w s ≫ e.inv) ≫ (e.hom ≫ w s' ≫ e.inv)
    rw [hw_mul]
    simp only [Category.assoc, e.inv_hom_id_assoc]
  · intro s b
    exact (congrArg (fun x : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) => (x : LaurentSeries L)) (hθ s b)).trans ((hsmul s _).trans (by rw [hcoe]))
  · intro s b
    exact (congrArg (fun x : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) => (x : LaurentSeries L)) (hθ' s b)).trans ((hsmul s _).trans (by rw [hcoe]))
  · intro s
    have key : ((ModularCurve.TwoChart.ιFin A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j ≫ e.hom) ≫ w s) ≫ e.inv = Spec.map (CommRingCat.ofHom (θ s).toRingHom) ≫ ModularCurve.TwoChart.ιFin A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j := by
      rw [heFin]
      erw [hwθ]
      erw [Category.assoc]
      erw [heFin']
      rfl
    simp only [Category.assoc] at key
    exact key
  · intro s
    have key : ((ModularCurve.TwoChart.ιInf A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j ≫ e.hom) ≫ w s) ≫ e.inv = Spec.map (CommRingCat.ofHom (θ' s).toRingHom) ≫ ModularCurve.TwoChart.ιInf A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j := by
      rw [heInf]
      erw [hwθ']
      erw [Category.assoc]
      erw [heInf']
      rfl
    simp only [Category.assoc] at key
    exact key
  · intro s
    show (e.hom ≫ w s ≫ e.inv) ⁻¹ᵁ _ = _

    have h2 : e.inv ⁻¹ᵁ (ModularCurve.TwoChart.ιFin A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j).opensRange = (AlgebraicCurve.TwoChartIntegralModel.ιFin A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j).opensRange := by
      have : (ModularCurve.TwoChart.ιFin A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j).opensRange = e.inv ''ᵁ (AlgebraicCurve.TwoChartIntegralModel.ιFin A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) j).opensRange := by
        rw [← Scheme.Hom.opensRange_comp]
        congr 1
        exact heFin'.symm
      rw [this, Scheme.Hom.preimage_image_eq]
    rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, h2, hwU, ← h2, ← Scheme.Hom.comp_preimage, Iso.hom_inv_id]
    simp

end S_ModularCurve_XOneP_exists_galoisModelHom_comp_modelTo_eq_and_iotaFin_comp_eq_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_galoisModelHom_comp_modelTo_eq_and_iotaFin_comp_eq_twoChartModel_x1_mul (solution)
