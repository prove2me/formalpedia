-- Prove2me | solution 1 for ModularCurve.XOneP.exists_fin_hom_pullback_comp_eq_id_and_injective_base_closedPoint_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/d0dc1c38-44e6-5e99-9603-83c41bf5a87c

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
import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_fin_hom_pullback_comp_eq_id_and_injective_base_closedPoint_twoChartModel_x1_mul

set_option autoImplicit false

p2m_open "MvPolynomial CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

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
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n) :
    ∃ z : Fin n → (Spec (CommRingCat.of k) ⟶ pullback i₁.1 i₂.1),
      (∀ i, (z i ≫ pullback.fst i₁.1 i₂.1) ≫ c₁ = 𝟙 _) ∧ (∀ i, (z i ≫ pullback.snd i₁.1 i₂.1) ≫ c₂ = 𝟙 _) ∧
      Function.Injective fun i => (z i).base (IsLocalRing.closedPoint k) := by
  classical

  let g : pullback i₁.1 i₂.1 ⟶ Spec (CommRingCat.of k) := pullback.fst i₁.1 i₂.1 ≫ c₁
  haveI : LocallyOfFiniteType g := inferInstance
  haveI : JacobsonSpace ↥(pullback i₁.1 i₂.1) := LocallyOfFiniteType.jacobsonSpace g
  haveI : Finite ↥(pullback i₁.1 i₂.1) := Nat.finite_of_card_ne_zero (by rw [hn]; exact hn0.ne')
  have pt : ∀ x : ↥(pullback i₁.1 i₂.1), ∃ t : Spec (CommRingCat.of k) ⟶ pullback i₁.1 i₂.1,
      t ≫ g = 𝟙 _ ∧ t.base (IsLocalRing.closedPoint k) = x := fun x =>
    ⟨pointOfClosedPoint g x (isClosed_discrete _), pointOfClosedPoint_comp g x (isClosed_discrete _),
      pointOfClosedPoint_apply g x (isClosed_discrete _) _⟩
  choose t ht htx using pt

  have hi₁ : i₁.1 ≫ baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k = c₁ := i₁.2
  have hi₂ : i₂.1 ≫ baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k = c₂ := i₂.2
  have hg₂ : pullback.snd i₁.1 i₂.1 ≫ c₂ = g :=
    calc pullback.snd i₁.1 i₂.1 ≫ c₂ = pullback.snd i₁.1 i₂.1 ≫ i₂.1 ≫ baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k := by rw [hi₂]
      _ = pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k := by
          rw [← Category.assoc, ← pullback.condition, Category.assoc]
      _ = pullback.fst i₁.1 i₂.1 ≫ c₁ := by rw [hi₁]

  let e : ↥(pullback i₁.1 i₂.1) ≃ Fin n := (Finite.equivFin _).trans (finCongr hn)
  refine ⟨fun i => t (e.symm i), fun i => ?_, fun i => ?_, ?_⟩
  · rw [Category.assoc]; exact ht _
  · rw [Category.assoc, hg₂]; exact ht _
  · intro i i' h
    apply e.symm.injective
    simpa only [htx] using h

end S_ModularCurve_XOneP_exists_fin_hom_pullback_comp_eq_id_and_injective_base_closedPoint_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_fin_hom_pullback_comp_eq_id_and_injective_base_closedPoint_twoChartModel_x1_mul (solution)
