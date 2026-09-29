-- Prove2me | solution 1 for ModularCurve.XOneP.genericPoint_specializes_crossing_and_baseChange_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/2d394792-1d3b-540b-b812-790d4933c592

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_ModularCurve_DRModelPackageCrossingFrame
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_genericPoint_specializes_crossing_and_baseChange_twoChartModel_x1_mul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

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
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ρO : A →+* O) (ϖ : O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ})
    (toκ : O →+* k) (htoκ : toκ.comp ρO = algebraMap A k)

    (bc : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ))
    [IsIntegral C₁] [IsIntegral C₂] (ν : ↥(pullback i₁.1 i₂.1)) :
    ((i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (genericPoint C₁) ⤳ (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ν) ∧
    ((i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (genericPoint C₂) ⤳ (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ν) ∧
    ((i₁.1 ≫ bc).base (genericPoint C₁) ⤳ (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base ν) ∧
    ((i₂.1 ≫ bc).base (genericPoint C₂) ⤳ (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base ν) := by
  have hcond : pullback.fst i₁.1 i₂.1 ≫ i₁.1 = pullback.snd i₁.1 i₂.1 ≫ i₂.1 := pullback.condition

  have h1 : ((i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (genericPoint C₁)) ⤳
      ((i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ((pullback.fst i₁.1 i₂.1).base ν)) :=
    (genericPoint_specializes _).map (i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base.hom.continuous
  have h2 : ((i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (genericPoint C₂)) ⤳
      ((i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ((pullback.snd i₁.1 i₂.1).base ν)) :=
    (genericPoint_specializes _).map (i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base.hom.continuous
  have h3 : ((i₁.1 ≫ bc).base (genericPoint C₁)) ⤳ ((i₁.1 ≫ bc).base ((pullback.fst i₁.1 i₂.1).base ν)) :=
    (genericPoint_specializes _).map (i₁.1 ≫ bc).base.hom.continuous
  have h4 : ((i₂.1 ≫ bc).base (genericPoint C₂)) ⤳ ((i₂.1 ≫ bc).base ((pullback.snd i₁.1 i₂.1).base ν)) :=
    (genericPoint_specializes _).map (i₂.1 ≫ bc).base.hom.continuous
  have e1 : (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ν =
      (i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ((pullback.fst i₁.1 i₂.1).base ν) := by
    simp only [Scheme.Hom.comp_base, TopCat.comp_app]
  have e2 : (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ν =
      (i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ((pullback.snd i₁.1 i₂.1).base ν) := by
    rw [← Category.assoc, hcond]
    simp only [Scheme.Hom.comp_base, TopCat.comp_app]
  have e3 : (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base ν = (i₁.1 ≫ bc).base ((pullback.fst i₁.1 i₂.1).base ν) := by
    simp only [Scheme.Hom.comp_base, TopCat.comp_app]
  have e4 : (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base ν = (i₂.1 ≫ bc).base ((pullback.snd i₁.1 i₂.1).base ν) := by
    rw [← Category.assoc, hcond]
    simp only [Scheme.Hom.comp_base, TopCat.comp_app]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1]; exact h1
  · rw [e2]; exact h2
  · rw [e3]; exact h3
  · rw [e4]; exact h4

end S_ModularCurve_XOneP_genericPoint_specializes_crossing_and_baseChange_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_genericPoint_specializes_crossing_and_baseChange_twoChartModel_x1_mul (solution)
