-- Prove2me | solution 1 for MazurTransfer.Order13PublicFiniteChartParameters.parameter_product
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T06:59:38.176854+00:00
-- url     : https://prove2.me/submissions/43ae00a4-93b6-47ea-8810-05807ca6ee8b

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the two specified actual curve parameters multiply to one after restriction to the actual first/inverse chart intersection.
Named downstream consumer: res_f_mul_res_g in unchanged original integral FiniteMapData. Uses checked literal parameter pullbacks and the Proved public actual chart intersection. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13FirstFiniteChartSections
import Definitions.Def_MazurTransfer_Order13FirstFiniteChartCanonicalOpen
import Definitions.Def_MazurTransfer_Order13InverseFiniteChartSections
import Theorems.Thm_MazurTransfer_Order13InverseParameterFiniteAlgebra_actual_chart_intersection_opensRange
import Theorems.Thm_MazurTransfer_ActualAffineSectionRingRestrictionTransport_transportedSection_pullback
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped MazurTransfer.Order13SingleSectionFiniteAlgebra
open MazurTorsion.XOneThirteenAffineCurve MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer MazurTransfer.Order13InverseParameterFiniteAlgebra
open MazurTransfer.Order13ActualPositiveInfinityComplement
namespace ActualParameterReciprocityPublicProof20261017
variable {X : Scheme.{u}} (U : X.Opens)
theorem appLE_injective_of_image_top {Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (hImage : j ''ᵁ ⊤ = U) (h : ⊤ ≤ j ⁻¹ᵁ U) :
    Function.Injective (j.appLE U ⊤ h) := by
  let e : Γ(X, U) ≅ Γ(Y, ⊤) :=
    X.presheaf.mapIso (eqToIso hImage).op ≪≫ j.appIso ⊤
  have he : e.hom = j.appLE U ⊤ h := by
    change X.presheaf.map (eqToHom hImage).op ≫ (j.appIso ⊤).hom = _
    rw [Scheme.Hom.appIso_hom']
    exact j.map_appLE' h hImage
  rw [← he]
  exact e.commRingCatIsoToRingEquiv.injective
end ActualParameterReciprocityPublicProof20261017

theorem solution (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (h104 : IsUnit (104 : R)) :
    ((curveScheme R).presheaf.map (homOfLE (inf_le_left :
      Order13FirstFiniteChartFromPublicTheorem.chartOpen R ⊓ inverseChartOpen R ≤ Order13FirstFiniteChartFromPublicTheorem.chartOpen R)).op)
      (Order13FirstFiniteChartFromPublicTheorem.parameterSection R h104) *
    ((curveScheme R).presheaf.map (homOfLE (inf_le_right :
      Order13FirstFiniteChartFromPublicTheorem.chartOpen R ⊓ inverseChartOpen R ≤ inverseChartOpen R)).op)
      (Order13InverseFiniteChartFromPublicTheorems.parameterSection R h104) = 1 := by
  let Ω := MazurTransfer.Order13SingleSectionFiniteAlgebra.ordinaryParameterLocalization R
  let j := ordinaryParameterCurveMap R
  let U := Order13FirstFiniteChartFromPublicTheorem.chartOpen R
  let V := inverseChartOpen R
  let W := U ⊓ V
  have hInter : U ⊓ V = (ordinaryParameterCurveMap R).opensRange := by
    exact actual_chart_intersection_opensRange R h104
  have hW : ⊤ ≤ j ⁻¹ᵁ W := by
    intro p hp
    change ordinaryParameterCurveMap R p ∈ Order13FirstFiniteChartFromPublicTheorem.chartOpen R ⊓ inverseChartOpen R
    rw [hInter]
    exact ⟨p, rfl⟩
  have hU : ⊤ ≤ j ⁻¹ᵁ U := fun p hp => (hW hp).1
  have hV : ⊤ ≤ j ⁻¹ᵁ V := fun p hp => (hW hp).2
  let φ : Order13SingleSectionFiniteAlgebra.candidateAlgebra R →+* Ω :=
    (algebraMap (CoordinateRing R) Ω).comp
      (Order13SingleSectionFiniteAlgebra.candidateAlgebra R).val.toRingHom
  have hfScheme : Spec.map (CommRingCat.ofHom φ) ≫
      (Order13FirstFiniteChartFromPublicTheorem.specIso R h104).hom ≫ U.ι = j := by
    have hφ : Spec.map (CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing R) Ω)) ≫
          Spec.map (CommRingCat.ofHom
            (Order13SingleSectionFiniteAlgebra.candidateAlgebra R).val.toRingHom) := by
      rw [← Spec.map_comp]
      rfl
    rw [hφ, Category.assoc, Order13FirstFiniteChartFromPublicTheorem.specIso_ordinary]
    rfl
  have hf := ActualAffineSectionRingRestrictionTransport.transportedSection_pullback U
    (Order13FirstFiniteChartFromPublicTheorem.specIso R h104) φ
    (Order13FirstFiniteChartFromPublicTheorem.parameterElement R)
    (show ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫
      (Order13FirstFiniteChartFromPublicTheorem.specIso R h104).hom ≫ U.ι) ⁻¹ᵁ U by
      simpa only [hfScheme] using hU)
  change (Scheme.ΓSpecIso (.of Ω)).hom
      ((Spec.map (CommRingCat.ofHom φ) ≫
        (Order13FirstFiniteChartFromPublicTheorem.specIso R h104).hom ≫ U.ι).appLE U ⊤ _
        (Order13FirstFiniteChartFromPublicTheorem.parameterSection R h104)) =
    algebraMap (CoordinateRing R) Ω
      (Order13FirstFiniteChartFromPublicTheorem.parameterElement R : CoordinateRing R) at hf
  have hf' : (Scheme.ΓSpecIso (.of Ω)).hom
      ((j.appLE U ⊤ hU) (Order13FirstFiniteChartFromPublicTheorem.parameterSection R h104)) =
      algebraMap (CoordinateRing R) Ω (Order13SingleSectionFiniteMapIdentities.t R) := by
    simpa only [hfScheme, Order13FirstFiniteChartFromPublicTheorem.parameterElement_value] using hf
  have hg : (Scheme.ΓSpecIso (.of Ω)).hom
      ((j.appLE V ⊤ hV) (Order13InverseFiniteChartFromPublicTheorems.parameterSection R h104)) =
      Order13InverseParameterPolynomialIdentities.s R := by
    exact Order13InverseFiniteChartFromPublicTheorems.parameterSection_ordinary_pullback R h104
  have hImage : j ''ᵁ ⊤ = W :=
    j.image_top_eq_opensRange.trans hInter.symm
  apply ActualParameterReciprocityPublicProof20261017.appLE_injective_of_image_top W j hImage hW
  apply (Scheme.ΓSpecIso (.of Ω)).commRingCatIsoToRingEquiv.injective
  have hresU := j.map_appLE hW (homOfLE (inf_le_left : W ≤ U)).op
  have hresV := j.map_appLE hW (homOfLE (inf_le_right : W ≤ V)).op
  simp only [map_mul, map_one]
  rw [← CommRingCat.comp_apply, hresU, ← CommRingCat.comp_apply, hresV]
  change (Scheme.ΓSpecIso (.of Ω)).hom
      ((j.appLE U ⊤ hU) (Order13FirstFiniteChartFromPublicTheorem.parameterSection R h104)) *
    (Scheme.ΓSpecIso (.of Ω)).hom
      ((j.appLE V ⊤ hV) (Order13InverseFiniteChartFromPublicTheorems.parameterSection R h104)) = 1
  rw [hf', hg]
  exact IsLocalization.Away.mul_invSelf (Order13SingleSectionFiniteMapIdentities.t R)
#print axioms solution
