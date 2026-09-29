-- Prove2me | solution 1 for ModularCurve.XOneP.apply_eq_zero_of_mul_eq_of_map_eq_zero_of_comp_eq_specMap_comp_iotaFin_of_gaussReading_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/6585a5e0-4133-5623-8a8c-2ef95d637017

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_apply_eq_zero_of_mul_eq_of_map_eq_zero_of_comp_eq_specMap_comp_iotaFin_of_gaussReading_twoChartModel_x1_mul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

namespace GaussQEPTools

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

theorem appIso_hom_res_app_appIso_inv_apply
    {X Y : Scheme} (f : Y ⟶ X) {A B : CommRingCat} (ι : Spec A ⟶ X) [IsOpenImmersion ι]
    (g : Spec B ⟶ Y) [IsOpenImmersion g] (θ : A ⟶ B) (hfac : g ≫ f = Spec.map θ ≫ ι) (a : A)
    (V' : (Spec B).Opens) (hV' : g ''ᵁ V' ≤ f ⁻¹ᵁ (ι ''ᵁ ⊤)) :
    (g.appIso V').hom (Y.presheaf.map (homOfLE hV').op
      ((f.app (ι ''ᵁ ⊤)) ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv a)))) =
    (Spec B).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso B).inv (θ a)) := by
  let V : X.Opens := ι ''ᵁ ⊤
  let r := (Scheme.ΓSpecIso A).inv a
  show (g.appIso V').hom (Y.presheaf.map (homOfLE hV').op ((f.app V) ((ι.appIso ⊤).inv r))) = _
  have e1 := CategoryTheory.ConcreteCategory.congr_hom (g.appIso_hom V')
    (Y.presheaf.map (homOfLE hV').op ((f.app V) ((ι.appIso ⊤).inv r)))
  rw [CategoryTheory.comp_apply] at e1
  rw [e1]
  have e2 := CategoryTheory.ConcreteCategory.congr_hom (g.naturality (homOfLE hV').op) ((f.app V) ((ι.appIso ⊤).inv r))
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e2
  rw [e2]
  have e3 := CategoryTheory.ConcreteCategory.congr_hom
    ((Scheme.Hom.comp_app g f V).symm.trans ((Scheme.Hom.congr_app hfac V).trans
      (congrArg (· ≫ (Spec B).presheaf.map _) (Scheme.Hom.comp_app (Spec.map θ) ι V))))
    ((ι.appIso ⊤).inv r)
  erw [e3]
  erw [CategoryTheory.comp_apply, CategoryTheory.comp_apply]
  have e4 := CategoryTheory.ConcreteCategory.congr_hom (ι.appIso_inv_app ⊤) r
  rw [CategoryTheory.comp_apply] at e4
  erw [e4]
  have e5 := CategoryTheory.ConcreteCategory.congr_hom
    ((Spec.map θ).naturality (eqToHom (ι.preimage_image_eq ⊤)).op) r
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e5
  erw [e5]
  have e6 := CategoryTheory.ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality θ) a
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e6
  erw [← e6]
  simp only [← CategoryTheory.comp_apply]
  rfl

end GaussQEPTools

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)]
    (k : Type) [Field k] [Algebra A k]
    (C₁ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))

    (w : ModularCurve.IntegralWeightOneForm k M)
    (Mdl₁ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₁ : Mdl₁.C ≅ C₁)
    (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)
    [hne₁ : Nonempty (Scheme.Opens.toScheme ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hgauss₁ : ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
      y.map (algebraMap A k) ≠ 0 →
      ((a : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      ((Mdl₁.ffEquiv.symm
          (Mdl₁.C.germToFunctionField ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) =
        HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) / HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k)))

    (r : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A)
    (hy : y.map (algebraMap A k) ≠ 0)
    (hr : ((r : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
      HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hx : x.map (algebraMap A k) = 0)

    (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁)
    (ψ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* k)
    (hc : c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
      Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j) :
    ψ r = 0 := by
  classical

  let g₂ : Mdl₁.C ⟶ ModularCurve.TwoChartModel A (↥K) j :=
    e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)
  let V : (ModularCurve.TwoChartModel A (↥K) j).Opens := (ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤
  let U : Mdl₁.C.Opens := g₂ ⁻¹ᵁ V
  let sec : Γ(ModularCurve.TwoChartModel A (↥K) j, V) :=
    ((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
      ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv r)
  haveI : Nonempty ↥U := hne₁

  have hread := hgauss₁ r x y hy hr
  rw [hx, map_zero, zero_div] at hread
  have h0 : Mdl₁.ffEquiv.symm (Mdl₁.C.germToFunctionField U (g₂.app V sec)) = 0 := by
    rw [← ZeroMemClass.coe_eq_zero]
    exact hread
  have h1 : Mdl₁.C.germToFunctionField U (g₂.app V sec) = 0 := by
    have := congrArg Mdl₁.ffEquiv h0
    rwa [RingEquiv.apply_symm_apply, map_zero] at this
  have hsec : g₂.app V sec = 0 :=
    (Scheme.germToFunctionField_injective (X := Mdl₁.C) U) (by rw [h1, map_zero])

  let c' : Spec (CommRingCat.of k) ⟶ Mdl₁.C := c.1 ≫ e₁.inv
  have hfac : 𝟙 _ ≫ (c' ≫ g₂) = Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j := by
    rw [Category.id_comp]
    change (c.1 ≫ e₁.inv) ≫ e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = _
    rw [Category.assoc, e₁.inv_hom_id_assoc]
    exact hc
  have hV' : (𝟙 (Spec (CommRingCat.of k))) ''ᵁ ⊤ ≤ (c' ≫ g₂) ⁻¹ᵁ V := by
    intro t _
    change (c' ≫ g₂).base t ∈ (V : Set _)
    rw [← Category.id_comp (c' ≫ g₂), hfac]
    exact ⟨(Spec.map (CommRingCat.ofHom ψ)).base t, trivial, rfl⟩
  have key := GaussQEPTools.appIso_hom_res_app_appIso_inv_apply (c' ≫ g₂) (ModularCurve.TwoChart.ιFin A (↥K) j)
    (𝟙 (Spec (CommRingCat.of k))) (CommRingCat.ofHom ψ) hfac r ⊤ hV'

  have hL : (c' ≫ g₂).app V sec = 0 := by
    rw [Scheme.Hom.comp_app]
    change c'.app _ (g₂.app V sec) = 0
    rw [hsec, map_zero]
  change ((𝟙 (Spec (CommRingCat.of k)) : Spec (CommRingCat.of k) ⟶ _).appIso ⊤).hom
      ((Spec (CommRingCat.of k)).presheaf.map (homOfLE hV').op ((c' ≫ g₂).app V sec)) = _ at key
  rw [hL, map_zero, map_zero] at key

  have hid : (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of k)).Opens) ≤ ⊤)).op = 𝟙 _ := Subsingleton.elim _ _
  rw [hid, CategoryTheory.Functor.map_id] at key
  change (0 : Γ(Spec (CommRingCat.of k), ⊤)) = (Scheme.ΓSpecIso (CommRingCat.of k)).inv (ψ r) at key
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom key.symm
  rw [map_zero] at this
  rw [← this]
  exact (CategoryTheory.Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of k)) (ψ r)).symm

end S_ModularCurve_XOneP_apply_eq_zero_of_mul_eq_of_map_eq_zero_of_comp_eq_specMap_comp_iotaFin_of_gaussReading_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_apply_eq_zero_of_mul_eq_of_map_eq_zero_of_comp_eq_specMap_comp_iotaFin_of_gaussReading_twoChartModel_x1_mul (solution)
