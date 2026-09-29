-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.exists_ringHom_functionField_pullback_forall_eq_algebraMap_and_coe_eq_coeffEmb
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/2857e14d-0612-5259-832e-7af1a92e4e0d

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_ModularCurve_DRResolvedModelChartsLevelRam
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_exists_ringHom_functionField_pullback_forall_eq_algebraMap_and_coe_eq_coeffEmb

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open IsLocalRing ModularCurve.PlaceSpecialization MvPolynomial MvPolynomial.CrossingQuotient

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

noncomputable section

universe u

private theorem c1L_germ_app_app_eq_of_comp_eq {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z} (e : f ≫ g = k)
    (W : Z.Opens) (x : X) (hx : x ∈ f ⁻¹ᵁ (g ⁻¹ᵁ W)) (hx' : x ∈ k ⁻¹ᵁ W) (t : Γ(Z, W)) :
    (X.presheaf.germ (f ⁻¹ᵁ (g ⁻¹ᵁ W)) x hx).hom ((f.app (g ⁻¹ᵁ W)).hom ((g.app W).hom t)) =
      (X.presheaf.germ (k ⁻¹ᵁ W) x hx').hom ((k.app W).hom t) := by
  subst e; rfl

section
variable (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
  (O : Type) [CommRing O] (ρO : DRLevel.R q →+* O)
  (τ : O →+* AlgebraicClosure ℚ) (hτ : τ.comp ρO = algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))

private abbrev c1L_XO : Scheme.{0} := pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))

private def c1L_g : pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) (AlgebraicClosure ℚ)))) ⟶ c1L_XO N₀ q O ρO :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom τ)) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hτ])

private theorem c1L_range_g : Set.range (c1L_g N₀ q O ρO τ hτ) =
    (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹' Set.range (𝟙 (DRLevel.X N₀ q)) ∩
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹' Set.range (Spec.map (CommRingCat.ofHom τ)) := by
  unfold c1L_g
  exact Scheme.Pullback.range_map _ _ _ _ _ _ _ _ _

private def c1L_h : 𝔓.Meta.C ⟶ c1L_XO N₀ q O ρO := 𝔓.eeta ≫ c1L_g N₀ q O ρO τ hτ

private theorem c1L_h_fst : c1L_h N₀ q hqN 𝔓 O ρO τ hτ ≫ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) =
    𝔓.eeta ≫ (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))))) := by
  simp only [c1L_h, c1L_g, Category.assoc, pullback.lift_fst, Category.comp_id]

private theorem c1L_h_snd : c1L_h N₀ q hqN 𝔓 O ρO τ hτ ≫ (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) =
    𝔓.Meta.toBase ≫ Spec.map (CommRingCat.ofHom τ) := by
  simp only [c1L_h, c1L_g, Category.assoc, pullback.lift_snd]
  rw [← Category.assoc, 𝔓.heeta]

end

section
variable (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
  (O : Type) [CommRing O] [IsDomain O] (ρO : DRLevel.R q →+* O)
  (τ : O →+* AlgebraicClosure ℚ) (hτ : τ.comp ρO = algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))
  (hτi : Function.Injective τ)

include 𝔓 in

private theorem c1L_snd_genericPoint [IsIntegral (c1L_XO N₀ q O ρO)] :
    (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).base (genericPoint (c1L_XO N₀ q O ρO)) =
      genericPoint (Spec (CommRingCat.of O)) := by
  haveI : Flat (DRLevel.toBase N₀ q) := 𝔓.flat
  have hgen : GeneralizingMap (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).base :=
    Flat.generalizingMap _
  obtain ⟨x', hx', hπx'⟩ := hgen (genericPoint_specializes
    ((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).base (genericPoint (c1L_XO N₀ q O ρO))) :
    genericPoint (Spec (CommRingCat.of O)) ⤳
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).base (genericPoint (c1L_XO N₀ q O ρO)))
  have : x' = genericPoint (c1L_XO N₀ q O ρO) := (hx'.antisymm (genericPoint_specializes x')).eq
  rw [← this]
  exact hπx'

include hτi in

private theorem c1L_genericPoint_mem_range_h [IsIntegral (c1L_XO N₀ q O ρO)] :
    genericPoint (c1L_XO N₀ q O ρO) ∈ Set.range (c1L_h N₀ q hqN 𝔓 O ρO τ hτ).base := by
  have hmem : genericPoint (c1L_XO N₀ q O ρO) ∈ Set.range (c1L_g N₀ q O ρO τ hτ) := by
    rw [c1L_range_g]
    refine ⟨⟨_, rfl⟩, ?_⟩
    show (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).base (genericPoint (c1L_XO N₀ q O ρO)) ∈
      Set.range (Spec.map (CommRingCat.ofHom τ))
    rw [c1L_snd_genericPoint N₀ q hqN 𝔓 O ρO, genericPoint_eq_bot_of_affine]
    refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (AlgebraicClosure ℚ)), ?_⟩
    rw [Spec.map_apply]
    apply PrimeSpectrum.ext
    rw [PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom]
    exact Ideal.comap_bot_of_injective τ hτi
  obtain ⟨z, hz⟩ := hmem
  haveI : IsIso 𝔓.eeta := 𝔓.eeta_iso
  obtain ⟨m, rfl⟩ := (inferInstance : Surjective 𝔓.eeta).surj z
  exact ⟨m, by rw [← hz, c1L_h, Scheme.Hom.comp_base]; rfl⟩

include hτi in

private theorem c1L_h_genericPoint [IsIntegral (c1L_XO N₀ q O ρO)] :
    (c1L_h N₀ q hqN 𝔓 O ρO τ hτ).base (genericPoint 𝔓.Meta.C) = genericPoint (c1L_XO N₀ q O ρO) := by
  obtain ⟨m, hm⟩ := c1L_genericPoint_mem_range_h N₀ q hqN 𝔓 O ρO τ hτ hτi
  have h1 : (c1L_h N₀ q hqN 𝔓 O ρO τ hτ).base (genericPoint 𝔓.Meta.C) ⤳ genericPoint (c1L_XO N₀ q O ρO) := by
    rw [← hm]
    exact (genericPoint_specializes m).map (c1L_h N₀ q hqN 𝔓 O ρO τ hτ).base.hom.continuous
  exact (h1.antisymm (genericPoint_specializes _)).eq

private def c1L_φ0Hom [IsIntegral (c1L_XO N₀ q O ρO)] : (c1L_XO N₀ q O ρO).functionField ⟶ 𝔓.Meta.C.functionField :=
  (c1L_XO N₀ q O ρO).presheaf.stalkSpecializes (specializes_of_eq (c1L_h_genericPoint N₀ q hqN 𝔓 O ρO τ hτ hτi)) ≫
    (c1L_h N₀ q hqN 𝔓 O ρO τ hτ).stalkMap (genericPoint 𝔓.Meta.C)

private theorem c1L_germ_φ0Hom [IsIntegral (c1L_XO N₀ q O ρO)] (U : (c1L_XO N₀ q O ρO).Opens) (hU : genericPoint (c1L_XO N₀ q O ρO) ∈ U) :
    (c1L_XO N₀ q O ρO).presheaf.germ U (genericPoint (c1L_XO N₀ q O ρO)) hU ≫ c1L_φ0Hom N₀ q hqN 𝔓 O ρO τ hτ hτi =
      (c1L_h N₀ q hqN 𝔓 O ρO τ hτ).app U ≫ 𝔓.Meta.C.presheaf.germ ((c1L_h N₀ q hqN 𝔓 O ρO τ hτ) ⁻¹ᵁ U) (genericPoint 𝔓.Meta.C)
        (show (c1L_h N₀ q hqN 𝔓 O ρO τ hτ).base (genericPoint 𝔓.Meta.C) ∈ U by
          rw [c1L_h_genericPoint N₀ q hqN 𝔓 O ρO τ hτ hτi]; exact hU) := by
  rw [c1L_φ0Hom, ← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes, Scheme.Hom.germ_stalkMap]

private theorem c1L_φ0Hom_germ [IsIntegral (c1L_XO N₀ q O ρO)] (U : (c1L_XO N₀ q O ρO).Opens) (hU : genericPoint (c1L_XO N₀ q O ρO) ∈ U)
    (s : Γ(c1L_XO N₀ q O ρO, U)) :
    (c1L_φ0Hom N₀ q hqN 𝔓 O ρO τ hτ hτi).hom (((c1L_XO N₀ q O ρO).presheaf.germ U (genericPoint (c1L_XO N₀ q O ρO)) hU).hom s) =
      (𝔓.Meta.C.presheaf.germ ((c1L_h N₀ q hqN 𝔓 O ρO τ hτ) ⁻¹ᵁ U) (genericPoint 𝔓.Meta.C)
        (show (c1L_h N₀ q hqN 𝔓 O ρO τ hτ).base (genericPoint 𝔓.Meta.C) ∈ U by
          rw [c1L_h_genericPoint N₀ q hqN 𝔓 O ρO τ hτ hτi]; exact hU)).hom
        (((c1L_h N₀ q hqN 𝔓 O ρO τ hτ).app U).hom s) := by
  have e := RingHom.congr_fun (congrArg CommRingCat.Hom.hom (c1L_germ_φ0Hom N₀ q hqN 𝔓 O ρO τ hτ hτi U hU)) s
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using e

private def c1L_φ [IsIntegral (c1L_XO N₀ q O ρO)] : ↥((c1L_XO N₀ q O ρO).functionField) →+* ↥(modularFunctionFieldBar (N₀ * q)) :=
  𝔓.Meta.ffEquiv.symm.toRingHom.comp (c1L_φ0Hom N₀ q hqN 𝔓 O ρO τ hτ hτi).hom

private theorem c1L_φ_apply [IsIntegral (c1L_XO N₀ q O ρO)] (f : ↥((c1L_XO N₀ q O ρO).functionField)) :
    c1L_φ N₀ q hqN 𝔓 O ρO τ hτ hτi f = 𝔓.Meta.ffEquiv.symm ((c1L_φ0Hom N₀ q hqN 𝔓 O ρO τ hτ hτi).hom f) := rfl

private theorem c1L_pin2 [IsIntegral (c1L_XO N₀ q O ρO)]
    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)))]
    (a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) :
    ((c1L_φ N₀ q hqN 𝔓 O ρO τ hτ hτi ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).germToFunctionField ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤))
        (((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom
          (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a)))) : ↥(modularFunctionFieldBar (N₀ * q))) :
        LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) := by
  rw [c1L_φ_apply, ← 𝔓.Meta_pin a]
  congr 2

  rw [Scheme.germToFunctionField, c1L_φ0Hom_germ]
  exact c1L_germ_app_app_eq_of_comp_eq (c1L_h_fst N₀ q hqN 𝔓 O ρO τ hτ) _ _ _ _ _

private theorem c1L_pin1 [IsIntegral (c1L_XO N₀ q O ρO)] (x : ↥(pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))) (a : O) :
    c1L_φ N₀ q hqN 𝔓 O ρO τ hτ hτi (algebraMap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk x) _
      (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ ⊤ x trivial).hom
        (((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)) (τ a) := by
  rw [c1L_φ_apply]

  have e0 : algebraMap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk x) ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField)
      (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ ⊤ x trivial).hom
        (((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a))) =
      ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ ⊤ (genericPoint (c1L_XO N₀ q O ρO)) trivial).hom
        (((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)) := by
    change ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes ((genericPoint_spec (c1L_XO N₀ q O ρO)).specializes trivial)).hom _ = _
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, TopCat.Presheaf.germ_stalkSpecializes]
  rw [e0, c1L_φ0Hom_germ]

  have e1 : ((c1L_h N₀ q hqN 𝔓 O ρO τ hτ).app ⊤).hom (((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)) =
      (𝔓.Meta.toBase.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).inv (τ a)) := by
    have e2 : ((c1L_h N₀ q hqN 𝔓 O ρO τ hτ).app ⊤).hom (((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)) =
        ((c1L_h N₀ q hqN 𝔓 O ρO τ hτ ≫ (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a) := by
      rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
      rfl
    rw [e2, c1L_h_snd, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    congr 1
    have e3 := RingHom.congr_fun (congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom τ))) a
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e3
    exact e3.symm
  rw [e1]

  have e4 : (𝔓.Meta.C.presheaf.germ ((c1L_h N₀ q hqN 𝔓 O ρO τ hτ) ⁻¹ᵁ ⊤) (genericPoint 𝔓.Meta.C)
        (show (c1L_h N₀ q hqN 𝔓 O ρO τ hτ).base (genericPoint 𝔓.Meta.C) ∈ (⊤ : (c1L_XO N₀ q O ρO).Opens) by
          rw [c1L_h_genericPoint N₀ q hqN 𝔓 O ρO τ hτ hτi]; exact trivial)).hom
      ((𝔓.Meta.toBase.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).inv (τ a))) =
      baseToFunctionField 𝔓.Meta.toBase (τ a) := rfl
  rw [e4, ← 𝔓.Meta.ffEquiv_algebraMap, RingEquiv.symm_apply_apply]

end

end

theorem solution

    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q)
    (ρ : DRLevel.R q →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))

    (𝔓 : DRModelPackageLevel N₀ q hqN)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (ρO : DRLevel.R q →+* O)
    (hρO : ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
        (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))).comp ρO =
      algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))
    [hint : IsIntegral (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))]
    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)))] :
    ∃ φ : ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) →+* ↥(modularFunctionFieldBar (N₀ * q)),
      (∀ (x : ↥(pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))) (a : O),
        φ (algebraMap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk x) _
          (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ ⊤ x trivial).hom
            (((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)) (((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))) a)) ∧
      (∀ a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q),
        ((φ ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).germToFunctionField ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤))
            (((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom
              (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a)))) : ↥(modularFunctionFieldBar (N₀ * q))) :
            LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ)) := by
  refine ⟨c1L_φ N₀ q hqN 𝔓 O ρO _ hρO ?_, fun x a => c1L_pin1 N₀ q hqN 𝔓 O ρO _ hρO _ x a,
    fun a => c1L_pin2 N₀ q hqN 𝔓 O ρO _ hρO _ a⟩

  intro x y hxy
  simp only [RingHom.comp_apply] at hxy
  exact eO.injective (Subtype.ext ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).injective hxy))

end S_ModularCurve_DRModelPackageLevel_exists_ringHom_functionField_pullback_forall_eq_algebraMap_and_coe_eq_coeffEmb
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_exists_ringHom_functionField_pullback_forall_eq_algebraMap_and_coe_eq_coeffEmb (solution)
