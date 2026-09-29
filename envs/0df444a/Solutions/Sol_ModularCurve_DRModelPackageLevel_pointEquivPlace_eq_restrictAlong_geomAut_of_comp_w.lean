-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.pointEquivPlace_eq_restrictAlong_geomAut_of_comp_w
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/2fbeabac-97b0-5556-98d0-34765faabde6

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_GeometricBaseChange

import Theorems.Thm_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlg_chartRing
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_hom_pointEquivPlace_restrict_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_pointEquivPlace_eq_restrictAlong_geomAut_of_comp_w
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_pointEquivPlace_eq_restrictAlong_geomAut_of_comp_w.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicCurve"

open Topology
open scoped TensorProduct

universe u

noncomputable section

namespace GenRestr

section FieldMap

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

theorem apply_genericPoint_eq (f : X ⟶ Y) [Flat f] : f.base (genericPoint X) = genericPoint Y := by
  obtain ⟨a, ha, hfa⟩ := Flat.generalizingMap f (genericPoint_specializes (f.base (genericPoint X)))
  have hgen : IsGenericPoint a (Set.univ : Set X) := by
    rw [isGenericPoint_iff_specializes]
    intro y
    simp only [Set.mem_univ, iff_true]
    exact ha.trans (genericPoint_specializes y)
  have : a = genericPoint X := hgen.eq (genericPoint_spec X)
  rw [← this]; exact hfa

noncomputable def fieldMap (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y) :
    Y.functionField →+* X.functionField :=
  (f.stalkMap (genericPoint X)).hom.comp
    (Y.presheaf.stalkSpecializes (specializes_of_eq h : f.base (genericPoint X) ⤳ genericPoint Y)).hom

theorem fieldMap_eq (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y) :
    CommRingCat.ofHom (fieldMap f h) =
      Y.presheaf.stalkSpecializes (specializes_of_eq h : f.base (genericPoint X) ⤳ genericPoint Y) ≫
        f.stalkMap (genericPoint X) := rfl

theorem algebraMap_stalkMap (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y)
    (p : X) (s : Y.presheaf.stalk (f.base p)) :
    algebraMap _ X.functionField (f.stalkMap p s) = fieldMap f h (algebraMap _ Y.functionField s) := by
  change (X.presheaf.stalkSpecializes (genericPoint_specializes p)).hom (f.stalkMap p s) =
    (f.stalkMap (genericPoint X)).hom ((Y.presheaf.stalkSpecializes _).hom
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes (f.base p))).hom s))
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply f (genericPoint X) p (genericPoint_specializes p) s]
  congr 1
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

theorem fieldMap_germToFunctionField (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y)
    (U : Y.Opens) [hU : Nonempty (U : Scheme.{u})] [hU' : Nonempty ((f ⁻¹ᵁ U : X.Opens) : Scheme.{u})]
    (s : Γ(Y, U)) :
    fieldMap f h (Y.germToFunctionField U s) = X.germToFunctionField (f ⁻¹ᵁ U) (f.app U s) := by
  have hη : f.base (genericPoint X) ∈ U := by
    rw [h]
    exact ((genericPoint_spec Y).mem_open_set_iff U.2).mpr
      ⟨(Classical.arbitrary (U : Scheme.{u})).1, Set.mem_univ _, (Classical.arbitrary (U : Scheme.{u})).2⟩
  change (f.stalkMap (genericPoint X)).hom ((Y.presheaf.stalkSpecializes _).hom
      ((Y.presheaf.germ U (genericPoint Y) _).hom s)) = (X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) _).hom (f.app U s)
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]

theorem fieldMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (hf : f.base (genericPoint X) = genericPoint Y)
    (hg : g.base (genericPoint Y) = genericPoint Z) (hfg : (f ≫ g).base (genericPoint X) = genericPoint Z) :
    fieldMap (f ≫ g) hfg = (fieldMap f hf).comp (fieldMap g hg) := by
  apply RingHom.ext
  intro t

  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.germ_exist (F := Z.presheaf) (x := genericPoint Z) t
  haveI : Nonempty (U : Scheme.{u}) := ⟨⟨_, hU⟩⟩
  have hηY : g.base (genericPoint Y) ∈ U := by rw [hg]; exact hU
  haveI : Nonempty ((g ⁻¹ᵁ U : Y.Opens) : Scheme.{u}) := ⟨⟨_, hηY⟩⟩
  have hηX : (f ≫ g).base (genericPoint X) ∈ U := by rw [hfg]; exact hU
  haveI : Nonempty (((f ≫ g) ⁻¹ᵁ U : X.Opens) : Scheme.{u}) := ⟨⟨_, hηX⟩⟩
  have hηX' : f.base (genericPoint X) ∈ g ⁻¹ᵁ U := by
    show (f ≫ g).base (genericPoint X) ∈ U; exact hηX
  haveI : Nonempty ((f ⁻¹ᵁ (g ⁻¹ᵁ U) : X.Opens) : Scheme.{u}) := ⟨⟨_, hηX'⟩⟩
  have e1 := fieldMap_germToFunctionField (f ≫ g) hfg U s
  have e2 := fieldMap_germToFunctionField g hg U s
  have e3 := fieldMap_germToFunctionField f hf (g ⁻¹ᵁ U) (g.app U s)
  change fieldMap (f ≫ g) hfg (Z.germToFunctionField U s) = fieldMap f hf (fieldMap g hg (Z.germToFunctionField U s))
  rw [e1, e2, e3]
  rfl

theorem fieldMap_eq_of_fromSpecStalk_comp_eq (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y)
    (c : Y.functionField →+* X.functionField)
    (hc : X.fromSpecStalk (genericPoint X) ≫ f = Spec.map (CommRingCat.ofHom c) ≫ Y.fromSpecStalk (genericPoint Y)) :
    fieldMap f h = c := by
  have key : Spec.map (CommRingCat.ofHom (fieldMap f h)) ≫ Y.fromSpecStalk (genericPoint Y) =
      Spec.map (CommRingCat.ofHom c) ≫ Y.fromSpecStalk (genericPoint Y) := by
    rw [← hc, fieldMap_eq, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  have := (cancel_mono (Y.fromSpecStalk (genericPoint Y))).mp key
  have := Spec.map_injective this
  exact congrArg CommRingCat.Hom.hom this

end FieldMap

section MoreFieldMap
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

theorem fieldMap_baseToFunctionField {K : Type u} [Field K] (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y)
    (x : X ⟶ Spec (CommRingCat.of K)) (y : Y ⟶ Spec (CommRingCat.of K)) (hf : f ≫ y = x) (a : K) :
    fieldMap f h (baseToFunctionField y a) = baseToFunctionField x a := by
  change (f.stalkMap (genericPoint X)).hom ((Y.presheaf.stalkSpecializes _).hom
      ((Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom
        (y.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)))) =
    (X.presheaf.germ ⊤ (genericPoint X) trivial).hom
      (x.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]
  have happ : (f.app ⊤).hom (y.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) =
      x.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a) := by
    rw [← hf]; rfl
  rw [happ]; rfl

theorem fieldMap_id : fieldMap (𝟙 X) rfl = RingHom.id X.functionField := by
  apply RingHom.ext; intro t
  change ((𝟙 X : X ⟶ X).stalkMap (genericPoint X)).hom ((X.presheaf.stalkSpecializes _).hom t) = t
  rw [Scheme.Hom.stalkMap_id]
  change (X.presheaf.stalkSpecializes _ ≫ 𝟙 _).hom t = t
  rw [Category.comp_id, TopCat.Presheaf.stalkSpecializes_refl]; rfl

noncomputable def fieldMapEquiv (e : X ⟶ Y) [IsIso e] : Y.functionField ≃+* X.functionField :=
  RingEquiv.ofRingHom (fieldMap e (apply_genericPoint_eq e)) (fieldMap (inv e) (apply_genericPoint_eq (inv e)))
    (by rw [← fieldMap_comp _ _ (apply_genericPoint_eq e) (apply_genericPoint_eq (inv e))
          (apply_genericPoint_eq (e ≫ inv e))]
        have : fieldMap (e ≫ inv e) (apply_genericPoint_eq (e ≫ inv e)) = fieldMap (𝟙 X) rfl := by
          congr 1 <;> simp
        rw [this, fieldMap_id])
    (by rw [← fieldMap_comp _ _ (apply_genericPoint_eq (inv e)) (apply_genericPoint_eq e)
          (apply_genericPoint_eq (inv e ≫ e))]
        have : fieldMap (inv e ≫ e) (apply_genericPoint_eq (inv e ≫ e)) = fieldMap (𝟙 Y) rfl := by
          congr 1 <;> simp
        rw [this, fieldMap_id])

theorem fieldMapEquiv_apply (e : X ⟶ Y) [IsIso e] (t : Y.functionField) :
    fieldMapEquiv e t = fieldMap e (apply_genericPoint_eq e) t := rfl

end MoreFieldMap

end GenRestr

namespace GenRestr

theorem chartFin_baseChange (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (O : Type) [CommRing O] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) O] :
    ∃ g : Spec (CommRingCat.of (↥(IgusaScheme.chartAlgFin N ℓ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] O)) ⟶
        pullback (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) O))),
      IsOpenImmersion g ∧
      g ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ↥(IgusaScheme.chartAlgFin N ℓ)) (B := O))) ≫
          IgusaScheme.ιFin N ℓ ∧
      g ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ↥(IgusaScheme.chartAlgFin N ℓ)) (B := O)).toRingHom) ∧
      Set.range g.base = ((pullback.fst (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) O)))) ⁻¹ᵁ ((IgusaScheme.ιFin N ℓ) ''ᵁ ⊤) :
        Set ↥(pullback (IgusaScheme.igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) O))))) := by
  set A : Type := ↥(IgusaScheme.chartAlgFin N ℓ) with hA
  set b : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)) := Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) O)) with hb
  set a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)) := Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) A)) with ha

  have hιa : IgusaScheme.ιFin N ℓ ≫ IgusaScheme.igusaTo N ℓ = a := IgusaScheme.ιFin_igusaTo N ℓ
  let g' : pullback a b ⟶ pullback (IgusaScheme.igusaTo N ℓ) b :=
    pullback.lift (pullback.fst a b ≫ IgusaScheme.ιFin N ℓ) (pullback.snd a b) (by rw [Category.assoc, hιa, pullback.condition])
  have hg'fst : g' ≫ pullback.fst _ _ = pullback.fst a b ≫ IgusaScheme.ιFin N ℓ := pullback.lift_fst _ _ _
  have hg'snd : g' ≫ pullback.snd _ _ = pullback.snd a b := pullback.lift_snd _ _ _

  have sq : IsPullback (pullback.fst a b) g' (IgusaScheme.ιFin N ℓ) (pullback.fst (IgusaScheme.igusaTo N ℓ) b) := by
    refine IsPullback.of_bot ?_ hg'fst.symm (IsPullback.of_hasPullback (IgusaScheme.igusaTo N ℓ) b)
    rw [hg'snd, hιa]
    exact IsPullback.of_hasPullback a b
  have hopen : IsOpenImmersion g' := MorphismProperty.of_isPullback sq inferInstance
  have hrange : Set.range g'.base = ((pullback.fst (IgusaScheme.igusaTo N ℓ) b) ⁻¹ᵁ ((IgusaScheme.ιFin N ℓ) ''ᵁ ⊤) : Set _) := by
    have e1 : g' = sq.isoPullback.hom ≫ pullback.snd (IgusaScheme.ιFin N ℓ) (pullback.fst (IgusaScheme.igusaTo N ℓ) b) :=
      (sq.isoPullback_hom_snd).symm
    have hs1 : Function.Surjective sq.isoPullback.hom.base := sq.isoPullback.hom.homeomorph.surjective
    rw [e1, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr hs1, Set.image_univ,
      Scheme.Pullback.range_snd]
    ext x
    simp only [Set.mem_preimage, Set.mem_range]
    constructor
    · rintro ⟨y, hy⟩; exact ⟨y, trivial, hy⟩
    · rintro ⟨y, -, hy⟩; exact ⟨y, hy⟩

  refine ⟨(pullbackSpecIso ↥(GaloisRep.ratLocalizedAt ℓ) A O).inv ≫ g', inferInstance, ?_, ?_, ?_⟩
  · rw [Category.assoc, hg'fst, ← Category.assoc, pullbackSpecIso_inv_fst]
  · rw [Category.assoc, hg'snd, pullbackSpecIso_inv_snd]
    rfl
  · have hs2 : Function.Surjective (pullbackSpecIso ↥(GaloisRep.ratLocalizedAt ℓ) A O).inv.base := (pullbackSpecIso ↥(GaloisRep.ratLocalizedAt ℓ) A O).inv.homeomorph.surjective
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr hs2, Set.image_univ, hrange]

end GenRestr

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.congr_app Scheme.mem_basicOpen pullbackSpecIso_inv_snd Surjective isAffineOpen_opensRange IsOpenImmersion.comp Scheme.Hom Scheme.basicOpen_res_eq Scheme.Hom.germ_stalkMap_apply Scheme.SpecMap_stalkSpecializes_fromSpecStalk Scheme.Hom.stalkSpecializes_stalkMap_apply Scheme.preimage_basicOpen Scheme.Hom.image_top_eq_opensRange Spec IsIntegral Scheme.Opens.toScheme Spec.map Scheme.ΓSpecIso_inv_naturality Scheme pullbackSpecIso IsOpenImmersion functionField_isFractionRing_of_isAffineOpen Scheme.Hom.appIso_inv_app_apply Scheme.Hom.comp_base genericPoint_eq_of_isOpenImmersion Scheme.Hom.comp_appTop Scheme.Pullback.range_snd Spec.map_injective Flat pullbackSpecIso_inv_fst isIntegral_of_isOpenImmersion Scheme.Hom.comp_app Scheme.SpecMap_stalkMap_fromSpecStalk IsAffineOpen genericPoint_eq_bot_of_affine Scheme.Opens Scheme.Hom.stalkMap_id Flat.generalizingMap Scheme.Hom.comp_apply basicOpen_eq_of_affine range_eq_univ Scheme.ΓSpecIso Scheme.Hom.coe_opensRange" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom.congr_app mem_basicOpen germToFunctionField fromSpecStalk Hom basicOpen_res_eq Γ Hom.germ_stalkMap_apply empty SpecMap_stalkSpecializes_fromSpecStalk Hom.stalkSpecializes_stalkMap_apply preimage_basicOpen Hom.image_top_eq_opensRange Opens.toScheme ΓSpecIso_inv_naturality functionField Hom.appIso_inv_app_apply Hom.comp_base Hom.comp_appTop Pullback.range_snd Hom.comp_app basicOpen SpecMap_stalkMap_fromSpecStalk Opens Hom.stalkMap_id Hom.comp_apply ΓSpecIso Hom.coe_opensRange" end AlgebraicGeometry.Scheme
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme" in
theorem AlgebraicGeometry.Scheme.appIso_hom_res_app_appIso_inv_apply
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

  simp only [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl

p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme" in

theorem AlgebraicGeometry.Scheme.map_app_eq_of_eq_comp_comp {X Y Z T : Scheme.{u}} (e' : X ⟶ T) (e : X ⟶ Y) (g : Y ⟶ Z)
    (f : Z ⟶ T) (h : e' = e ≫ g ≫ f)
    (W : T.Opens) (V : Z.Opens) (hV : V ≤ f ⁻¹ᵁ W)
    (hU : (e ≫ g) ⁻¹ᵁ V ≤ e' ⁻¹ᵁ W) (t : Γ(T, W)) :
    X.presheaf.map (homOfLE hU).op ((e'.app W).hom t) =
      ((e ≫ g).app V).hom ((Z.presheaf.map (homOfLE hV).op) ((f.app W).hom t)) := by
  subst h
  have nat := CategoryTheory.ConcreteCategory.congr_hom ((e ≫ g).naturality (homOfLE hV).op) ((f.app W).hom t)
  simp only [CategoryTheory.comp_apply] at nat
  rw [nat]
  simp only [Scheme.Hom.comp_app, CategoryTheory.comp_apply]
  simp only [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl

namespace GenRestr

theorem base_genericPoint_eq_of_chart {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    {B : CommRingCat.{u}} (G : Spec B ⟶ Y) [IsOpenImmersion G]
    (hξ : f.base (genericPoint X) ∈ G ''ᵁ ⊤)
    (hinj : ∀ b : B, X.presheaf.germ (f ⁻¹ᵁ (G ''ᵁ ⊤)) (genericPoint X) hξ
        (f.app (G ''ᵁ ⊤) ((G.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv b))) = 0 → b = 0) :
    f.base (genericPoint X) = genericPoint Y := by
  obtain ⟨𝔮, -, h𝔮⟩ := id hξ

  have hbot : ∀ b ∈ 𝔮.asIdeal, b = 0 := by
    intro b hb
    apply hinj

    set s : Γ(Y, G ''ᵁ ⊤) := (G.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv b) with hs

    have h1 : 𝔮 ∉ G ⁻¹ᵁ Y.basicOpen s := by
      rw [Scheme.preimage_basicOpen, hs, Scheme.Hom.appIso_inv_app_apply, Scheme.basicOpen_res_eq,
        basicOpen_eq_of_affine]
      exact fun h => (PrimeSpectrum.mem_basicOpen _ _ ).mp h hb

    have h2 : genericPoint X ∉ X.basicOpen (f.app (G ''ᵁ ⊤) s) := by
      rw [← Scheme.preimage_basicOpen]
      show f.base (genericPoint X) ∉ Y.basicOpen s
      rw [← h𝔮]; exact h1
    rw [Scheme.mem_basicOpen X _ (genericPoint X) hξ] at h2
    exact not_ne_iff.mp fun hne => h2 (isUnit_iff_ne_zero.mpr hne)

  haveI : Nonempty (Spec B) := ⟨𝔮⟩
  haveI : IsIntegral (Spec B) := isIntegral_of_isOpenImmersion G
  haveI : IsDomain B := MulEquiv.isDomain Γ(Spec B, ⊤) (Scheme.ΓSpecIso B).symm.commRingCatIsoToRingEquiv.toMulEquiv
  have h𝔮bot : 𝔮 = genericPoint (Spec B) := by
    rw [genericPoint_eq_bot_of_affine]
    refine PrimeSpectrum.ext (le_bot_iff.mp fun b hb => ?_)
    rw [hbot b hb]
    exact Ideal.zero_mem _
  rw [← h𝔮, h𝔮bot]
  exact genericPoint_eq_of_isOpenImmersion G

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem injective_of_chart_generators (M M' p : ℕ) [NeZero M] [NeZero M'] [Fact p.Prime]
    {E : Type*} [Ring E] (ψ : ↥(IgusaScheme.chartAlgFin M p) ⊗[R p] AlgebraicClosure ℚ →+* E)
    (ffE : ↥(modularFunctionFieldBar M') ≃+* E)
    (θ : ↥(IgusaScheme.chartAlgFin M p) → ↥(IgusaScheme.chartAlgFin M' p))
    (Φ : ↥(modularFunctionFieldBar M) →ₐ[AlgebraicClosure ℚ] ↥(modularFunctionFieldBar M'))
    (hΦθ : ∀ a : ↥(IgusaScheme.chartAlgFin M p),
      ((Φ ⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(modularFunctionFieldFull M)).2⟩ :
          ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (((θ a : ↥(IgusaScheme.chartAlgFin M' p)) :
          ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ))
    (γ : ↥(IgusaScheme.chartAlgFin M' p) → E)
    (hpin : ∀ b, ((ffE.symm (γ b) : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ))
    (h1 : ∀ a, ψ (a ⊗ₜ 1) = γ (θ a))
    (h2 : ∀ k, ψ (1 ⊗ₜ k) = ffE (algebraMap (AlgebraicClosure ℚ) _ k)) :
    Function.Injective ψ := by
  classical
  set K := AlgebraicClosure ℚ with hK
  obtain ⟨⟨eFin, heFin⟩, -⟩ := IgusaScheme.exists_algEquiv_tensor_chartAlg_chartRing M p

  let ρ : K ⊗[R p] ↥(IgusaScheme.chartAlgFin M p) →+* ↥(modularFunctionFieldBar M') :=
    Φ.toRingHom.comp ((Subalgebra.val _).toRingHom.comp eFin.toAlgHom.toRingHom)
  have hρinj : Function.Injective ρ :=
    Φ.toRingHom.injective.comp (Subtype.val_injective.comp eFin.injective)

  have key : ∀ z, ffE.symm (ψ (Algebra.TensorProduct.comm (R p) K ↥(IgusaScheme.chartAlgFin M p) z)) = ρ z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
    | tmul k a =>

      have hψ : ψ (a ⊗ₜ k) = γ (θ a) * ffE (algebraMap K _ k) := by
        rw [show a ⊗ₜ[R p] k = (a ⊗ₜ[R p] (1 : K)) * ((1 : ↥(IgusaScheme.chartAlgFin M p)) ⊗ₜ[R p] k) by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], map_mul, h1, h2]
      have hca : (ffE.symm (γ (θ a)) : ↥(modularFunctionFieldBar M')) =
          Φ ⟨coeffEmb K ((a : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange K (a : ↥(modularFunctionFieldFull M)).2⟩ :=
        Subtype.ext ((hpin (θ a)).trans (hΦθ a).symm)
      have heFa : eFin (k ⊗ₜ a) = algebraMap K _ k * eFin (1 ⊗ₜ a) := by
        rw [show k ⊗ₜ[R p] a = k • ((1 : K) ⊗ₜ[R p] a) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
          map_smul, Algebra.smul_def]
      change ffE.symm (ψ (Algebra.TensorProduct.comm (R p) K ↥(IgusaScheme.chartAlgFin M p) (k ⊗ₜ a))) =
        Φ ((eFin (k ⊗ₜ a) : ↥(modularFunctionFieldBar M)))
      rw [Algebra.TensorProduct.comm_tmul, hψ, map_mul, hca, RingEquiv.symm_apply_apply, heFa, Subalgebra.coe_mul,
        Subalgebra.coe_algebraMap, map_mul, AlgHom.commutes, heFin a]
      exact mul_comm _ _

  intro x y hxy
  have hx := key ((Algebra.TensorProduct.comm (R p) K ↥(IgusaScheme.chartAlgFin M p)).symm x)
  have hy := key ((Algebra.TensorProduct.comm (R p) K ↥(IgusaScheme.chartAlgFin M p)).symm y)
  rw [AlgEquiv.apply_symm_apply] at hx hy
  rw [hxy, hy] at hx
  exact (Algebra.TensorProduct.comm (R p) K ↥(IgusaScheme.chartAlgFin M p)).symm.injective (hρinj hx).symm

end GenRestr

namespace GenRestr

open ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicCurve Opposite TopologicalSpace

theorem germ_app_appIso_inv_chart {X Y Z : Scheme.{u}} (f : X ⟶ Y) {A B : CommRingCat.{u}} (ι : Spec A ⟶ Z) [IsOpenImmersion ι]
    (G : Spec B ⟶ Y) [IsOpenImmersion G] (π : Y ⟶ Z) (θ : A ⟶ B) (hfac : G ≫ π = Spec.map θ ≫ ι)
    (hWle : G ''ᵁ ⊤ ≤ π ⁻¹ᵁ (ι ''ᵁ ⊤)) (ξ : X) (hξW : f.base ξ ∈ G ''ᵁ ⊤) (U' : X.Opens) (hξU : ξ ∈ U')
    (hUU₀ : U' ≤ f ⁻¹ᵁ (π ⁻¹ᵁ (ι ''ᵁ ⊤))) (a : A) :
    X.presheaf.germ (f ⁻¹ᵁ (G ''ᵁ ⊤)) ξ hξW (f.app _ ((G.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv (θ a)))) =
      X.presheaf.germ U' ξ hξU (X.presheaf.map (homOfLE hUU₀).op
        (f.app _ (π.app (ι ''ᵁ ⊤) ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv a))))) := by
  have hA := AlgebraicGeometry.Scheme.appIso_hom_res_app_appIso_inv_apply π ι G θ hfac a ⊤ hWle
  have htop : (homOfLE le_top : (⊤ : (Spec B).Opens) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
  rw [htop, op_id, CategoryTheory.Functor.map_id, CommRingCat.id_apply] at hA
  have hA' := congrArg (G.appIso ⊤).inv hA
  rw [Iso.hom_inv_id_apply] at hA'
  rw [← hA']
  have hnat := CategoryTheory.ConcreteCategory.congr_hom (f.naturality (homOfLE hWle).op)
    (π.app (ι ''ᵁ ⊤) ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv a)))
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hnat
  erw [hnat]
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]

theorem germ_app_appIso_inv_appTop {X Y S T : Scheme.{u}} (f : X ⟶ Y) (G : S ⟶ Y) [IsOpenImmersion G]
    (y : Y ⟶ T) (x : X ⟶ T) (hfx : f ≫ y = x) (ξ : X) (hξW : f.base ξ ∈ G ''ᵁ ⊤) (c : Γ(T, ⊤)) :
    X.presheaf.germ (f ⁻¹ᵁ (G ''ᵁ ⊤)) ξ hξW (f.app _ ((G.appIso ⊤).inv ((G ≫ y).appTop c))) =
      X.presheaf.germ ⊤ ξ trivial (x.appTop c) := by
  rw [Scheme.Hom.comp_appTop, CategoryTheory.comp_apply]
  have h2k := CategoryTheory.ConcreteCategory.congr_hom (G.app_appIso_inv ⊤) (y.appTop c)
  rw [CategoryTheory.comp_apply] at h2k
  erw [h2k]
  have hnat := CategoryTheory.ConcreteCategory.congr_hom (f.naturality (homOfLE (le_top : G ''ᵁ ⊤ ≤ ⊤)).op) (y.appTop c)
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hnat
  erw [hnat]
  rw [TopCat.Presheaf.germ_res_apply, ← hfx, Scheme.Hom.comp_appTop, CategoryTheory.comp_apply]
  rfl

theorem ΓSpecIso_inv_one_tmul (R A O : Type) [CommRing R] [CommRing A] [Algebra R A] [CommRing O] [Algebra R O] (k : O) :
    (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] O))).inv ((1 : A) ⊗ₜ k) =
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := O)).toRingHom)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv k) := by
  have e6 := CategoryTheory.ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := O)).toRingHom)) k
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e6
  exact e6

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem dominant (M M' p : ℕ) [NeZero M] [NeZero M'] [Fact p.Prime]

    (C₂ : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar M'))
    (e₂ : C₂.C ⟶ pullback (IgusaScheme.igusaTo M' p) (genPt p)) [IsIso e₂]
    (hne₂ : Nonempty (Scheme.Opens.toScheme ((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M' p) ''ᵁ ⊤))))
    (pin₂ : ∀ b : ↥(IgusaScheme.chartAlgFin M' p),
      ((C₂.ffEquiv.symm
          (C₂.C.germToFunctionField
            ((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M' p) ''ᵁ ⊤))
            (((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)).app ((IgusaScheme.ιFin M' p) ''ᵁ ⊤)).hom
              (((IgusaScheme.ιFin M' p).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin M' p))).inv b))))
          : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ))

    (C₁ : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar M))
    (e₁ : C₁.C ⟶ pullback (IgusaScheme.igusaTo M p) (genPt p)) [IsIso e₁] (he₁ : e₁ ≫ pullback.snd _ _ = C₁.toBase)
    (hne₁ : Nonempty (Scheme.Opens.toScheme ((e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M p) ''ᵁ ⊤))))
    (pin₁ : ∀ a : ↥(IgusaScheme.chartAlgFin M p),
      ((C₁.ffEquiv.symm
          (C₁.C.germToFunctionField
            ((e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M p) ''ᵁ ⊤))
            (((e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)).app ((IgusaScheme.ιFin M p) ''ᵁ ⊤)).hom
              (((IgusaScheme.ιFin M p).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin M p))).inv a))))
          : ↥(modularFunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ))
    (θ : ↥(IgusaScheme.chartAlgFin M p) →ₐ[R p] ↥(IgusaScheme.chartAlgFin M' p))
    (Φ : ↥(modularFunctionFieldBar M) →ₐ[AlgebraicClosure ℚ] ↥(modularFunctionFieldBar M'))
    (hΦθ : ∀ a : ↥(IgusaScheme.chartAlgFin M p),
      ((Φ ⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(modularFunctionFieldFull M)).2⟩ :
          ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (((θ a : ↥(IgusaScheme.chartAlgFin M' p)) :
          ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ))
    (πM : C₂.C ⟶ C₁.C)
    (hπM₂ : πM ≫ C₁.toBase = C₂.toBase)
    (hUU₀ : ((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M' p) ''ᵁ ⊤)) ≤ πM ⁻¹ᵁ ((e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M p) ''ᵁ ⊤)))
    (hsecθ : ∀ a : ↥(IgusaScheme.chartAlgFin M p),
      C₂.C.presheaf.map (homOfLE hUU₀).op ((πM.app _).hom (((e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)).app ((IgusaScheme.ιFin M p) ''ᵁ ⊤)).hom (((IgusaScheme.ιFin M p).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin M p))).inv a)))) =
      ((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)).app ((IgusaScheme.ιFin M' p) ''ᵁ ⊤)).hom
        (((IgusaScheme.ιFin M' p).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin M' p))).inv (θ a)))) :
    πM.base (genericPoint C₂.C) = genericPoint C₁.C := by
  classical
  haveI : Nonempty (((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M' p) ''ᵁ ⊤)) : Scheme.{0}) := hne₂
  haveI : Nonempty (((e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M p) ''ᵁ ⊤)) : Scheme.{0}) := hne₁

  obtain ⟨g₀, hg₀open, hg₀fst, hg₀snd, hg₀range⟩ := chartFin_baseChange M p (AlgebraicClosure ℚ)
  let G₀ := g₀ ≫ inv e₁
  haveI : IsOpenImmersion G₀ := IsOpenImmersion.comp _ _
  have hG₀ : G₀ ≫ e₁ = g₀ := by simp only [G₀, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hfac : G₀ ≫ (e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥(IgusaScheme.chartAlgFin M p)) (B := (AlgebraicClosure ℚ)))) ≫
        IgusaScheme.ιFin M p := by
    rw [← Category.assoc, hG₀, hg₀fst]

  have hWU₀ : G₀ ''ᵁ ⊤ = ((e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M p) ''ᵁ ⊤)) := by
    apply TopologicalSpace.Opens.ext
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.coe_opensRange]
    show Set.range (g₀ ≫ inv e₁).base =
      (e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)).base ⁻¹' (((IgusaScheme.ιFin M p) ''ᵁ ⊤) : Set (IgusaScheme M p))
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hg₀range]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have e1 := Scheme.Hom.comp_apply (inv e₁) (e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)) y
      rw [IsIso.inv_hom_id_assoc] at e1
      show (e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)) ((inv e₁) y) ∈ (((IgusaScheme.ιFin M p) ''ᵁ ⊤) : Set (IgusaScheme M p))
      rw [← e1]; exact hy
    · intro hx
      refine ⟨e₁ x, ?_, ?_⟩
      · show (pullback.fst (IgusaScheme.igusaTo M p) (genPt p)) (e₁ x) ∈ (((IgusaScheme.ιFin M p) ''ᵁ ⊤) : Set (IgusaScheme M p))
        rw [← Scheme.Hom.comp_apply]; exact hx
      · show (inv e₁) (e₁ x) = x
        rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  have hWle : G₀ ''ᵁ ⊤ ≤ ((e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M p) ''ᵁ ⊤)) := hWU₀.le

  have hξU : genericPoint C₂.C ∈ ((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M' p) ''ᵁ ⊤)) :=
    ((genericPoint_spec C₂.C).mem_open_set_iff (((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M' p) ''ᵁ ⊤))).2).mpr
      ⟨(Classical.arbitrary (((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M' p) ''ᵁ ⊤)) : Scheme.{0})).1, Set.mem_univ _, (Classical.arbitrary (((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M' p) ''ᵁ ⊤)) : Scheme.{0})).2⟩
  have hξW : πM.base (genericPoint C₂.C) ∈ G₀ ''ᵁ ⊤ := by rw [hWU₀]; exact hUU₀ hξU

  refine base_genericPoint_eq_of_chart πM G₀ hξW ?_
  let ψ : ↥(IgusaScheme.chartAlgFin M p) ⊗[R p] (AlgebraicClosure ℚ) →+* C₂.C.functionField :=
    (C₂.C.presheaf.germ (πM ⁻¹ᵁ (G₀ ''ᵁ ⊤)) (genericPoint C₂.C) hξW).hom.comp
      ((πM.app (G₀ ''ᵁ ⊤)).hom.comp ((G₀.appIso ⊤).inv.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of (↥(IgusaScheme.chartAlgFin M p) ⊗[R p] (AlgebraicClosure ℚ)))).inv.hom))
  have hψapply : ∀ b, ψ b = (C₂.C.presheaf.germ (πM ⁻¹ᵁ (G₀ ''ᵁ ⊤)) (genericPoint C₂.C) hξW).hom
      ((πM.app (G₀ ''ᵁ ⊤)).hom ((G₀.appIso ⊤).inv
        ((Scheme.ΓSpecIso (CommRingCat.of (↥(IgusaScheme.chartAlgFin M p) ⊗[R p] (AlgebraicClosure ℚ)))).inv b))) := fun _ => rfl
  suffices hψ : Function.Injective ψ from fun b hb => hψ (hb.trans (map_zero ψ).symm)
  refine injective_of_chart_generators M M' p ψ C₂.ffEquiv θ Φ hΦθ
    (fun b => C₂.C.germToFunctionField ((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M' p) ''ᵁ ⊤))
      (((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)).app ((IgusaScheme.ιFin M' p) ''ᵁ ⊤)).hom
        (((IgusaScheme.ιFin M' p).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin M' p))).inv b))))
    (fun b => pin₂ b) ?_ ?_
  ·
    intro a
    rw [hψapply]
    have h1 := germ_app_appIso_inv_chart πM (IgusaScheme.ιFin M p) G₀
      (e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥(IgusaScheme.chartAlgFin M p)) (B := (AlgebraicClosure ℚ)))) hfac hWle
      (genericPoint C₂.C) hξW ((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M' p) ''ᵁ ⊤)) hξU hUU₀ a
    erw [h1]
    rw [hsecθ a]
  ·
    intro k
    rw [C₂.ffEquiv_algebraMap, hψapply]
    have hbase : G₀ ≫ C₁.toBase = g₀ ≫ pullback.snd (IgusaScheme.igusaTo M p) (genPt p) := by
      rw [← he₁, ← Category.assoc, hG₀]
    have h1k : (Scheme.ΓSpecIso (CommRingCat.of (↥(IgusaScheme.chartAlgFin M p) ⊗[R p] (AlgebraicClosure ℚ)))).inv ((1 : ↥(IgusaScheme.chartAlgFin M p)) ⊗ₜ k) =
        (G₀ ≫ C₁.toBase).appTop ((Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).inv k) := by
      rw [hbase, hg₀snd]
      exact ΓSpecIso_inv_one_tmul (R p) ↥(IgusaScheme.chartAlgFin M p) (AlgebraicClosure ℚ) k
    rw [h1k]
    exact germ_app_appIso_inv_appTop πM G₀ C₁.toBase C₂.toBase hπM₂ (genericPoint C₂.C) hξW _

end GenRestr

namespace GenRestr

section ChartExt

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

theorem germToFunctionField_appIso_inv_chart {A B : CommRingCat.{u}} (ι : Spec A ⟶ Z) [IsOpenImmersion ι]
    (G : Spec B ⟶ Y) [IsOpenImmersion G] (π : Y ⟶ Z) (θ : A ⟶ B) (hfac : G ≫ π = Spec.map θ ≫ ι)
    (hWle : G ''ᵁ ⊤ ≤ π ⁻¹ᵁ (ι ''ᵁ ⊤))
    [Nonempty ((G ''ᵁ ⊤ : Y.Opens) : Scheme.{u})] [Nonempty ((π ⁻¹ᵁ (ι ''ᵁ ⊤) : Y.Opens) : Scheme.{u})] (a : A) :
    Y.germToFunctionField (G ''ᵁ ⊤) ((G.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv (θ a))) =
      Y.germToFunctionField (π ⁻¹ᵁ (ι ''ᵁ ⊤))
        ((π.app (ι ''ᵁ ⊤)).hom (((ι.appIso ⊤).inv) ((Scheme.ΓSpecIso A).inv a))) := by
  have hA := AlgebraicGeometry.Scheme.appIso_hom_res_app_appIso_inv_apply π ι G θ hfac a ⊤ hWle
  have htop : (homOfLE le_top : (⊤ : (Spec B).Opens) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
  rw [htop, op_id, CategoryTheory.Functor.map_id, CommRingCat.id_apply] at hA
  have hA' := congrArg (G.appIso ⊤).inv hA
  rw [Iso.hom_inv_id_apply] at hA'
  rw [← hA']
  exact TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hWle) _ _ _

theorem germToFunctionField_appIso_inv_base {B : CommRingCat.{u}} (G : Spec B ⟶ Y) [IsOpenImmersion G]
    {K : Type u} [Field K] (y : Y ⟶ Spec (CommRingCat.of K)) (c : CommRingCat.of K ⟶ B) (hc : G ≫ y = Spec.map c)
    [Nonempty ((G ''ᵁ ⊤ : Y.Opens) : Scheme.{u})] (k : K) :
    Y.germToFunctionField (G ''ᵁ ⊤) ((G.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv (c k))) =
      baseToFunctionField y k := by
  have e6 := CategoryTheory.ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality c) k
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e6
  rw [e6, ← hc, Scheme.Hom.comp_appTop, CategoryTheory.comp_apply]
  have h2k := CategoryTheory.ConcreteCategory.congr_hom (G.app_appIso_inv ⊤) (y.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv k))
  rw [CategoryTheory.comp_apply] at h2k
  erw [h2k]
  erw [TopCat.Presheaf.germ_res_apply]
  rfl

theorem fieldMap_eq_of_chart (f : X ⟶ Y) (hξ : f.base (genericPoint X) = genericPoint Y)
    {A B : CommRingCat.{u}} (ι : Spec A ⟶ Z) [IsOpenImmersion ι]
    (G : Spec B ⟶ Y) [IsOpenImmersion G] (π : Y ⟶ Z) (θ : A ⟶ B) (hfac : G ≫ π = Spec.map θ ≫ ι)
    (hWle : G ''ᵁ ⊤ ≤ π ⁻¹ᵁ (ι ''ᵁ ⊤))
    {K : Type u} [Field K] (y : Y ⟶ Spec (CommRingCat.of K)) (x : X ⟶ Spec (CommRingCat.of K)) (hfx : f ≫ y = x)
    (c : CommRingCat.of K ⟶ B) (hc : G ≫ y = Spec.map c)
    (hgen : ∀ (χ χ' : (B : Type u) →+* (X.functionField : Type u)),
      (∀ a : A, χ (θ a) = χ' (θ a)) → (∀ k : K, χ (c k) = χ' (c k)) → χ = χ')
    (hB : Nontrivial B)
    (U' : X.Opens) (hU'ne : Nonempty (U' : Scheme.{u})) (hU' : U' ≤ f ⁻¹ᵁ (π ⁻¹ᵁ (ι ''ᵁ ⊤)))
    (hVne : Nonempty ((π ⁻¹ᵁ (ι ''ᵁ ⊤) : Y.Opens) : Scheme.{u}))
    (ψ : (Y.functionField : Type u) →+* (X.functionField : Type u))
    (h₁ : ∀ a : A, X.germToFunctionField U' (X.presheaf.map (homOfLE hU').op
        ((f.app _).hom ((π.app (ι ''ᵁ ⊤)).hom (((ι.appIso ⊤).inv) ((Scheme.ΓSpecIso A).inv a))))) =
      ψ (Y.germToFunctionField (π ⁻¹ᵁ (ι ''ᵁ ⊤))
        ((π.app (ι ''ᵁ ⊤)).hom (((ι.appIso ⊤).inv) ((Scheme.ΓSpecIso A).inv a)))))
    (h₂ : ∀ k : K, baseToFunctionField x k = ψ (baseToFunctionField y k)) :
    fieldMap f hξ = ψ := by
  classical
  haveI := hB

  haveI : Nonempty (Spec B) := (inferInstance : Nonempty (PrimeSpectrum B))
  haveI : Nonempty ((G ''ᵁ ⊤ : Y.Opens) : Scheme.{u}) :=
    ⟨⟨G.base (Classical.arbitrary (Spec B)), ⟨_, trivial, rfl⟩⟩⟩
  haveI : Nonempty ((f ⁻¹ᵁ (π ⁻¹ᵁ (ι ''ᵁ ⊤)) : X.Opens) : Scheme.{u}) :=
    ⟨⟨(Classical.arbitrary (U' : Scheme.{u})).1, hU' (Classical.arbitrary (U' : Scheme.{u})).2⟩⟩
  have hWaff : IsAffineOpen (G ''ᵁ ⊤) := by
    rw [Scheme.Hom.image_top_eq_opensRange]; exact isAffineOpen_opensRange G
  haveI := AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen Y (G ''ᵁ ⊤) hWaff

  obtain ⟨r, hr⟩ : ∃ r : (B : Type u) →+* (Y.functionField : Type u),
      ∀ b, r b = Y.germToFunctionField (G ''ᵁ ⊤) ((G.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv b)) :=
    ⟨(Y.germToFunctionField (G ''ᵁ ⊤)).hom.comp ((G.appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso B).inv.hom), fun _ => rfl⟩
  have key : (fieldMap f hξ).comp r = ψ.comp r := by
    apply hgen
    · intro a
      rw [RingHom.comp_apply, RingHom.comp_apply, hr, germToFunctionField_appIso_inv_chart ι G π θ hfac hWle a,
        fieldMap_germToFunctionField, ← h₁ a]
      exact (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hU') _ _ _).symm
    · intro k
      rw [RingHom.comp_apply, RingHom.comp_apply, hr, germToFunctionField_appIso_inv_base G y c hc k,
        fieldMap_baseToFunctionField f hξ x y hfx k, h₂ k]

  apply IsLocalization.ringHom_ext (nonZeroDivisors Γ(Y, G ''ᵁ ⊤))
  apply RingHom.ext
  intro s
  obtain ⟨b, rfl⟩ : ∃ b : B, (G.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv b) = s :=
    ⟨(Scheme.ΓSpecIso B).hom ((G.appIso ⊤).hom s), by rw [Iso.hom_inv_id_apply, Iso.hom_inv_id_apply]⟩
  have := RingHom.congr_fun key b
  rw [RingHom.comp_apply, RingHom.comp_apply, hr] at this
  rw [RingHom.comp_apply, RingHom.comp_apply]
  exact this

theorem fromSpecStalk_comp_eq_of_fieldMap_eq (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y)
    (c : Y.functionField →+* X.functionField) (hc : fieldMap f h = c) :
    X.fromSpecStalk (genericPoint X) ≫ f = Spec.map (CommRingCat.ofHom c) ≫ Y.fromSpecStalk (genericPoint Y) := by
  subst hc
  rw [fieldMap_eq, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

end ChartExt

theorem ringHom_ext_tensor {R A O L : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing O] [Algebra R O]
    [Semiring L] (χ χ' : A ⊗[R] O →+* L)
    (h1 : ∀ a, χ (a ⊗ₜ 1) = χ' (a ⊗ₜ 1)) (h2 : ∀ k, χ (1 ⊗ₜ k) = χ' (1 ⊗ₜ k)) : χ = χ' := by
  apply RingHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a k =>
    rw [show a ⊗ₜ[R] k = (a ⊗ₜ[R] (1 : O)) * ((1 : A) ⊗ₜ[R] k) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], map_mul, map_mul, h1, h2]

end GenRestr

namespace GenRestr

open ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicCurve

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem core (M M' p : ℕ) [NeZero M] [NeZero M'] [Fact p.Prime]

    (C₂ : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar M'))
    (e₂ : C₂.C ⟶ pullback (IgusaScheme.igusaTo M' p) (genPt p)) [IsIso e₂]
    (hne₂ : Nonempty (Scheme.Opens.toScheme ((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M' p) ''ᵁ ⊤))))
    (pin₂ : ∀ b : ↥(IgusaScheme.chartAlgFin M' p),
      ((C₂.ffEquiv.symm
          (C₂.C.germToFunctionField
            ((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M' p) ''ᵁ ⊤))
            (((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)).app ((IgusaScheme.ιFin M' p) ''ᵁ ⊤)).hom
              (((IgusaScheme.ιFin M' p).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin M' p))).inv b))))
          : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ))

    (C₁ : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar M))
    (e₁ : C₁.C ⟶ pullback (IgusaScheme.igusaTo M p) (genPt p)) [IsIso e₁] (he₁ : e₁ ≫ pullback.snd _ _ = C₁.toBase)
    (hne₁ : Nonempty (Scheme.Opens.toScheme ((e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M p) ''ᵁ ⊤))))
    (pin₁ : ∀ a : ↥(IgusaScheme.chartAlgFin M p),
      ((C₁.ffEquiv.symm
          (C₁.C.germToFunctionField
            ((e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M p) ''ᵁ ⊤))
            (((e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)).app ((IgusaScheme.ιFin M p) ''ᵁ ⊤)).hom
              (((IgusaScheme.ιFin M p).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin M p))).inv a))))
          : ↥(modularFunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ))
    (θ : ↥(IgusaScheme.chartAlgFin M p) →ₐ[R p] ↥(IgusaScheme.chartAlgFin M' p))
    (Φ : ↥(modularFunctionFieldBar M) →ₐ[AlgebraicClosure ℚ] ↥(modularFunctionFieldBar M'))
    (hΦθ : ∀ a : ↥(IgusaScheme.chartAlgFin M p),
      ((Φ ⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(modularFunctionFieldFull M)).2⟩ :
          ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (((θ a : ↥(IgusaScheme.chartAlgFin M' p)) :
          ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ))
    (πX : IgusaScheme M' p ⟶ IgusaScheme M p)
    (hchart : IgusaScheme.ιFin M' p ≫ πX = Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ IgusaScheme.ιFin M p)
    (πM : C₂.C ⟶ C₁.C)
    (hπM₁ : πM ≫ e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p) =
      e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p) ≫ πX)
    (hπM₂ : πM ≫ C₁.toBase = C₂.toBase) :
    C₂.C.fromSpecStalk (genericPoint C₂.C) ≫ πM =
      Spec.map (CommRingCat.ofHom
        (C₂.ffEquiv.toRingHom.comp (Φ.toRingHom.comp C₁.ffEquiv.symm.toRingHom))) ≫
        C₁.C.fromSpecStalk (genericPoint C₁.C) := by
  classical

  let V : (IgusaScheme M' p).Opens := (IgusaScheme.ιFin M' p) ''ᵁ ⊤
  let V₀ : (IgusaScheme M p).Opens := (IgusaScheme.ιFin M p) ''ᵁ ⊤
  let U : C₂.C.Opens := (e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)) ⁻¹ᵁ V
  let U₀ : C₁.C.Opens := (e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)) ⁻¹ᵁ V₀

  let sec : ↥(IgusaScheme.chartAlgFin M' p) → Γ(C₂.C, U) := fun b =>
    ((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)).app V).hom
      (((IgusaScheme.ιFin M' p).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin M' p))).inv b))
  let sec₀ : ↥(IgusaScheme.chartAlgFin M p) → Γ(C₁.C, U₀) := fun a =>
    ((e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)).app V₀).hom
      (((IgusaScheme.ιFin M p).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin M p))).inv a))
  haveI : Nonempty (U : Scheme.{0}) := hne₂
  haveI : Nonempty (U₀ : Scheme.{0}) := hne₁
  let γ : ↥(IgusaScheme.chartAlgFin M' p) → C₂.C.functionField := fun b => C₂.C.germToFunctionField U (sec b)
  let γ₀ : ↥(IgusaScheme.chartAlgFin M p) → C₁.C.functionField := fun a => C₁.C.germToFunctionField U₀ (sec₀ a)
  have hpin : ∀ b, ((C₂.ffEquiv.symm (γ b) : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ) := fun b => pin₂ b
  have hpin₀ : ∀ a, ((C₁.ffEquiv.symm (γ₀ a) : ↥(modularFunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ) := fun a => pin₁ a

  have hVV₀ : V ≤ πX ⁻¹ᵁ V₀ := by
    rintro _ ⟨z, -, rfl⟩
    show (IgusaScheme.ιFin M' p ≫ πX).base z ∈ (V₀ : Set (IgusaScheme M p))
    rw [hchart]
    exact ⟨_, trivial, rfl⟩
  have hUU₀ : U ≤ πM ⁻¹ᵁ U₀ := by
    intro x hx
    have e := congrArg (fun f : C₂.C ⟶ IgusaScheme M p => f.base x) hπM₁
    simp only [Scheme.Hom.comp_apply] at e
    have hx' : πX.base ((pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)).base (e₂.base x)) ∈ V₀ := by
      apply hVV₀
      simp only [Scheme.Hom.comp_apply] at hx ⊢
      exact hx
    rw [← e] at hx'
    exact hx'

  have hXsec : ∀ a, (IgusaScheme M' p).presheaf.map (homOfLE hVV₀).op
      ((πX.app V₀).hom (((IgusaScheme.ιFin M p).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin M p))).inv a))) =
      ((IgusaScheme.ιFin M' p).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin M' p))).inv (θ a)) := by
    intro a
    have h1 := AlgebraicGeometry.Scheme.appIso_hom_res_app_appIso_inv_apply πX (IgusaScheme.ιFin M p)
      (IgusaScheme.ιFin M' p) (CommRingCat.ofHom θ.toRingHom) hchart a ⊤ hVV₀
    have h1' := congrArg ((IgusaScheme.ιFin M' p).appIso ⊤).inv h1
    rw [Iso.hom_inv_id_apply] at h1'
    rw [h1']
    congr 1

  have hsecθ : ∀ a, C₂.C.presheaf.map (homOfLE hUU₀).op ((πM.app U₀).hom (sec₀ a)) = sec (θ a) := by
    intro a
    show C₂.C.presheaf.map (homOfLE hUU₀).op ((πM.app U₀).hom
      (((e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)).app V₀).hom _)) =
      ((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)).app V).hom _
    rw [← hXsec a]
    have e1 : (πM.app U₀).hom ((((e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)).app V₀).hom
        (((IgusaScheme.ιFin M p).appIso ⊤).inv ((Scheme.ΓSpecIso _).inv a)))) =
      ((πM ≫ e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)).app V₀).hom
        (((IgusaScheme.ιFin M p).appIso ⊤).inv ((Scheme.ΓSpecIso _).inv a)) := by
      rw [Scheme.Hom.comp_app πM (e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)) V₀]
      rfl
    rw [e1]
    exact AlgebraicGeometry.Scheme.map_app_eq_of_eq_comp_comp _ e₂ (pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)) πX
      hπM₁ V₀ V hVV₀ _ _

  have hξ : πM.base (genericPoint C₂.C) = genericPoint C₁.C :=
    dominant M M' p C₂ e₂ hne₂ pin₂ C₁ e₁ he₁ hne₁ pin₁ θ Φ hΦθ πM hπM₂ hUU₀ hsecθ

  have hv1' : ∀ a, C₂.ffEquiv (Φ (C₁.ffEquiv.symm (γ₀ a))) = γ (θ a) := by
    intro a
    have e1 : C₁.ffEquiv.symm (γ₀ a) =
        ⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(modularFunctionFieldFull M)).2⟩ := Subtype.ext (hpin₀ a)
    have e2 : Φ (C₁.ffEquiv.symm (γ₀ a)) = C₂.ffEquiv.symm (γ (θ a)) :=
      Subtype.ext (by rw [e1, hΦθ a, hpin (θ a)])
    rw [e2, RingEquiv.apply_symm_apply]

  have hv2' : ∀ k : AlgebraicClosure ℚ, C₂.ffEquiv (Φ (C₁.ffEquiv.symm (baseToFunctionField C₁.toBase k))) =
      baseToFunctionField C₂.toBase k := by
    intro k
    rw [← C₁.ffEquiv_algebraMap k, RingEquiv.symm_apply_apply, AlgHom.commutes, C₂.ffEquiv_algebraMap]

  obtain ⟨⟨eF₀, -⟩, -⟩ := IgusaScheme.exists_algEquiv_tensor_chartAlg_chartRing M p
  haveI : IsDomain ((AlgebraicClosure ℚ) ⊗[R p] ↥(IgusaScheme.chartAlgFin M p)) := MulEquiv.isDomain _ eF₀.toMulEquiv
  have hnt : Nontrivial (CommRingCat.of (↥(IgusaScheme.chartAlgFin M p) ⊗[R p] (AlgebraicClosure ℚ))) :=
    (Algebra.TensorProduct.comm (R p) (AlgebraicClosure ℚ) ↥(IgusaScheme.chartAlgFin M p)).injective.nontrivial

  obtain ⟨g₀, hg₀o, hg₀fst, hg₀snd, -⟩ := chartFin_baseChange M p (AlgebraicClosure ℚ)
  haveI := hg₀o
  obtain ⟨G₀, hG₀o, hG₀fac, hG₀base⟩ : ∃ G₀ : Spec (CommRingCat.of (↥(IgusaScheme.chartAlgFin M p) ⊗[R p] (AlgebraicClosure ℚ))) ⟶ C₁.C,
      IsOpenImmersion G₀ ∧
      G₀ ≫ (e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)) =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := R p) (A := ↥(IgusaScheme.chartAlgFin M p)) (B := (AlgebraicClosure ℚ)))) ≫ IgusaScheme.ιFin M p ∧
      G₀ ≫ C₁.toBase =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := R p) (A := ↥(IgusaScheme.chartAlgFin M p)) (B := (AlgebraicClosure ℚ))).toRingHom) :=
    ⟨g₀ ≫ inv e₁, IsOpenImmersion.comp _ _,
      by rw [Category.assoc, IsIso.inv_hom_id_assoc, hg₀fst],
      by rw [← hg₀snd, ← he₁, Category.assoc, IsIso.inv_hom_id_assoc]⟩
  haveI := hG₀o
  have hG₀top : G₀ ''ᵁ ⊤ ≤ U₀ := by
    rintro _ ⟨z, -, rfl⟩
    show (G₀ ≫ e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)).base z ∈ (V₀ : Set (IgusaScheme M p))
    rw [hG₀fac]
    exact ⟨_, trivial, rfl⟩

  have hB : fieldMap πM hξ = C₂.ffEquiv.toRingHom.comp (Φ.toRingHom.comp C₁.ffEquiv.symm.toRingHom) :=
    fieldMap_eq_of_chart πM hξ (IgusaScheme.ιFin M p) G₀ (e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := ↥(IgusaScheme.chartAlgFin M p)) (B := (AlgebraicClosure ℚ)))) hG₀fac hG₀top
      C₁.toBase C₂.toBase hπM₂
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := ↥(IgusaScheme.chartAlgFin M p)) (B := (AlgebraicClosure ℚ))).toRingHom) hG₀base
      (fun χ χ' ha hk => ringHom_ext_tensor χ χ' (fun a => ha a) (fun k => hk k))
      hnt U hne₂ hUU₀ hne₁ _
      (fun a => (congrArg (fun s => C₂.C.germToFunctionField U s) (hsecθ a)).trans (hv1' a).symm)
      (fun k => (hv2' k).symm)

  exact fromSpecStalk_comp_eq_of_fieldMap_eq πM hξ _ hB

end GenRestr

end

open ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicCurve in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem GenRestr.alpha_of_core
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (M : LevelModel N₀ p A)
    (πM : 𝔓.Meta.C ⟶ M.Meta₀.C)
    (hπM₁ : πM ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) =
      𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ 𝔓.π.1)
    (hπM₂ : πM ≫ M.Meta₀.toBase = 𝔓.Meta.toBase) :
    𝔓.Meta.C.fromSpecStalk (genericPoint 𝔓.Meta.C) ≫ πM =
      Spec.map (CommRingCat.ofHom
        (𝔓.Meta.ffEquiv.toRingHom.comp ((heckeAlphaBar (AlgebraicClosure ℚ) N₀ p).toRingHom.comp
          M.Meta₀.ffEquiv.symm.toRingHom))) ≫
        M.Meta₀.C.fromSpecStalk (genericPoint M.Meta₀.C) :=
  GenRestr.core N₀ (N₀ * p) p 𝔓.Meta 𝔓.eeta 𝔓.Meta_chart_nonempty 𝔓.Meta_pin M.Meta₀ M.eeta₀ M.heeta₀ M.Meta₀_chart_nonempty M.Meta₀_pin
    𝔓.iota0 (heckeAlphaBar (AlgebraicClosure ℚ) N₀ p)
    (fun a => by rw [coe_heckeAlphaBar, 𝔓.iota0_spec a]) 𝔓.π.1 𝔓.pi_chart πM hπM₁ hπM₂

open ModularCurve ModularCurve.DRLevel AlgebraicCurve in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem GenRestr.place
    (M M' p : ℕ) [NeZero M] [NeZero M'] [Fact p.Prime]

    (C₂ : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar M'))
    (e₂ : C₂.C ⟶ pullback (IgusaScheme.igusaTo M' p) (genPt p)) [IsIso e₂] (he₂ : e₂ ≫ pullback.snd _ _ = C₂.toBase)
    (hne₂ : Nonempty (Scheme.Opens.toScheme ((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M' p) ''ᵁ ⊤))))
    (pin₂ : ∀ b : ↥(IgusaScheme.chartAlgFin M' p),
      ((C₂.ffEquiv.symm
          (C₂.C.germToFunctionField
            ((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M' p) ''ᵁ ⊤))
            (((e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p)).app ((IgusaScheme.ιFin M' p) ''ᵁ ⊤)).hom
              (((IgusaScheme.ιFin M' p).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin M' p))).inv b))))
          : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ))

    (C₁ : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar M))
    (e₁ : C₁.C ⟶ pullback (IgusaScheme.igusaTo M p) (genPt p)) [IsIso e₁] (he₁ : e₁ ≫ pullback.snd _ _ = C₁.toBase)
    (hne₁ : Nonempty (Scheme.Opens.toScheme ((e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M p) ''ᵁ ⊤))))
    (pin₁ : ∀ a : ↥(IgusaScheme.chartAlgFin M p),
      ((C₁.ffEquiv.symm
          (C₁.C.germToFunctionField
            ((e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin M p) ''ᵁ ⊤))
            (((e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p)).app ((IgusaScheme.ιFin M p) ''ᵁ ⊤)).hom
              (((IgusaScheme.ιFin M p).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin M p))).inv a))))
          : ↥(modularFunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ))
    (θ : ↥(IgusaScheme.chartAlgFin M p) →ₐ[R p] ↥(IgusaScheme.chartAlgFin M' p))
    (Φ : ↥(modularFunctionFieldBar M) →ₐ[AlgebraicClosure ℚ] ↥(modularFunctionFieldBar M'))
    (hΦθ : ∀ a : ↥(IgusaScheme.chartAlgFin M p),
      ((Φ ⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(modularFunctionFieldFull M)).2⟩ :
          ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (((θ a : ↥(IgusaScheme.chartAlgFin M' p)) :
          ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ))
    (πX : IgusaScheme M' p ⟶ IgusaScheme M p) (hπX : πX ≫ IgusaScheme.igusaTo M p = IgusaScheme.igusaTo M' p)
    (hchart : IgusaScheme.ιFin M' p ≫ πX = Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ IgusaScheme.ιFin M p)

    (hint : Φ.toRingHom.IsIntegral) (hfin : FiniteAlong (AlgebraicClosure ℚ) Φ)

    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ C₂.C // q ≫ C₂.toBase = 𝟙 _})
    (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ C₁.C // q ≫ C₁.toBase = 𝟙 _})
    (hyx : x.1 ≫ e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p) =
      y.1 ≫ e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p) ≫ πX) :
    C₁.pointEquivPlace x = (C₂.pointEquivPlace y).restrictAlong Φ hint := by

  have hinv₁ : inv e₁ ≫ C₁.toBase = pullback.snd (IgusaScheme.igusaTo M p) (genPt p) := by
    rw [IsIso.inv_comp_eq, he₁]
  let πM : C₂.C ⟶ C₁.C :=
    pullback.lift (e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p) ≫ πX) (e₂ ≫ pullback.snd (IgusaScheme.igusaTo M' p) (genPt p))
      (by simp only [Category.assoc, hπX]; rw [pullback.condition]) ≫ inv e₁
  have hπM₁ : πM ≫ e₁ ≫ pullback.fst (IgusaScheme.igusaTo M p) (genPt p) =
      e₂ ≫ pullback.fst (IgusaScheme.igusaTo M' p) (genPt p) ≫ πX := by
    simp only [πM, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]
  have hπM₂ : πM ≫ C₁.toBase = C₂.toBase := by
    simp only [πM, Category.assoc, hinv₁, pullback.lift_snd, he₂]

  have hxy : y.1 ≫ πM = x.1 := by
    rw [← cancel_mono e₁]
    apply pullback.hom_ext
    · simp only [Category.assoc]; rw [hπM₁, hyx]
    · simp only [Category.assoc]; rw [he₁, hπM₂, y.2, x.2]

  letI := algebraAlong Φ
  haveI := isScalarTower_along Φ
  haveI : Module.Finite ↥(modularFunctionFieldBar M) ↥(modularFunctionFieldBar M') := hfin

  obtain ⟨πu, -, -, -, -, -, hgenu, hplaces, huniq⟩ :=
    AlgebraicCurve.CurveModel.exists_hom_pointEquivPlace_restrict_eq C₁ C₂
  have hgenM := GenRestr.core M M' p C₂ e₂ hne₂ pin₂ C₁ e₁ he₁ hne₁ pin₁ θ Φ hΦθ πX hchart πM hπM₁ hπM₂
  have heq : πM = πu := huniq πM (by rw [hgenM, hgenu])
  have hres := hplaces y x (by rw [← heq, hxy])
  rw [← hres]
  rfl

open ModularCurve ModularCurve.DRLevel AlgebraicCurve in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (hint : ((geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N₀ * p))
      (atkinLehnerInvolutionFull N₀ p)).toAlgHom).toRingHom.IsIntegral)

    (y x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (hyx : x.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) =
      y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ 𝔓.w.hom) :
    𝔓.Meta.pointEquivPlace x =
      (𝔓.Meta.pointEquivPlace y).restrictAlong
        (geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N₀ * p)) (atkinLehnerInvolutionFull N₀ p)).toAlgHom hint := by
  let σ := geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N₀ * p)) (atkinLehnerInvolutionFull N₀ p)
  have hfin : FiniteAlong (AlgebraicClosure ℚ) σ.toAlgHom :=
    RingHom.Finite.of_surjective σ.toAlgHom.toRingHom σ.surjective
  have hΦθ : ∀ a : ↥(IgusaScheme.chartAlgFin (N₀ * p) p),
      ((σ.toAlgHom ⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull (N₀ * p))) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(modularFunctionFieldFull (N₀ * p))).2⟩ :
          ↥(modularFunctionFieldBar (N₀ * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (((𝔓.theta a : ↥(IgusaScheme.chartAlgFin (N₀ * p) p)) :
          ↥(modularFunctionFieldFull (N₀ * p))) : LaurentSeries ℚ) := by
    intro a
    rw [𝔓.theta_spec a]
    exact coe_geomAut_coeffEmb (AlgebraicClosure ℚ) _ _ _
  have hchart : IgusaScheme.ιFin (N₀ * p) p ≫ 𝔓.w.hom =
      Spec.map (CommRingCat.ofHom 𝔓.theta.toAlgHom.toRingHom) ≫ IgusaScheme.ιFin (N₀ * p) p := 𝔓.w_chart
  exact GenRestr.place (N₀ * p) (N₀ * p) p 𝔓.Meta 𝔓.eeta 𝔓.heeta 𝔓.Meta_chart_nonempty 𝔓.Meta_pin
    𝔓.Meta 𝔓.eeta 𝔓.heeta 𝔓.Meta_chart_nonempty 𝔓.Meta_pin 𝔓.theta.toAlgHom σ.toAlgHom hΦθ 𝔓.w.hom 𝔓.w_over hchart
    hint hfin y x hyx

end S_ModularCurve_DRModelPackageLevel_pointEquivPlace_eq_restrictAlong_geomAut_of_comp_w
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_pointEquivPlace_eq_restrictAlong_geomAut_of_comp_w (solution)
