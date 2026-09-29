-- Prove2me | solution 1 for ModularCurve.fromSpecStalk_genericPoint_comp_eq_of_xHDRModelAtP_top_drModelPackageLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/5f130313-07a6-5087-9cb0-58654c2a55eb

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_fromSpecStalk_genericPoint_comp_eq_of_xHDRModelAtP_top_drModelPackageLevel

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_fromSpecStalk_genericPoint_comp_eq_of_xHDRModelAtP_top_drModelPackageLevel.AlgebraicGeometry AlgebraicCurve P2MW.S_ModularCurve_fromSpecStalk_genericPoint_comp_eq_of_xHDRModelAtP_top_drModelPackageLevel.AlgebraicCurve"
open Topology
open scoped TensorProduct

universe u v

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel TwoChartIntegralModel.ιFin_toBase baseToFunctionField CurveModel"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "chartAlgFin ιFin toBase ιFin_toBase"
namespace PlaceTransport
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

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

end AlgebraicCurve.TwoChartIntegralModel.PlaceTransport

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.congr_app Scheme.mem_basicOpen pullbackSpecIso_inv_snd Surjective isAffineOpen_opensRange IsOpenImmersion.comp Scheme.Hom Scheme.basicOpen_res_eq Scheme.Hom.germ_stalkMap_apply Scheme.SpecMap_stalkSpecializes_fromSpecStalk Scheme.Hom.stalkSpecializes_stalkMap_apply Scheme.preimage_basicOpen Scheme.Hom.image_top_eq_opensRange Spec IsIntegral Scheme.Opens.toScheme Spec.map Scheme.ΓSpecIso_inv_naturality Scheme pullbackSpecIso IsOpenImmersion functionField_isFractionRing_of_isAffineOpen Scheme.Hom.appIso_inv_app_apply Scheme.Hom.comp_base genericPoint_eq_of_isOpenImmersion Scheme.Hom.comp_appTop Scheme.Pullback.range_snd Spec.map_injective Flat pullbackSpecIso_inv_fst isIntegral_of_isOpenImmersion Scheme.Hom.comp_app Scheme.SpecMap_stalkMap_fromSpecStalk IsAffineOpen genericPoint_eq_bot_of_affine Scheme.Opens Scheme.Hom.stalkMap_id Flat.generalizingMap Scheme.Hom.comp_apply basicOpen_eq_of_affine range_eq_univ Scheme.ΓSpecIso Scheme.Hom.coe_opensRange" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom.congr_app mem_basicOpen germToFunctionField fromSpecStalk Hom basicOpen_res_eq germToFunctionField_injective Γ Hom.germ_stalkMap_apply empty SpecMap_stalkSpecializes_fromSpecStalk Hom.stalkSpecializes_stalkMap_apply preimage_basicOpen Hom.image_top_eq_opensRange Opens.toScheme ΓSpecIso_inv_naturality functionField Hom.appIso_inv_app_apply Hom.comp_base Hom.comp_appTop Pullback.range_snd Hom.comp_app basicOpen SpecMap_stalkMap_fromSpecStalk Opens Hom.stalkMap_id Hom.comp_apply ΓSpecIso Hom.coe_opensRange" end AlgebraicGeometry.Scheme
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

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel TwoChartIntegralModel.ιFin_toBase baseToFunctionField CurveModel"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "chartAlgFin ιFin toBase ιFin_toBase"
namespace PlaceTransport
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

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

theorem ΓSpecIso_inv_one_tmul (R A O : Type u) [CommRing R] [CommRing A] [Algebra R A] [CommRing O] [Algebra R O] (k : O) :
    (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] O))).inv ((1 : A) ⊗ₜ k) =
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := O)).toRingHom)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv k) := by
  have e6 := CategoryTheory.ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := O)).toRingHom)) k
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e6
  exact e6

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

theorem chartFin_baseChange (R : Type u) [CommRing R] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) (A : Type u) [CommRing A] [Algebra R A]
    (ι₁ : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion ι₁] (hι₁ : ι₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (O : Type u) [CommRing O] [Algebra R O] :
    ∃ g : Spec (CommRingCat.of (A ⊗[R] O)) ⟶
        pullback (f) (Spec.map (CommRingCat.ofHom (algebraMap R O))),
      IsOpenImmersion g ∧
      g ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := O))) ≫
          ι₁ ∧
      g ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := O)).toRingHom) ∧
      Set.range g.base = ((pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R O)))) ⁻¹ᵁ ((ι₁) ''ᵁ ⊤) :
        Set ↥(pullback (f) (Spec.map (CommRingCat.ofHom (algebraMap R O))))) := by
  set b : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R O)) with hb
  set a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R A)) with ha

  have hιa : ι₁ ≫ f = a := hι₁
  let g' : pullback a b ⟶ pullback (f) b :=
    pullback.lift (pullback.fst a b ≫ ι₁) (pullback.snd a b) (by rw [Category.assoc, hιa, pullback.condition])
  have hg'fst : g' ≫ pullback.fst _ _ = pullback.fst a b ≫ ι₁ := pullback.lift_fst _ _ _
  have hg'snd : g' ≫ pullback.snd _ _ = pullback.snd a b := pullback.lift_snd _ _ _

  have sq : IsPullback (pullback.fst a b) g' (ι₁) (pullback.fst (f) b) := by
    refine IsPullback.of_bot ?_ hg'fst.symm (IsPullback.of_hasPullback (f) b)
    rw [hg'snd, hιa]
    exact IsPullback.of_hasPullback a b
  have hopen : IsOpenImmersion g' := MorphismProperty.of_isPullback sq inferInstance
  have hrange : Set.range g'.base = ((pullback.fst (f) b) ⁻¹ᵁ ((ι₁) ''ᵁ ⊤) : Set _) := by
    have e1 : g' = sq.isoPullback.hom ≫ pullback.snd (ι₁) (pullback.fst (f) b) :=
      (sq.isoPullback_hom_snd).symm
    have hs1 : Function.Surjective sq.isoPullback.hom.base := sq.isoPullback.hom.homeomorph.surjective
    rw [e1, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr hs1, Set.image_univ,
      Scheme.Pullback.range_snd]
    ext x
    simp only [Set.mem_preimage, Set.mem_range]
    constructor
    · rintro ⟨y, hy⟩; exact ⟨y, trivial, hy⟩
    · rintro ⟨y, -, hy⟩; exact ⟨y, hy⟩

  refine ⟨(pullbackSpecIso R A O).inv ≫ g', inferInstance, ?_, ?_, ?_⟩
  · rw [Category.assoc, hg'fst, ← Category.assoc, pullbackSpecIso_inv_fst]
  · rw [Category.assoc, hg'snd, pullbackSpecIso_inv_snd]
    rfl
  · have hs2 : Function.Surjective (pullbackSpecIso R A O).inv.base := (pullbackSpecIso R A O).inv.homeomorph.surjective
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr hs2, Set.image_univ, hrange]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem dominant
    (R : Type u) [CommRing R] (K : Type u) [Field K] [Algebra R K]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) (A : Type u) [CommRing A] [Algebra R A]
    (ι₁ : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion ι₁] (hι₁ : ι₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of R)) (A' : Type u) [CommRing A'] [Algebra R A']
    (ι₂ : Spec (CommRingCat.of A') ⟶ X') [IsOpenImmersion ι₂] (hι₂ : ι₂ ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap R A')))
    {L : Type v} [Field L] [Algebra K L] {L' : Type v} [Field L'] [Algebra K L']
    (ι : A → L) (ι' : A' → L')
    (C₂ : CurveModel K L')
    (e₂ : C₂.C ⟶ pullback (f') (Spec.map (CommRingCat.ofHom (algebraMap R K)))) [IsIso e₂]
    (he₂ : e₂ ≫ pullback.snd (f') (Spec.map (CommRingCat.ofHom (algebraMap R K))) = C₂.toBase)
    (hne₂ : Nonempty (Scheme.Opens.toScheme
      ((e₂ ≫ pullback.fst (f') (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ι₂) ''ᵁ ⊤))))
    (pin₂ : ∀ b : A',
      C₂.ffEquiv.symm
        (C₂.C.germToFunctionField
          ((e₂ ≫ pullback.fst (f') (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ι₂) ''ᵁ ⊤))
          (((e₂ ≫ pullback.fst (f') (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app ((ι₂) ''ᵁ ⊤)).hom
            (((ι₂).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of A')).inv b)))) = ι' b)
    (C₁ : CurveModel K L)
    (e₁ : C₁.C ⟶ pullback (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) [IsIso e₁]
    (he₁ : e₁ ≫ pullback.snd (f) (Spec.map (CommRingCat.ofHom (algebraMap R K))) = C₁.toBase)
    (hne₁ : Nonempty (Scheme.Opens.toScheme
      ((e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ι₁) ''ᵁ ⊤))))
    (pin₁ : ∀ a : A,
      C₁.ffEquiv.symm
        (C₁.C.germToFunctionField
          ((e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ι₁) ''ᵁ ⊤))
          (((e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app ((ι₁) ''ᵁ ⊤)).hom
            (((ι₁).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)))) = ι a)
    (θ : A →+* A')
    (Φ : L →ₐ[K] L') (hΦθ : ∀ a : A, Φ (ι a) = ι' (θ a))
    (πM : C₂.C ⟶ C₁.C)
    (hπM₂ : πM ≫ C₁.toBase = C₂.toBase)
    (hUU₀ : ((e₂ ≫ pullback.fst (f') (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ι₂) ''ᵁ ⊤)) ≤ πM ⁻¹ᵁ ((e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ι₁) ''ᵁ ⊤)))
    (hsecθ : ∀ a : A,
      C₂.C.presheaf.map (homOfLE hUU₀).op ((πM.app _).hom (((e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app ((ι₁) ''ᵁ ⊤)).hom (((ι₁).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)))) =
      ((e₂ ≫ pullback.fst (f') (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app ((ι₂) ''ᵁ ⊤)).hom
        (((ι₂).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of A')).inv (θ a)))) :
    πM.base (genericPoint C₂.C) = genericPoint C₁.C := by
  classical
  haveI : Nonempty (((e₂ ≫ pullback.fst (f') (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ι₂) ''ᵁ ⊤)) : Scheme.{u}) := hne₂
  haveI : Nonempty (((e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ι₁) ''ᵁ ⊤)) : Scheme.{u}) := hne₁

  obtain ⟨g₀, hg₀open, hg₀fst, hg₀snd, hg₀range⟩ := chartFin_baseChange R X f A ι₁ hι₁ K
  let G₀ := g₀ ≫ inv e₁
  haveI : IsOpenImmersion G₀ := IsOpenImmersion.comp _ _
  have hG₀ : G₀ ≫ e₁ = g₀ := by simp only [G₀, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hfac : G₀ ≫ (e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := K))) ≫
        ι₁ := by
    rw [← Category.assoc, hG₀, hg₀fst]

  have hWU₀ : G₀ ''ᵁ ⊤ = ((e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ι₁) ''ᵁ ⊤)) := by
    apply TopologicalSpace.Opens.ext
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.coe_opensRange]
    show Set.range (g₀ ≫ inv e₁).base =
      (e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))).base ⁻¹' (((ι₁) ''ᵁ ⊤) : Set (X))
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hg₀range]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have e1 := Scheme.Hom.comp_apply (inv e₁) (e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) y
      rw [IsIso.inv_hom_id_assoc] at e1
      show (e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ((inv e₁) y) ∈ (((ι₁) ''ᵁ ⊤) : Set (X))
      rw [← e1]; exact hy
    · intro hx
      refine ⟨e₁ x, ?_, ?_⟩
      · show (pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (e₁ x) ∈ (((ι₁) ''ᵁ ⊤) : Set (X))
        rw [← Scheme.Hom.comp_apply]; exact hx
      · show (inv e₁) (e₁ x) = x
        rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  have hWle : G₀ ''ᵁ ⊤ ≤ ((e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ι₁) ''ᵁ ⊤)) := hWU₀.le

  have hξU : genericPoint C₂.C ∈ ((e₂ ≫ pullback.fst (f') (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ι₂) ''ᵁ ⊤)) :=
    ((genericPoint_spec C₂.C).mem_open_set_iff (((e₂ ≫ pullback.fst (f') (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ι₂) ''ᵁ ⊤))).2).mpr
      ⟨(Classical.arbitrary (((e₂ ≫ pullback.fst (f') (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ι₂) ''ᵁ ⊤)) : Scheme.{u})).1, Set.mem_univ _, (Classical.arbitrary (((e₂ ≫ pullback.fst (f') (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ι₂) ''ᵁ ⊤)) : Scheme.{u})).2⟩
  have hξW : πM.base (genericPoint C₂.C) ∈ G₀ ''ᵁ ⊤ := by rw [hWU₀]; exact hUU₀ hξU

  refine base_genericPoint_eq_of_chart πM G₀ hξW ?_
  let ψ : A ⊗[R] K →+* C₂.C.functionField :=
    (C₂.C.presheaf.germ (πM ⁻¹ᵁ (G₀ ''ᵁ ⊤)) (genericPoint C₂.C) hξW).hom.comp
      ((πM.app (G₀ ''ᵁ ⊤)).hom.comp ((G₀.appIso ⊤).inv.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] K))).inv.hom))
  have hψapply : ∀ b, ψ b = (C₂.C.presheaf.germ (πM ⁻¹ᵁ (G₀ ''ᵁ ⊤)) (genericPoint C₂.C) hξW).hom
      ((πM.app (G₀ ''ᵁ ⊤)).hom ((G₀.appIso ⊤).inv
        ((Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] K))).inv b))) := fun _ => rfl
  suffices hψ : Function.Injective ψ from fun b hb => hψ (hb.trans (map_zero ψ).symm)

  have h1 : ∀ a, ψ (a ⊗ₜ 1) = C₂.C.germToFunctionField ((e₂ ≫ pullback.fst (f') (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ι₂) ''ᵁ ⊤))
      (((e₂ ≫ pullback.fst (f') (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app ((ι₂) ''ᵁ ⊤)).hom
        (((ι₂).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of A')).inv (θ a)))) := by
    intro a
    rw [hψapply]
    have h1 := germ_app_appIso_inv_chart πM (ι₁) G₀
      (e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := K))) hfac hWle
      (genericPoint C₂.C) hξW ((e₂ ≫ pullback.fst (f') (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ι₂) ''ᵁ ⊤)) hξU hUU₀ a
    erw [h1]
    rw [hsecθ a]

  have h2 : ∀ k : K, ψ (1 ⊗ₜ k) = baseToFunctionField C₂.toBase k := by
    intro k
    rw [hψapply]
    have hbase : G₀ ≫ C₁.toBase = g₀ ≫ pullback.snd (f) (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
      rw [← he₁, ← Category.assoc, hG₀]
    have h1k : (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] K))).inv ((1 : A) ⊗ₜ k) =
        (G₀ ≫ C₁.toBase).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv k) := by
      rw [hbase, hg₀snd]
      exact ΓSpecIso_inv_one_tmul R A K k
    rw [h1k]
    exact germ_app_appIso_inv_appTop πM G₀ C₁.toBase C₂.toBase hπM₂ (genericPoint C₂.C) hξW _

  haveI hG₀ne : Nonempty ((G₀ ''ᵁ ⊤ : C₁.C.Opens) : Scheme.{u}) := by rw [hWU₀]; infer_instance
  let ρ₁ : A ⊗[R] K →+* C₁.C.functionField :=
    (C₁.C.germToFunctionField (G₀ ''ᵁ ⊤)).hom.comp
      ((G₀.appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] K))).inv.hom)
  have hρ₁apply : ∀ b, ρ₁ b = C₁.C.germToFunctionField (G₀ ''ᵁ ⊤)
      ((G₀.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] K))).inv b)) := fun _ => rfl
  have hρ₁inj : Function.Injective ρ₁ :=
    (C₁.C.germToFunctionField_injective (G₀ ''ᵁ ⊤)).comp
      ((ConcreteCategory.bijective_of_isIso (G₀.appIso ⊤).inv).1.comp
        (ConcreteCategory.bijective_of_isIso
          (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] K))).inv).1)

  have hρ₁a : ∀ a, ρ₁ (a ⊗ₜ 1) = C₁.C.germToFunctionField ((e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ι₁) ''ᵁ ⊤))
      (((e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app ((ι₁) ''ᵁ ⊤)).hom
        (((ι₁).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) := by
    intro a
    rw [hρ₁apply]
    exact germToFunctionField_appIso_inv_chart (ι₁) G₀
      (e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := K))) hfac hWle a

  have hG₀base : G₀ ≫ C₁.toBase =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := A) (B := K)).toRingHom) := by
    rw [← hg₀snd, ← he₁, ← Category.assoc, hG₀]
  have hρ₁k : ∀ k : K, ρ₁ (1 ⊗ₜ k) = baseToFunctionField C₁.toBase k := by
    intro k
    rw [hρ₁apply]
    exact germToFunctionField_appIso_inv_base G₀ C₁.toBase
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := K)).toRingHom)
      hG₀base k

  have key : ψ = (C₂.ffEquiv.toRingHom.comp (Φ.toRingHom.comp C₁.ffEquiv.symm.toRingHom)).comp ρ₁ := by
    apply ringHom_ext_tensor
    · intro a
      rw [h1 a, RingHom.comp_apply, hρ₁a a]
      show _ = C₂.ffEquiv (Φ (C₁.ffEquiv.symm _))
      rw [pin₁ a, hΦθ a, ← pin₂ (θ a), RingEquiv.apply_symm_apply]
    · intro k
      rw [h2 k, RingHom.comp_apply, hρ₁k k]
      show _ = C₂.ffEquiv (Φ (C₁.ffEquiv.symm _))
      rw [← C₁.ffEquiv_algebraMap, RingEquiv.symm_apply_apply, AlgHom.commutes, C₂.ffEquiv_algebraMap]
  rw [key]
  exact (C₂.ffEquiv.injective.comp (Φ.toRingHom.injective.comp C₁.ffEquiv.symm.injective)).comp hρ₁inj

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem core
    (R : Type u) [CommRing R] (K : Type u) [Field K] [Algebra R K]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) (A : Type u) [CommRing A] [Algebra R A]
    (ι₁ : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion ι₁] (hι₁ : ι₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of R)) (A' : Type u) [CommRing A'] [Algebra R A']
    (ι₂ : Spec (CommRingCat.of A') ⟶ X') [IsOpenImmersion ι₂] (hι₂ : ι₂ ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap R A')))
    {L : Type v} [Field L] [Algebra K L] {L' : Type v} [Field L'] [Algebra K L']
    (ι : A → L) (ι' : A' → L')
    (C₂ : CurveModel K L')
    (e₂ : C₂.C ⟶ pullback (f') (Spec.map (CommRingCat.ofHom (algebraMap R K)))) [IsIso e₂]
    (he₂ : e₂ ≫ pullback.snd (f') (Spec.map (CommRingCat.ofHom (algebraMap R K))) = C₂.toBase)
    (hne₂ : Nonempty (Scheme.Opens.toScheme
      ((e₂ ≫ pullback.fst (f') (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ι₂) ''ᵁ ⊤))))
    (pin₂ : ∀ b : A',
      C₂.ffEquiv.symm
        (C₂.C.germToFunctionField
          ((e₂ ≫ pullback.fst (f') (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ι₂) ''ᵁ ⊤))
          (((e₂ ≫ pullback.fst (f') (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app ((ι₂) ''ᵁ ⊤)).hom
            (((ι₂).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of A')).inv b)))) = ι' b)
    (C₁ : CurveModel K L)
    (e₁ : C₁.C ⟶ pullback (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) [IsIso e₁]
    (he₁ : e₁ ≫ pullback.snd (f) (Spec.map (CommRingCat.ofHom (algebraMap R K))) = C₁.toBase)
    (hne₁ : Nonempty (Scheme.Opens.toScheme
      ((e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ι₁) ''ᵁ ⊤))))
    (pin₁ : ∀ a : A,
      C₁.ffEquiv.symm
        (C₁.C.germToFunctionField
          ((e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ ((ι₁) ''ᵁ ⊤))
          (((e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app ((ι₁) ''ᵁ ⊤)).hom
            (((ι₁).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)))) = ι a)
    (θ : A →+* A')
    (Φ : L →ₐ[K] L') (hΦθ : ∀ a : A, Φ (ι a) = ι' (θ a))
    (πX : X' ⟶ X)
    (hchart : ι₂ ≫ πX = Spec.map (CommRingCat.ofHom θ) ≫ ι₁)
    (πM : C₂.C ⟶ C₁.C)
    (hπM₁ : πM ≫ e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      e₂ ≫ pullback.fst (f') (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ πX)
    (hπM₂ : πM ≫ C₁.toBase = C₂.toBase) :
    ∃ hξ : πM.base (genericPoint C₂.C) = genericPoint C₁.C,
      fieldMap πM hξ = C₂.ffEquiv.toRingHom.comp (Φ.toRingHom.comp C₁.ffEquiv.symm.toRingHom) := by
  classical

  let V : (X').Opens := (ι₂) ''ᵁ ⊤
  let V₀ : (X).Opens := (ι₁) ''ᵁ ⊤
  let U : C₂.C.Opens := (e₂ ≫ pullback.fst (f') (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ V
  let U₀ : C₁.C.Opens := (e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ V₀

  let sec : A' → Γ(C₂.C, U) := fun b =>
    ((e₂ ≫ pullback.fst (f') (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app V).hom
      (((ι₂).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of A')).inv b))
  let sec₀ : A → Γ(C₁.C, U₀) := fun a =>
    ((e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app V₀).hom
      (((ι₁).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))
  haveI : Nonempty (U : Scheme.{u}) := hne₂
  haveI : Nonempty (U₀ : Scheme.{u}) := hne₁
  let γ : A' → C₂.C.functionField := fun b => C₂.C.germToFunctionField U (sec b)
  let γ₀ : A → C₁.C.functionField := fun a => C₁.C.germToFunctionField U₀ (sec₀ a)
  have hpin : ∀ b, C₂.ffEquiv.symm (γ b) = ι' b := fun b => pin₂ b
  have hpin₀ : ∀ a, C₁.ffEquiv.symm (γ₀ a) = ι a := fun a => pin₁ a

  have hVV₀ : V ≤ πX ⁻¹ᵁ V₀ := by
    rintro _ ⟨z, -, rfl⟩
    show (ι₂ ≫ πX).base z ∈ (V₀ : Set (X))
    rw [hchart]
    exact ⟨_, trivial, rfl⟩
  have hUU₀ : U ≤ πM ⁻¹ᵁ U₀ := by
    intro x hx
    have e := congrArg (fun f : C₂.C ⟶ X => f.base x) hπM₁
    simp only [Scheme.Hom.comp_apply] at e
    have hx' : πX.base ((pullback.fst (f') (Spec.map (CommRingCat.ofHom (algebraMap R K)))).base (e₂.base x)) ∈ V₀ := by
      apply hVV₀
      simp only [Scheme.Hom.comp_apply] at hx ⊢
      exact hx
    rw [← e] at hx'
    exact hx'

  have hXsec : ∀ a, (X').presheaf.map (homOfLE hVV₀).op
      ((πX.app V₀).hom (((ι₁).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) =
      ((ι₂).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of A')).inv (θ a)) := by
    intro a
    have h1 := AlgebraicGeometry.Scheme.appIso_hom_res_app_appIso_inv_apply πX (ι₁)
      (ι₂) (CommRingCat.ofHom θ) hchart a ⊤ hVV₀
    have h1' := congrArg ((ι₂).appIso ⊤).inv h1
    rw [Iso.hom_inv_id_apply] at h1'
    rw [h1']
    congr 1

  have hsecθ : ∀ a, C₂.C.presheaf.map (homOfLE hUU₀).op ((πM.app U₀).hom (sec₀ a)) = sec (θ a) := by
    intro a
    show C₂.C.presheaf.map (homOfLE hUU₀).op ((πM.app U₀).hom
      (((e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app V₀).hom _)) =
      ((e₂ ≫ pullback.fst (f') (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app V).hom _
    rw [← hXsec a]
    have e1 : (πM.app U₀).hom ((((e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app V₀).hom
        (((ι₁).appIso ⊤).inv ((Scheme.ΓSpecIso _).inv a)))) =
      ((πM ≫ e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))).app V₀).hom
        (((ι₁).appIso ⊤).inv ((Scheme.ΓSpecIso _).inv a)) := by
      rw [Scheme.Hom.comp_app πM (e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) V₀]
      rfl
    rw [e1]
    exact AlgebraicGeometry.Scheme.map_app_eq_of_eq_comp_comp _ e₂ (pullback.fst (f') (Spec.map (CommRingCat.ofHom (algebraMap R K)))) πX
      hπM₁ V₀ V hVV₀ _ _

  have hξ : πM.base (genericPoint C₂.C) = genericPoint C₁.C :=
    dominant R K X f A ι₁ hι₁ X' f' A' ι₂ hι₂ ι ι' C₂ e₂ he₂ hne₂ pin₂ C₁ e₁ he₁ hne₁ pin₁ θ Φ hΦθ πM hπM₂ hUU₀ hsecθ

  have hv1' : ∀ a, C₂.ffEquiv (Φ (C₁.ffEquiv.symm (γ₀ a))) = γ (θ a) := by
    intro a
    rw [hpin₀ a, hΦθ a, ← hpin (θ a), RingEquiv.apply_symm_apply]

  have hv2' : ∀ k : K, C₂.ffEquiv (Φ (C₁.ffEquiv.symm (baseToFunctionField C₁.toBase k))) =
      baseToFunctionField C₂.toBase k := by
    intro k
    rw [← C₁.ffEquiv_algebraMap k, RingEquiv.symm_apply_apply, AlgHom.commutes, C₂.ffEquiv_algebraMap]

  obtain ⟨g₀, hg₀o, hg₀fst, hg₀snd, hg₀range⟩ := chartFin_baseChange R X f A ι₁ hι₁ K
  haveI := hg₀o
  obtain ⟨G₀, hG₀o, hG₀fac, hG₀base, hG₀range⟩ : ∃ G₀ : Spec (CommRingCat.of (A ⊗[R] K)) ⟶ C₁.C,
      IsOpenImmersion G₀ ∧
      G₀ ≫ (e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := R) (A := A) (B := K))) ≫ ι₁ ∧
      G₀ ≫ C₁.toBase =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := R) (A := A) (B := K)).toRingHom) ∧
      Set.range G₀.base = (U₀ : Set C₁.C) := by
    refine ⟨g₀ ≫ inv e₁, IsOpenImmersion.comp _ _,
      by rw [Category.assoc, IsIso.inv_hom_id_assoc, hg₀fst],
      by rw [← hg₀snd, ← he₁, Category.assoc, IsIso.inv_hom_id_assoc], ?_⟩
    show Set.range (g₀ ≫ inv e₁).base =
      (e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))).base ⁻¹' (((ι₁) ''ᵁ ⊤) : Set (X))
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hg₀range]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have e1 := Scheme.Hom.comp_apply (inv e₁) (e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) y
      rw [IsIso.inv_hom_id_assoc] at e1
      show (e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ((inv e₁) y) ∈ (((ι₁) ''ᵁ ⊤) : Set (X))
      rw [← e1]; exact hy
    · intro hx
      refine ⟨e₁ x, ?_, ?_⟩
      · show (pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (e₁ x) ∈ (((ι₁) ''ᵁ ⊤) : Set (X))
        rw [← Scheme.Hom.comp_apply]; exact hx
      · show (inv e₁) (e₁ x) = x
        rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  haveI := hG₀o
  have hG₀U₀ : G₀ ''ᵁ ⊤ = U₀ := by
    apply TopologicalSpace.Opens.ext
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.coe_opensRange, hG₀range]

  have hnt : Nontrivial (CommRingCat.of (A ⊗[R] K)) := by
    haveI : Nonempty ((G₀ ''ᵁ ⊤ : C₁.C.Opens) : Scheme.{u}) := by rw [hG₀U₀]; exact hne₁
    obtain ⟨⟨z, hz⟩⟩ := (inferInstance : Nonempty ((G₀ ''ᵁ ⊤ : C₁.C.Opens) : Scheme.{u}))
    obtain ⟨q, -, -⟩ := hz
    haveI : Nonempty (Spec (CommRingCat.of (A ⊗[R] K))) := ⟨q⟩
    haveI : IsIntegral (Spec (CommRingCat.of (A ⊗[R] K))) := isIntegral_of_isOpenImmersion G₀
    haveI : IsDomain (A ⊗[R] K) :=
      MulEquiv.isDomain Γ(Spec (CommRingCat.of (A ⊗[R] K)), ⊤)
        (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[R] K))).symm.commRingCatIsoToRingEquiv.toMulEquiv
    exact (inferInstance : Nontrivial (A ⊗[R] K))
  have hG₀top : G₀ ''ᵁ ⊤ ≤ U₀ := by
    rintro _ ⟨z, -, rfl⟩
    show (G₀ ≫ e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K)))).base z ∈ (V₀ : Set (X))
    rw [hG₀fac]
    exact ⟨_, trivial, rfl⟩

  have hB : fieldMap πM hξ = C₂.ffEquiv.toRingHom.comp (Φ.toRingHom.comp C₁.ffEquiv.symm.toRingHom) :=
    fieldMap_eq_of_chart πM hξ (ι₁) G₀ (e₁ ≫ pullback.fst (f) (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := A) (B := K))) hG₀fac hG₀top
      C₁.toBase C₂.toBase hπM₂
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := A) (B := K)).toRingHom) hG₀base
      (fun χ χ' ha hk => ringHom_ext_tensor χ χ' (fun a => ha a) (fun k => hk k))
      hnt U hne₂ hUU₀ hne₁ _
      (fun a => (congrArg (fun s => C₂.C.germToFunctionField U s) (hsecθ a)).trans (hv1' a).symm)
      (fun k => (hv2' k).symm)
  exact ⟨hξ, hB⟩

end AlgebraicCurve.TwoChartIntegralModel.PlaceTransport

end

theorem coe_equivOfEq_symm_apply {K L : Type*} [Field K] [Field L] [Algebra K L] {E F : IntermediateField K L}
    (h : E = F) (x : F) : ((IntermediateField.equivOfEq h).symm x : L) = x := by
  subst h; rfl

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_fromSpecStalk_genericPoint_comp_eq_of_xHDRModelAtP_top_drModelPackageLevel.AlgebraicGeometry NeronModelInfra AlgebraicCurve P2MW.S_ModularCurve_fromSpecStalk_genericPoint_comp_eq_of_xHDRModelAtP_top_drModelPackageLevel.AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_fromSpecStalk_genericPoint_comp_eq_of_xHDRModelAtP_top_drModelPackageLevel.AlgebraicCurve.TwoChartIntegralModel.PlaceTransport"

open scoped MatrixGroups

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) [NeZero (N₀ * p)]
    (hpM : p ∣ N₀ * p) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p (N₀ * p) ⊤ hpM hj) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (hF : xHFunctionFieldBar (N₀ * p) ⊤ = modularFunctionFieldBar (N₀ * p))
    (e : IgusaScheme (N₀ * p) p ≅ XHDRLevel.X p (XHDRLevel.ΓM (N₀ * p) ⊤) hj)
    (eFin : ↥(IgusaScheme.chartAlgFin (N₀ * p) p) →+* ↥(XHDRLevel.chartAlgFin p (XHDRLevel.ΓM (N₀ * p) ⊤) hj))
    (hFin : ∀ x : ↥(IgusaScheme.chartAlgFin (N₀ * p) p),
      (((eFin x : ↥(XHDRLevel.chartAlgFin p (XHDRLevel.ΓM (N₀ * p) ⊤) hj)) : ↥(qExpFunctionFieldC ℚ (XHDRLevel.ΓM (N₀ * p) ⊤))) :
          LaurentSeries ℚ) = ((x : ↥(modularFunctionFieldFull (N₀ * p))) : LaurentSeries ℚ))
    (hbase : e.hom ≫ XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj = IgusaScheme.igusaTo (N₀ * p) p)
    (hcFin : Spec.map (CommRingCat.ofHom eFin) ≫ IgusaScheme.ιFin (N₀ * p) p = XHDRLevel.ιFin p (XHDRLevel.ΓM (N₀ * p) ⊤) hj ≫ e.inv)
    (ψ : 𝔛.Meta.C ⟶ 𝔓.Meta.C)
    (hψ₁ : ψ ≫ 𝔓.eeta ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _ ≫ e.inv)
    (hψ₂ : ψ ≫ 𝔓.Meta.toBase = 𝔛.Meta.toBase) :
    𝔛.Meta.C.fromSpecStalk (genericPoint 𝔛.Meta.C) ≫ ψ =
      Spec.map (CommRingCat.ofHom
        (𝔛.Meta.ffEquiv.toRingHom.comp
          ((IntermediateField.equivOfEq hF).toRingEquiv.symm.toRingHom.comp 𝔓.Meta.ffEquiv.symm.toRingHom))) ≫
        𝔓.Meta.C.fromSpecStalk (genericPoint 𝔓.Meta.C) := by
  haveI := 𝔛.Meta_chart_nonempty
  haveI := 𝔓.Meta_chart_nonempty
  haveI := 𝔛.eeta_iso
  haveI := 𝔓.eeta_iso

  let ι : ↥(IgusaScheme.chartAlgFin (N₀ * p) p) → ↥(modularFunctionFieldBar (N₀ * p)) := fun a =>
    𝔓.Meta.ffEquiv.symm
      (𝔓.Meta.C.germToFunctionField
        ((𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (XHDRLevel.R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * p) p) ''ᵁ ⊤))
        (((𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (XHDRLevel.R p) (AlgebraicClosure ℚ))))).app ((IgusaScheme.ιFin (N₀ * p) p) ''ᵁ ⊤)).hom
          (((IgusaScheme.ιFin (N₀ * p) p).appIso ⊤).inv
            ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * p) p))).inv a))))
  let ι' : ↥(XHDRLevel.chartAlgFin p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) → ↥(xHFunctionFieldBar (N₀ * p) ⊤) := fun b =>
    𝔛.Meta.ffEquiv.symm
      (𝔛.Meta.C.germToFunctionField
        ((𝔛.eeta ≫ pullback.fst (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (Spec.map (CommRingCat.ofHom (algebraMap (XHDRLevel.R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((XHDRLevel.ιFin p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) ''ᵁ ⊤))
        (((𝔛.eeta ≫ pullback.fst (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (Spec.map (CommRingCat.ofHom (algebraMap (XHDRLevel.R p) (AlgebraicClosure ℚ))))).app ((XHDRLevel.ιFin p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) ''ᵁ ⊤)).hom
          (((XHDRLevel.ιFin p (XHDRLevel.ΓM (N₀ * p) ⊤) hj).appIso ⊤).inv
            ((Scheme.ΓSpecIso (CommRingCat.of ↥(XHDRLevel.chartAlgFin p (XHDRLevel.ΓM (N₀ * p) ⊤) hj))).inv b))))

  let Φ : ↥(modularFunctionFieldBar (N₀ * p)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar (N₀ * p) ⊤) :=
    (IntermediateField.equivOfEq hF).symm.toAlgHom
  have hΦcoe : ∀ x : ↥(modularFunctionFieldBar (N₀ * p)), ((Φ x : ↥(xHFunctionFieldBar (N₀ * p) ⊤)) : LaurentSeries (AlgebraicClosure ℚ)) = (x : LaurentSeries (AlgebraicClosure ℚ)) := by
    intro x
    show (((IntermediateField.equivOfEq hF).symm x : ↥(xHFunctionFieldBar (N₀ * p) ⊤)) : LaurentSeries (AlgebraicClosure ℚ)) = _
    exact coe_equivOfEq_symm_apply hF x

  have hΦθ : ∀ a : ↥(IgusaScheme.chartAlgFin (N₀ * p) p), Φ (ι a) = ι' (eFin a) := fun a => by
    apply Subtype.ext
    rw [hΦcoe (ι a)]
    rw [show ((ι a : ↥(modularFunctionFieldBar (N₀ * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull (N₀ * p))) : LaurentSeries ℚ) from 𝔓.Meta_pin a,
      show ((ι' (eFin a) : ↥(xHFunctionFieldBar (N₀ * p) ⊤)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) (((eFin a : ↥(XHDRLevel.chartAlgFin p (XHDRLevel.ΓM (N₀ * p) ⊤) hj)) : ↥(qExpFunctionFieldC ℚ (XHDRLevel.ΓM (N₀ * p) ⊤))) : LaurentSeries ℚ)
        from 𝔛.Meta_pin (eFin a),
      hFin a]
  obtain ⟨hξ, hB⟩ := core (XHDRLevel.R p) (AlgebraicClosure ℚ)
    (IgusaScheme (N₀ * p) p) (IgusaScheme.igusaTo (N₀ * p) p) ↥(IgusaScheme.chartAlgFin (N₀ * p) p)
    (IgusaScheme.ιFin (N₀ * p) p) (IgusaScheme.ιFin_igusaTo (N₀ * p) p)
    (XHDRLevel.X p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) ↥(XHDRLevel.chartAlgFin p (XHDRLevel.ΓM (N₀ * p) ⊤) hj)
    (XHDRLevel.ιFin p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (TwoChartIntegralModel.ιFin_toBase _ _ _)
    ι ι'
    𝔛.Meta 𝔛.eeta 𝔛.heeta 𝔛.Meta_chart_nonempty (fun _ => rfl)
    𝔓.Meta 𝔓.eeta 𝔓.heeta 𝔓.Meta_chart_nonempty (fun _ => rfl)
    eFin Φ hΦθ e.inv hcFin.symm ψ hψ₁ hψ₂
  have hB' : fieldMap ψ hξ = 𝔛.Meta.ffEquiv.toRingHom.comp
      ((IntermediateField.equivOfEq hF).toRingEquiv.symm.toRingHom.comp 𝔓.Meta.ffEquiv.symm.toRingHom) := by
    rw [hB]; rfl
  exact fromSpecStalk_comp_eq_of_fieldMap_eq ψ hξ _ hB'

end S_ModularCurve_fromSpecStalk_genericPoint_comp_eq_of_xHDRModelAtP_top_drModelPackageLevel
end P2MW
export P2MW.S_ModularCurve_fromSpecStalk_genericPoint_comp_eq_of_xHDRModelAtP_top_drModelPackageLevel (solution)
