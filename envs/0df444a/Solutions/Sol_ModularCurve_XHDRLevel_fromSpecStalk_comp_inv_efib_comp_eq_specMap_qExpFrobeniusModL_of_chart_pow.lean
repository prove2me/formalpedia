-- Prove2me | solution 1 for ModularCurve.XHDRLevel.fromSpecStalk_comp_inv_efib_comp_eq_specMap_qExpFrobeniusModL_of_chart_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/99ea898c-53c3-554e-ab0e-1a3463ed674d

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_fromSpecStalk_comp_inv_efib_comp_eq_specMap_qExpFrobeniusModL_of_chart_pow

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open Topology
open scoped TensorProduct

universe u

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC coeffMap coeffMap_coeff coeffMap_coeffMap coeffEmb qExpand_eq_pow_of_coeff_fixed qExpFrobeniusModL coe_qExpFrobeniusModL jqModC exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC"
namespace FGMBody
p2m_open "ModularCurve"

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

end ModularCurve.FGMBody

namespace ModularCurve p2m_export "ModularCurve" "qExpFunctionFieldC coeffMap coeffMap_coeff coeffMap_coeffMap coeffEmb qExpand_eq_pow_of_coeff_fixed qExpFrobeniusModL coe_qExpFrobeniusModL jqModC exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC" namespace FGMBody end ModularCurve.FGMBody
p2m_open_scoped "ModularCurve" in
theorem ModularCurve.FGMBody.appIso_hom_res_app_appIso_inv_apply
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

p2m_open_scoped "ModularCurve" in

theorem ModularCurve.FGMBody.map_app_eq_of_eq_comp_comp {X Y Z T : Scheme.{u}} (e' : X ⟶ T) (e : X ⟶ Y) (g : Y ⟶ Z)
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

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC coeffMap coeffMap_coeff coeffMap_coeffMap coeffEmb qExpand_eq_pow_of_coeff_fixed qExpFrobeniusModL coe_qExpFrobeniusModL jqModC exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC"
namespace FGMBody
p2m_open "ModularCurve"

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
  have hA := appIso_hom_res_app_appIso_inv_apply π ι G θ hfac a ⊤ hWle
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
  have hA := appIso_hom_res_app_appIso_inv_apply π ι G θ hfac a ⊤ hWle
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

theorem chartFin_baseChange (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (O : Type u) [CommRing O] [Algebra R O] :
    ∃ g : Spec (CommRingCat.of (↥(TwoChartIntegralModel.chartAlgFin R F j) ⊗[R] O)) ⟶
        pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O))),
      IsOpenImmersion g ∧
      g ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := ↥(TwoChartIntegralModel.chartAlgFin R F j)) (B := O))) ≫
          TwoChartIntegralModel.ιFin R F j ∧
      g ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := ↥(TwoChartIntegralModel.chartAlgFin R F j)) (B := O)).toRingHom) ∧
      Set.range g.base = ((pullback.fst (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤) :
        Set ↥(pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O))))) := by
  set A : Type u := ↥(TwoChartIntegralModel.chartAlgFin R F j) with hA
  set b : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R O)) with hb
  set a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R A)) with ha

  have hιa : TwoChartIntegralModel.ιFin R F j ≫ TwoChartIntegralModel.toBase R F j = a := TwoChartIntegralModel.ιFin_toBase R F j
  let g' : pullback a b ⟶ pullback (TwoChartIntegralModel.toBase R F j) b :=
    pullback.lift (pullback.fst a b ≫ TwoChartIntegralModel.ιFin R F j) (pullback.snd a b) (by rw [Category.assoc, hιa, pullback.condition])
  have hg'fst : g' ≫ pullback.fst _ _ = pullback.fst a b ≫ TwoChartIntegralModel.ιFin R F j := pullback.lift_fst _ _ _
  have hg'snd : g' ≫ pullback.snd _ _ = pullback.snd a b := pullback.lift_snd _ _ _

  have sq : IsPullback (pullback.fst a b) g' (TwoChartIntegralModel.ιFin R F j) (pullback.fst (TwoChartIntegralModel.toBase R F j) b) := by
    refine IsPullback.of_bot ?_ hg'fst.symm (IsPullback.of_hasPullback (TwoChartIntegralModel.toBase R F j) b)
    rw [hg'snd, hιa]
    exact IsPullback.of_hasPullback a b
  have hopen : IsOpenImmersion g' := MorphismProperty.of_isPullback sq inferInstance
  have hrange : Set.range g'.base = ((pullback.fst (TwoChartIntegralModel.toBase R F j) b) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤) : Set _) := by
    have e1 : g' = sq.isoPullback.hom ≫ pullback.snd (TwoChartIntegralModel.ιFin R F j) (pullback.fst (TwoChartIntegralModel.toBase R F j) b) :=
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

section SimpleChartExt

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

theorem germToFunctionField_preimage_eq_germ (f : X ⟶ Y) (V : Y.Opens)
    [Nonempty ((f ⁻¹ᵁ V : X.Opens) : Scheme.{u})] (h : f.base (genericPoint X) ∈ V) (s : Γ(X, f ⁻¹ᵁ V)) :
    X.germToFunctionField (f ⁻¹ᵁ V) s = X.presheaf.germ (f ⁻¹ᵁ V) (genericPoint X) h s := rfl

theorem fieldMap_eq_of_chart_simple (f : X ⟶ Y) (hξ : f.base (genericPoint X) = genericPoint Y)
    {B : CommRingCat.{u}} (G : Spec B ⟶ Y) [IsOpenImmersion G] [Nonempty ((G ''ᵁ ⊤ : Y.Opens) : Scheme.{u})]
    [Nonempty ((f ⁻¹ᵁ (G ''ᵁ ⊤) : X.Opens) : Scheme.{u})]
    (ψ : (Y.functionField : Type u) →+* (X.functionField : Type u))
    (h : ∀ b : B, X.germToFunctionField (f ⁻¹ᵁ (G ''ᵁ ⊤)) (f.app (G ''ᵁ ⊤) ((G.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv b)))
        = ψ (Y.germToFunctionField (G ''ᵁ ⊤) ((G.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv b)))) :
    fieldMap f hξ = ψ := by
  have hWaff : IsAffineOpen (G ''ᵁ ⊤) := by
    rw [Scheme.Hom.image_top_eq_opensRange]; exact isAffineOpen_opensRange G
  haveI := AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen Y (G ''ᵁ ⊤) hWaff
  apply IsLocalization.ringHom_ext (nonZeroDivisors Γ(Y, G ''ᵁ ⊤))
  apply RingHom.ext
  intro s
  obtain ⟨b, rfl⟩ : ∃ b : B, (G.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv b) = s :=
    ⟨(Scheme.ΓSpecIso B).hom ((G.appIso ⊤).hom s), by rw [Iso.hom_inv_id_apply, Iso.hom_inv_id_apply]⟩
  rw [RingHom.comp_apply, RingHom.comp_apply]
  show fieldMap f hξ (Y.germToFunctionField _ _) = ψ (Y.germToFunctionField _ _)
  rw [fieldMap_germToFunctionField]
  exact h b

end SimpleChartExt

theorem isIso_spec_map_of_bijective {A : Type u} {B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Bijective f) : IsIso (Spec.map (CommRingCat.ofHom f)) := by
  haveI : IsIso (CommRingCat.ofHom f) := by
    refine ⟨⟨CommRingCat.ofHom (RingEquiv.ofBijective f hf).symm.toRingHom, ?_, ?_⟩⟩
    · ext x
      exact (RingEquiv.ofBijective f hf).symm_apply_apply x
    · ext x
      exact (RingEquiv.ofBijective f hf).apply_symm_apply x
  infer_instance

theorem ringHom_ext_tensor' {R A O L : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing O] [Algebra R O]
    [Semiring L] (χ χ' : O ⊗[R] A →+* L)
    (h1 : ∀ a, χ (1 ⊗ₜ a) = χ' (1 ⊗ₜ a)) (h2 : ∀ k, χ (k ⊗ₜ 1) = χ' (k ⊗ₜ 1)) : χ = χ' := by
  apply RingHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul k a =>
    rw [show k ⊗ₜ[R] a = (k ⊗ₜ[R] (1 : A)) * ((1 : O) ⊗ₜ[R] a) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], map_mul, map_mul, h1, h2]

theorem pow_char_apply_ratLocalizedAt (p : ℕ) [Fact p.Prime] {K : Type*} [Field K] [CharP K p]
    (f : ↥(GaloisRep.ratLocalizedAt p) →+* K) (r : ↥(GaloisRep.ratLocalizedAt p)) : (f r) ^ p = f r := by
  have hden : ((r : ℚ).den : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K p] at h
    have hc : (r : ℚ).den.Coprime p := r.2
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hc) h
    exact (Fact.out : p.Prime).one_lt.ne' this
  have hr : r * ((r : ℚ).den : ↥(GaloisRep.ratLocalizedAt p)) = ((r : ℚ).num : ↥(GaloisRep.ratLocalizedAt p)) := by
    apply Subtype.ext
    push_cast
    exact Rat.mul_den_eq_num (r : ℚ)
  have hfr : f r = ((r : ℚ).num : K) / ((r : ℚ).den : K) := by
    rw [eq_div_iff hden]
    have := congrArg f hr
    rw [map_mul, map_natCast, map_intCast] at this
    exact this
  rw [hfr, div_pow]
  conv_lhs => rw [← frobenius_def, ← frobenius_def (p := p), map_intCast, map_natCast]

end ModularCurve.FGMBody

end

p2m_open "ModularCurve P2MW.S_ModularCurve_XHDRLevel_fromSpecStalk_comp_inv_efib_comp_eq_specMap_qExpFrobeniusModL_of_chart_pow.ModularCurve ModularCurve.XHDRLevel NeronModelInfra P2MW.S_ModularCurve_XHDRLevel_fromSpecStalk_comp_inv_efib_comp_eq_specMap_qExpFrobeniusModL_of_chart_pow.ModularCurve.FGMBody"
open scoped MatrixGroups

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (Mfib : CurveModel (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))
    (efib : Mfib.C ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) [IsIso efib]
    (hefib : efib ≫ pullback.snd _ _ = Mfib.toBase)
    [Mfib_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((efib ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤)))]
    (Mfib_pin : ∀ (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) (y : LaurentSeries ↥A),
    coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)) →
    ((Mfib.ffEquiv.symm
        (Mfib.C.germToFunctionField
          ((efib ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ
            ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤))
          (((efib ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app
              ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
            (((ιFin p (ΓN p M H hpM) hj).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓN p M H hpM) hj))).inv b))))
        : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
      coeffMap (IsLocalRing.residue ↥A) y)

    (θ : fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶
      fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (hθ : θ ≫ pullback.snd _ _ = pullback.snd _ _) :
    letI := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
    ∀ (c₀ : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))) ⟶
          fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : c₀ ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj))).toRingHom) ≫ ιFin p (ΓN p M H hpM) hj)
      (_ : c₀ ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj)))))
      (φ : (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[IsLocalRing.ResidueField ↥A]
        (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))
      (_ : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
        φ ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] b) = ((1 : IsLocalRing.ResidueField ↥A) ⊗ₜ[R p] b) ^ p)
      (_ : c₀ ≫ θ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ c₀)
,
    Mfib.C.fromSpecStalk (genericPoint Mfib.C) ≫ (efib ≫ θ ≫ inv efib) =
      Spec.map (CommRingCat.ofHom (Mfib.ffEquiv.toRingHom.comp
        ((qExpFrobeniusModL (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p).toRingHom.comp Mfib.ffEquiv.symm.toRingHom))) ≫
        Mfib.C.fromSpecStalk (genericPoint Mfib.C) := by
  intro c₀ hc₀fst hc₀snd φ hφ hcθ
  classical
  letI : Algebra (R p) (IsLocalRing.ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
  haveI hUne : Nonempty (((efib ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤)) : Scheme.{0}) := Mfib_chart_nonempty

  obtain ⟨g, hgo, hgfst, hgsnd, hgrange⟩ :=
    chartFin_baseChange (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) (IsLocalRing.ResidueField ↥A)
  haveI := hgo
  let ecomm : ↥(chartAlgFin p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A) ≃ₐ[R p] (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj) := Algebra.TensorProduct.comm (R p) ↥(chartAlgFin p (ΓN p M H hpM) hj) (IsLocalRing.ResidueField ↥A)
  have hc₀g : c₀ = Spec.map (CommRingCat.ofHom ecomm.toRingHom) ≫ g := by
    apply pullback.hom_ext
    · rw [Category.assoc, hgfst, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc₀fst]
      congr 3
    · rw [Category.assoc, hgsnd, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc₀snd]
      congr 2
  haveI hiso : IsIso (Spec.map (CommRingCat.ofHom (R := ↥(chartAlgFin p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A)) (S := (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)) ecomm.toRingHom)) :=
    isIso_spec_map_of_bijective _ ecomm.bijective
  haveI hc₀o : IsOpenImmersion c₀ := by rw [hc₀g]; exact IsOpenImmersion.comp _ _
  have hc₀range : Set.range c₀.base = ((pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) ⁻¹ᵁ ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤) : Set _)) := by
    have hs : Function.Surjective (Spec.map (CommRingCat.ofHom (R := ↥(chartAlgFin p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A)) (S := (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)) ecomm.toRingHom)).base :=
      (Spec.map (CommRingCat.ofHom (R := ↥(chartAlgFin p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A)) (S := (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)) ecomm.toRingHom)).homeomorph.surjective
    rw [hc₀g, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr hs, Set.image_univ, hgrange]

  obtain ⟨G, hGdef⟩ : ∃ G : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))) ⟶ Mfib.C, G = c₀ ≫ inv efib := ⟨_, rfl⟩
  haveI hGo : IsOpenImmersion G := by rw [hGdef]; exact IsOpenImmersion.comp _ _
  have hGU : G ''ᵁ ⊤ = ((efib ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤)) := by
    apply TopologicalSpace.Opens.ext
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.coe_opensRange]
    rw [hGdef]
    show Set.range (c₀ ≫ inv efib).base = (efib ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base ⁻¹' (((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤) : Set (X p (ΓN p M H hpM) hj))
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hc₀range]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have e1 := Scheme.Hom.comp_apply (inv efib) (efib ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) y
      rw [IsIso.inv_hom_id_assoc] at e1
      show (efib ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ((inv efib) y) ∈ (((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤) : Set (X p (ΓN p M H hpM) hj))
      rw [← e1]; exact hy
    · intro hx
      refine ⟨efib x, ?_, ?_⟩
      · show pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) (efib x) ∈ (((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤) : Set (X p (ΓN p M H hpM) hj))
        rw [← Scheme.Hom.comp_apply]; exact hx
      · show (inv efib) (efib x) = x
        rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  haveI hGne : Nonempty ((G ''ᵁ ⊤ : Mfib.C.Opens) : Scheme.{0}) := by rw [hGU]; exact hUne
  obtain ⟨πM, hπMdef⟩ : ∃ πM : Mfib.C ⟶ Mfib.C, πM = efib ≫ θ ≫ inv efib := ⟨_, rfl⟩
  have hGπ : G ≫ πM = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ G := by
    rw [hGdef, hπMdef, Category.assoc, IsIso.inv_hom_id_assoc, ← Category.assoc, hcθ, Category.assoc]
  have hGle : G ''ᵁ ⊤ ≤ πM ⁻¹ᵁ (G ''ᵁ ⊤) := by
    rintro _ ⟨z, -, rfl⟩
    show (G ≫ πM).base z ∈ ((G ''ᵁ ⊤ : Mfib.C.Opens) : Set Mfib.C)
    rw [hGπ]
    exact ⟨_, trivial, rfl⟩
  have hGfac : G ≫ (efib ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj))).toRingHom) ≫
        ιFin p (ΓN p M H hpM) hj := by
    rw [hGdef, Category.assoc, IsIso.inv_hom_id_assoc, hc₀fst]
  have hGbase : G ≫ Mfib.toBase =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj)))) := by
    rw [hGdef, Category.assoc, ← hefib, IsIso.inv_hom_id_assoc, hc₀snd]

  obtain ⟨ρ₁, hρ₁apply⟩ : ∃ ρ₁ : (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj) →+* Mfib.C.functionField, ∀ z, ρ₁ z = Mfib.C.germToFunctionField (G ''ᵁ ⊤)
      ((G.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)))).inv z)) :=
    ⟨(Mfib.C.germToFunctionField (G ''ᵁ ⊤)).hom.comp
      ((G.appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)))).inv.hom), fun _ => rfl⟩
  have hρ₁inj : Function.Injective ρ₁ := by
    intro x y hxy
    rw [hρ₁apply, hρ₁apply] at hxy
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)))).inv).1
      ((ConcreteCategory.bijective_of_isIso (G.appIso ⊤).inv).1 (Mfib.C.germToFunctionField_injective _ hxy))

  let rd : ↥(chartAlgFin p (ΓN p M H hpM) hj) → Mfib.C.functionField := fun b =>
    Mfib.C.germToFunctionField ((efib ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤))
      (((efib ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom (((ιFin p (ΓN p M H hpM) hj).appIso ⊤).inv
        ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓN p M H hpM) hj))).inv b)))
  have hρ₁b : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj), ρ₁ (1 ⊗ₜ b) = rd b := by
    intro b
    rw [hρ₁apply]
    exact germToFunctionField_appIso_inv_chart (ιFin p (ΓN p M H hpM) hj) G (efib ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj))).toRingHom) hGfac hGU.le b
  have hρ₁k : ∀ k : IsLocalRing.ResidueField ↥A, ρ₁ (k ⊗ₜ 1) = baseToFunctionField Mfib.toBase k := by
    intro k
    rw [hρ₁apply]
    exact germToFunctionField_appIso_inv_base G Mfib.toBase
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj)))) hGbase k

  have hfrob : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj), qExpFrobeniusModL (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p (Mfib.ffEquiv.symm (rd b)) = (Mfib.ffEquiv.symm (rd b)) ^ p := by
    intro b
    obtain ⟨y₀, hy₀⟩ := (ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
      (ΓN p M H hpM) p (jAt (ΓN p M H hpM) hj) (coe_jAt _ hj)).1 b
    have hy : coeffMap A.subtype (coeffMap ρ y₀) =
        coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)) := by
      rw [coeffMap_coeffMap, hρ, ← hy₀]
      show _ = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (coeffMap (algebraMap (R p) ℚ) y₀)
      rw [coeffMap_coeffMap, ← IsScalarTower.algebraMap_eq]
    have hpin := Mfib_pin b (coeffMap ρ y₀) hy
    apply Subtype.ext
    rw [coe_qExpFrobeniusModL, SubmonoidClass.coe_pow, hpin, coeffMap_coeffMap]
    refine qExpand_eq_pow_of_coeff_fixed (IsLocalRing.ResidueField ↥A) p _ (fun k => ?_)
    rw [coeffMap_coeff]
    exact pow_char_apply_ratLocalizedAt p ((IsLocalRing.residue ↥A).comp ρ) (y₀.coeff k)

  let Fc : Mfib.C.functionField →+* Mfib.C.functionField :=
    Mfib.ffEquiv.toRingHom.comp ((qExpFrobeniusModL (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p).toRingHom.comp Mfib.ffEquiv.symm.toRingHom)
  have hFc_rd : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj), Fc (rd b) = (rd b) ^ p := by
    intro b
    show Mfib.ffEquiv (qExpFrobeniusModL (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p (Mfib.ffEquiv.symm (rd b))) = rd b ^ p
    rw [hfrob, map_pow, RingEquiv.apply_symm_apply]
  have hFc_k : ∀ k : IsLocalRing.ResidueField ↥A, Fc (baseToFunctionField Mfib.toBase k) = baseToFunctionField Mfib.toBase k := by
    intro k
    show Mfib.ffEquiv (qExpFrobeniusModL (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p (Mfib.ffEquiv.symm (baseToFunctionField Mfib.toBase k))) = _
    rw [← Mfib.ffEquiv_algebraMap, RingEquiv.symm_apply_apply, AlgHom.commutes]

  have hξG : genericPoint Mfib.C ∈ G ''ᵁ ⊤ := by
    rw [hGU]
    exact ((genericPoint_spec Mfib.C).mem_open_set_iff (((efib ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤))).2).mpr
      ⟨(Classical.arbitrary (((efib ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤)) : Scheme.{0})).1, Set.mem_univ _, (Classical.arbitrary (((efib ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤)) : Scheme.{0})).2⟩
  have hξW : πM.base (genericPoint Mfib.C) ∈ G ''ᵁ ⊤ := hGle hξG
  haveI hπne : Nonempty ((πM ⁻¹ᵁ (G ''ᵁ ⊤) : Mfib.C.Opens) : Scheme.{0}) := ⟨⟨_, hξW⟩⟩
  obtain ⟨ψ, hψapply⟩ : ∃ ψ : (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj) →+* Mfib.C.functionField, ∀ z, ψ z =
      Mfib.C.germToFunctionField (πM ⁻¹ᵁ (G ''ᵁ ⊤))
        ((πM.app (G ''ᵁ ⊤)).hom ((G.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)))).inv z))) :=
    ⟨(Mfib.C.germToFunctionField (πM ⁻¹ᵁ (G ''ᵁ ⊤))).hom.comp
      ((πM.app (G ''ᵁ ⊤)).hom.comp ((G.appIso ⊤).inv.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj)))).inv.hom)), fun _ => rfl⟩
  have hψρ : ∀ z, ψ z = ρ₁ (φ z) := by
    intro z
    have h := germToFunctionField_appIso_inv_chart G G πM (CommRingCat.ofHom φ.toRingHom) hGπ hGle z
    simp only [CommRingCat.hom_ofHom] at h
    rw [hψapply, hρ₁apply]
    exact h.symm
  have key : ψ = Fc.comp ρ₁ := by
    apply ringHom_ext_tensor'
    · intro b
      show ψ _ = Fc (ρ₁ _)
      rw [hψρ, hφ, map_pow, hρ₁b, hFc_rd]
    · intro k
      show ψ _ = Fc (ρ₁ _)
      have : φ (k ⊗ₜ[R p] (1 : ↥(chartAlgFin p (ΓN p M H hpM) hj))) = k ⊗ₜ 1 := φ.commutes k
      rw [hψρ, this, hρ₁k, hFc_k]

  have hξ : πM.base (genericPoint Mfib.C) = genericPoint Mfib.C := by
    refine base_genericPoint_eq_of_chart πM G hξW ?_
    intro z hz
    have h1 : ψ z = 0 := by rw [hψapply, germToFunctionField_preimage_eq_germ πM (G ''ᵁ ⊤) hξW]; exact hz
    rw [key] at h1
    change Fc (ρ₁ z) = 0 at h1
    have h2 : ρ₁ z = 0 := Fc.injective (by rw [h1, map_zero])
    exact hρ₁inj (by rw [h2, map_zero])

  have hB : fieldMap πM hξ = Fc := by
    refine fieldMap_eq_of_chart_simple πM hξ G Fc (fun b => ?_)
    rw [← hψapply b, ← hρ₁apply b]
    exact RingHom.congr_fun key b

  rw [← hπMdef]
  exact fromSpecStalk_comp_eq_of_fieldMap_eq πM hξ Fc hB

#print axioms solution

end S_ModularCurve_XHDRLevel_fromSpecStalk_comp_inv_efib_comp_eq_specMap_qExpFrobeniusModL_of_chart_pow
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_fromSpecStalk_comp_inv_efib_comp_eq_specMap_qExpFrobeniusModL_of_chart_pow (solution)
