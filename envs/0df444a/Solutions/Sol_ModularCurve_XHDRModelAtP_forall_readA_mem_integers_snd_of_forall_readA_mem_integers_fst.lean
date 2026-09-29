-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.forall_readA_mem_integers_snd_of_forall_readA_mem_integers_fst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/f37b212d-4009-5a1b-9458-5a097d1e6c87

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_XHDRModelAtP_algEquiv_eq_of_forall_pointEquivPlace_eq_ofAlgAut_smul_of_comp_w_eq
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_forall_readA_mem_integers_snd_of_forall_readA_mem_integers_fst
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve TopCat
open scoped Pointwise

universe u v w

namespace ZeroTwinH

section Generic

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
variable (Mdl : CurveModel K L) (ψ : Mdl.C ⟶ Mdl.C) [IsIso ψ]

theorem base_genericPoint : ψ.base (genericPoint Mdl.C) = genericPoint Mdl.C :=
  genericPoint_eq_of_isOpenImmersion ψ

theorem inseparable_genericPoint : Inseparable (genericPoint Mdl.C) (ψ.base (genericPoint Mdl.C)) := by
  rw [base_genericPoint]

noncomputable def ffIso : Mdl.C.functionField ≅ Mdl.C.functionField :=
  Mdl.C.presheaf.stalkCongr (inseparable_genericPoint Mdl ψ) ≪≫ asIso (ψ.stalkMap (genericPoint Mdl.C))

theorem ffIso_hom : (ffIso Mdl ψ).hom =
    Mdl.C.presheaf.stalkSpecializes (inseparable_genericPoint Mdl ψ).ge ≫ ψ.stalkMap (genericPoint Mdl.C) := rfl

theorem algebraMap_comp_ffIso (x' : Mdl.C) :
    (Mdl.C.presheaf.stalkSpecializes (genericPoint_specializes (ψ.base x'))) ≫ (ffIso Mdl ψ).hom =
      ψ.stalkMap x' ≫ Mdl.C.presheaf.stalkSpecializes (genericPoint_specializes x') := by
  rw [ffIso_hom, ← Category.assoc, Presheaf.stalkSpecializes_comp]
  exact Scheme.Hom.stalkSpecializes_stalkMap ψ _ _ (genericPoint_specializes x')

noncomputable def theta : L ≃+* L :=
  Mdl.ffEquiv.trans ((ffIso Mdl ψ).commRingCatIsoToRingEquiv.trans Mdl.ffEquiv.symm)

theorem theta_apply (f : L) : theta Mdl ψ f = Mdl.ffEquiv.symm ((ffIso Mdl ψ).hom (Mdl.ffEquiv f)) := rfl

variable (hψ : ψ ≫ Mdl.toBase = Mdl.toBase)

include hψ in
theorem appTop_comp_app_top : Mdl.toBase.appTop ≫ ψ.app ⊤ = Mdl.toBase.appTop := by
  have e := Scheme.Hom.congr_app hψ ⊤
  rw [Scheme.Hom.comp_app] at e
  simpa using e

include hψ in
theorem appTop_germ_ffIso :
    Mdl.toBase.appTop ≫ Mdl.C.presheaf.germ ⊤ (genericPoint Mdl.C) trivial ≫ (ffIso Mdl ψ).hom =
      Mdl.toBase.appTop ≫ Mdl.C.presheaf.germ ⊤ (genericPoint Mdl.C) trivial := by
  simp only [ffIso_hom, Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]
  rw [← Category.assoc, appTop_comp_app_top Mdl ψ hψ]
  rfl

include hψ in
theorem ffIso_baseToFunctionField (a : K) :
    (ffIso Mdl ψ).hom (baseToFunctionField Mdl.toBase a) = baseToFunctionField Mdl.toBase a := by
  have h := appTop_germ_ffIso Mdl ψ hψ
  have := CommRingCat.hom_ext_iff.mp h
  have := congrFun (congrArg DFunLike.coe this) ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)
  simpa only [baseToFunctionField, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using this

include hψ in
theorem theta_algebraMap (a : K) : theta Mdl ψ (algebraMap K L a) = algebraMap K L a := by
  rw [theta_apply, Mdl.ffEquiv_algebraMap, ffIso_baseToFunctionField Mdl ψ hψ, ← Mdl.ffEquiv_algebraMap,
    RingEquiv.symm_apply_apply]

noncomputable def thetaAlg : L ≃ₐ[K] L :=
  AlgEquiv.ofRingEquiv (f := theta Mdl ψ) (theta_algebraMap Mdl ψ hψ)

theorem thetaAlg_apply (f : L) : thetaAlg Mdl ψ hψ f = theta Mdl ψ f := rfl

theorem genericPoint_mem_preimage {V : Mdl.C.Opens} (hV : genericPoint Mdl.C ∈ V) : genericPoint Mdl.C ∈ ψ ⁻¹ᵁ V :=
  (inseparable_genericPoint Mdl ψ).specializes'.mem_open V.isOpen hV

theorem germ_ffIso {V : Mdl.C.Opens} (hV : genericPoint Mdl.C ∈ V) (hV' : genericPoint Mdl.C ∈ ψ ⁻¹ᵁ V) :
    Mdl.C.presheaf.germ V (genericPoint Mdl.C) hV ≫ (ffIso Mdl ψ).hom =
      ψ.app V ≫ Mdl.C.presheaf.germ (ψ ⁻¹ᵁ V) (genericPoint Mdl.C) hV' := by
  simp only [ffIso_hom, Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]

theorem algebraMap_stalk_eq (x : Mdl.C) :
    algebraMap (Mdl.C.presheaf.stalk x) Mdl.C.functionField =
      (Mdl.C.presheaf.stalkSpecializes (genericPoint_specializes x)).hom := rfl

theorem range_algebraMap_stalk (x' : Mdl.C) :
    (algebraMap (Mdl.C.presheaf.stalk x') Mdl.C.functionField).range =
      Subring.map (ffIso Mdl ψ).hom.hom (algebraMap (Mdl.C.presheaf.stalk (ψ.base x')) Mdl.C.functionField).range := by
  have hnat := CommRingCat.hom_ext_iff.mp (algebraMap_comp_ffIso Mdl ψ x')
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp] at hnat
  rw [algebraMap_stalk_eq, algebraMap_stalk_eq, RingHom.map_range, hnat, ← RingHom.map_range]
  have hsurj : Function.Surjective (ψ.stalkMap x').hom :=
    (asIso (ψ.stalkMap x')).commRingCatIsoToRingEquiv.surjective
  rw [RingHom.range_eq_top.mpr hsurj, ← RingHom.range_eq_map]

theorem placeOfPoint_eq_smul (x' x : closedPoints Mdl.C) (h : ψ.base x'.1 = x.1) :
    Mdl.placeOfPoint x' = SemilinearAut.ofAlgAut (thetaAlg Mdl ψ hψ) • Mdl.placeOfPoint x := by
  apply Place.ext
  apply SetLike.coe_injective
  rw [SemilinearAut.smul_toValuationSubring, ValuationSubring.coe_pointwise_smul]
  have h' := Mdl.range_stalk_eq x'
  have hx := Mdl.range_stalk_eq x
  rw [← RingHom.map_range, range_algebraMap_stalk Mdl ψ x'.1, h] at h'
  rw [← RingHom.map_range] at hx
  have e1 : ((Mdl.placeOfPoint x').toValuationSubring : Set L) =
      (Mdl.ffEquiv.symm : Mdl.C.functionField ≃+* L).toRingHom ''
        ((ffIso Mdl ψ).hom.hom '' (algebraMap (Mdl.C.presheaf.stalk x.1) Mdl.C.functionField).range) := by
    have := congrArg (fun S : Subring L => (S : Set L)) h'
    simp only [Subring.coe_map] at this
    exact this.symm
  have e2 : ((Mdl.placeOfPoint x).toValuationSubring : Set L) =
      (Mdl.ffEquiv.symm : Mdl.C.functionField ≃+* L).toRingHom ''
        (algebraMap (Mdl.C.presheaf.stalk x.1) Mdl.C.functionField).range := by
    have := congrArg (fun S : Subring L => (S : Set L)) hx
    simp only [Subring.coe_map] at this
    exact this.symm
  rw [e1, e2, Set.image_image, ← Set.image_smul, Set.image_image]
  refine Set.image_congr' fun f => ?_
  show Mdl.ffEquiv.symm ((ffIso Mdl ψ).hom.hom f) = (thetaAlg Mdl ψ hψ) (Mdl.ffEquiv.symm f)
  rw [thetaAlg_apply, theta_apply, RingEquiv.apply_symm_apply]

theorem pointEquivPlace_eq_smul [IsAlgClosed K]
    (y y' : {q : Spec (CommRingCat.of K) ⟶ Mdl.C // q ≫ Mdl.toBase = 𝟙 _}) (h : y'.1 ≫ ψ = y.1) :
    Mdl.pointEquivPlace y' = SemilinearAut.ofAlgAut (thetaAlg Mdl ψ hψ) • Mdl.pointEquivPlace y := by
  rw [CurveModel.pointEquivPlace_apply, CurveModel.pointEquivPlace_apply]
  apply placeOfPoint_eq_smul
  have := congrArg (fun f : Spec (CommRingCat.of K) ⟶ Mdl.C => f.base (IsLocalRing.closedPoint K)) h
  simpa using this

end Generic

theorem app_germ_congr {X Y : Scheme.{u}} {f f' : X ⟶ Y} (e : f = f') (U : Y.Opens) (x : X)
    (hx : x ∈ f ⁻¹ᵁ U) (hx' : x ∈ f' ⁻¹ᵁ U) :
    f.app U ≫ X.presheaf.germ (f ⁻¹ᵁ U) x hx = f'.app U ≫ X.presheaf.germ (f' ⁻¹ᵁ U) x hx' := by
  subst e; rfl

theorem app_app_germ_congr {X Y Y' Z : Scheme.{u}} {a : X ⟶ Y} {b : Y ⟶ Z} {a' : X ⟶ Y'} {b' : Y' ⟶ Z}
    (e : a ≫ b = a' ≫ b') (U : Z.Opens) (x : X) (hx : x ∈ a ⁻¹ᵁ (b ⁻¹ᵁ U)) (hx' : x ∈ a' ⁻¹ᵁ (b' ⁻¹ᵁ U)) :
    b.app U ≫ a.app (b ⁻¹ᵁ U) ≫ X.presheaf.germ (a ⁻¹ᵁ (b ⁻¹ᵁ U)) x hx =
      b'.app U ≫ a'.app (b' ⁻¹ᵁ U) ≫ X.presheaf.germ (a' ⁻¹ᵁ (b' ⁻¹ᵁ U)) x hx' := by
  have h := app_germ_congr e U x hx hx'
  simp only [Scheme.Hom.comp_app] at h
  exact h

section Transport

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

theorem transport
    (Mdl : CurveModel K L) (ψ : Mdl.C ⟶ Mdl.C) [IsIso ψ]
    (θ : L → L) (hθ : ∀ f, θ f = Mdl.ffEquiv.symm ((ffIso Mdl ψ).hom (Mdl.ffEquiv f)))
    {Y XQ D : Scheme.{u}} [IsIntegral D]
    (e : Mdl.C ⟶ XQ) (q : XQ ⟶ Y) (wA : Y ⟶ Y)
    (hcomm : ψ ≫ e ≫ q = e ≫ q ≫ wA)
    (c0 c1 : D ⟶ Y) (hc : c0 ≫ wA = c1)
    {Fb : Type w} [NonAssocSemiring Fb] (rd : D.functionField → Fb)
    (O₁ O₂ : ValuationSubring L) (res₁ : O₁ →+* Fb) (res₂ : O₂ →+* Fb)
    (hmem : ∀ f, f ∈ O₂ ↔ θ f ∈ O₁)
    (hres : ∀ f (h : f ∈ O₂), res₂ ⟨f, h⟩ = res₁ ⟨θ f, (hmem f).mp h⟩)
    (H1 : ∀ (V : Y.Opens) (hgenV : genericPoint Mdl.C ∈ e ⁻¹ᵁ (q ⁻¹ᵁ V)) (g : Γ(Y, V)),
      ∀ hi : c0.base (genericPoint D) ∈ V,
        ∃ h₁ : (Mdl.ffEquiv.symm.toRingHom.comp
            ((Mdl.C.presheaf.germ (e ⁻¹ᵁ (q ⁻¹ᵁ V)) (genericPoint Mdl.C) hgenV).hom.comp
              ((e.app (q ⁻¹ᵁ V)).hom.comp (q.app V).hom))) g ∈ O₁,
          (∃ hg₀ : genericPoint D ∈ c0 ⁻¹ᵁ V,
            res₁ ⟨_, h₁⟩ = rd ((D.presheaf.germ (c0 ⁻¹ᵁ V) (genericPoint D) hg₀) ((c0.app V).hom g))) ∧
          (IsUnit (Y.presheaf.germ V _ hi g) → res₁ ⟨_, h₁⟩ ≠ 0))
    (V : Y.Opens) (hgenV : genericPoint Mdl.C ∈ e ⁻¹ᵁ (q ⁻¹ᵁ V)) (g : Γ(Y, V))
    (h0 : c1.base (genericPoint D) ∈ V) :
    ∃ h₂ : (Mdl.ffEquiv.symm.toRingHom.comp
        ((Mdl.C.presheaf.germ (e ⁻¹ᵁ (q ⁻¹ᵁ V)) (genericPoint Mdl.C) hgenV).hom.comp
          ((e.app (q ⁻¹ᵁ V)).hom.comp (q.app V).hom))) g ∈ O₂,
      (∃ hg₁ : genericPoint D ∈ c1 ⁻¹ᵁ V,
        res₂ ⟨_, h₂⟩ = rd ((D.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint D) hg₁) ((c1.app V).hom g))) ∧
      (IsUnit (Y.presheaf.germ V _ h0 g) → res₂ ⟨_, h₂⟩ ≠ 0) := by

  have hgen_ψ : ψ.base (genericPoint Mdl.C) = genericPoint Mdl.C := base_genericPoint Mdl ψ
  have hgenV' : genericPoint Mdl.C ∈ e ⁻¹ᵁ (q ⁻¹ᵁ (wA ⁻¹ᵁ V)) := by
    have h := congrArg (fun f : Mdl.C ⟶ Y => f.base (genericPoint Mdl.C)) hcomm
    simp only [Scheme.Hom.comp_apply] at h
    rw [hgen_ψ] at h
    show wA.base (q.base (e.base (genericPoint Mdl.C))) ∈ V
    rw [← h]
    exact hgenV

  have hξ : wA.base (c0.base (genericPoint D)) = c1.base (genericPoint D) := by
    rw [← hc, Scheme.Hom.comp_apply]
  have hi' : c0.base (genericPoint D) ∈ wA ⁻¹ᵁ V := by
    show wA.base _ ∈ V
    rw [hξ]
    exact h0
  obtain ⟨h₁, ⟨hg₀, hres₁⟩, hunit⟩ := H1 (wA ⁻¹ᵁ V) hgenV' ((wA.app V).hom g) hi'

  have hgenVc : genericPoint Mdl.C ∈ (e ≫ q) ⁻¹ᵁ V := hgenV
  have hgenVc' : genericPoint Mdl.C ∈ (e ≫ q) ⁻¹ᵁ (wA ⁻¹ᵁ V) := hgenV'
  have h3 : genericPoint Mdl.C ∈ ψ ⁻¹ᵁ ((e ≫ q) ⁻¹ᵁ V) := genericPoint_mem_preimage Mdl ψ hgenVc
  have hcomm' : ψ ≫ (e ≫ q) = (e ≫ q) ≫ wA := by simpa only [Category.assoc] using hcomm
  have key : (e ≫ q).app V ≫ Mdl.C.presheaf.germ ((e ≫ q) ⁻¹ᵁ V) (genericPoint Mdl.C) hgenVc ≫ (ffIso Mdl ψ).hom =
      wA.app V ≫ (e ≫ q).app (wA ⁻¹ᵁ V) ≫ Mdl.C.presheaf.germ ((e ≫ q) ⁻¹ᵁ (wA ⁻¹ᵁ V)) (genericPoint Mdl.C) hgenVc' := by
    rw [germ_ffIso Mdl ψ hgenVc h3]
    exact app_app_germ_congr hcomm' V (genericPoint Mdl.C) h3 hgenVc'
  have K : (Mdl.ffEquiv.symm.toRingHom.comp
        ((Mdl.C.presheaf.germ (e ⁻¹ᵁ (q ⁻¹ᵁ (wA ⁻¹ᵁ V))) (genericPoint Mdl.C) hgenV').hom.comp
          ((e.app (q ⁻¹ᵁ (wA ⁻¹ᵁ V))).hom.comp (q.app (wA ⁻¹ᵁ V)).hom))) ((wA.app V).hom g) =
      θ ((Mdl.ffEquiv.symm.toRingHom.comp
        ((Mdl.C.presheaf.germ (e ⁻¹ᵁ (q ⁻¹ᵁ V)) (genericPoint Mdl.C) hgenV).hom.comp
          ((e.app (q ⁻¹ᵁ V)).hom.comp (q.app V).hom))) g) := by
    rw [hθ]
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]
    refine congrArg Mdl.ffEquiv.symm ?_
    have e1 := congrFun (congrArg DFunLike.coe (CommRingCat.hom_ext_iff.mp key)) g
    simp only [Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at e1
    exact e1.symm
  have hsub : ∀ (x y : L) (hx : x ∈ O₁) (hy : y ∈ O₁), x = y → res₁ ⟨x, hx⟩ = res₁ ⟨y, hy⟩ := by
    rintro x y hx hy rfl; rfl
  refine ⟨(hmem _).mpr ?_, ⟨h0, ?_⟩, ?_⟩
  · rw [← K]; exact h₁
  · rw [hres, hsub _ _ _ h₁ K.symm, hres₁]
    refine congrArg rd ?_
    have h4 := app_germ_congr hc V (genericPoint D) hg₀ h0
    have e2 := congrFun (congrArg DFunLike.coe (CommRingCat.hom_ext_iff.mp h4)) g
    simp only [Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at e2
    exact e2
  · intro hu
    rw [hres, hsub _ _ _ h₁ K.symm]
    apply hunit
    have hu' : IsUnit ((Y.presheaf.germ V (wA.base (c0.base (genericPoint D))) hi') g) := by
      have aux : ∀ (x : Y) (hx : x ∈ V), x = c1.base (genericPoint D) → IsUnit ((Y.presheaf.germ V x hx) g) := by
        rintro x hx rfl; exact hu
      exact aux _ hi' hξ
    rw [← Scheme.Hom.germ_stalkMap_apply wA V (c0.base (genericPoint D)) hi' g]
    exact hu'.map _

end Transport

end ZeroTwinH

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial

open scoped MatrixGroups

open ZeroTwinH in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    letI bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl
    (∀ (V : (XO (ΓM M H) hj ρ).Opens) (hgenV : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V))
      (g : Γ(XO (ΓM M H) hj ρ, V)),
      letI readA : Γ(XO (ΓM M H) hj ρ, V) →+* ↥(xHFunctionFieldBar M H) :=
        (𝔛.Meta).ffEquiv.symm.toRingHom.comp
          (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V)) (genericPoint (𝔛.Meta).C) hgenV).hom.comp
            ((𝔛.eeta.app (prA ⁻¹ᵁ V)).hom.comp (prA.app V).hom))
      (∀ hi : 𝔛.ξinf A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl ∈ V,
        ∃ h₁ : readA g ∈ Rpd.R₁.integers,
          (letI := (𝔛.Mfib A hA ρ hρ).isIntegral
           ∃ hg₀ : genericPoint (𝔛.Mfib A hA ρ hρ).C ∈ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA) ⁻¹ᵁ V,
            Rpd.R₁.residue ⟨readA g, h₁⟩ =
              (𝔛.Mfib A hA ρ hρ).ffEquiv.symm
                (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA) ⁻¹ᵁ V) (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg₀)
                  (((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA).app V).hom g))) ∧
          (IsUnit ((XO (ΓM M H) hj ρ).presheaf.germ V _ hi g) → Rpd.R₁.residue ⟨readA g, h₁⟩ ≠ 0))) →
    ∀ (V : (XO (ΓM M H) hj ρ).Opens) (hgenV : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V))
      (g : Γ(XO (ΓM M H) hj ρ, V)),
    letI readA : Γ(XO (ΓM M H) hj ρ, V) →+* ↥(xHFunctionFieldBar M H) :=
      (𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V)) (genericPoint (𝔛.Meta).C) hgenV).hom.comp
          ((𝔛.eeta.app (prA ⁻¹ᵁ V)).hom.comp (prA.app V).hom))
    (∀ h0 : 𝔛.ξzero A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl ∈ V,
      ∃ h₂ : readA g ∈ Rpd.R₂.integers,
        (letI := (𝔛.Mfib A hA ρ hρ).isIntegral
         ∃ hg₁ : genericPoint (𝔛.Mfib A hA ρ hρ).C ∈ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA) ⁻¹ᵁ V,
          Rpd.R₂.residue ⟨readA g, h₂⟩ =
            (𝔛.Mfib A hA ρ hρ).ffEquiv.symm
              (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA) ⁻¹ᵁ V) (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg₁)
                (((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA).app V).hom g))) ∧
        (IsUnit ((XO (ΓM M H) hj ρ).presheaf.germ V _ h0 g) → Rpd.R₂.residue ⟨readA g, h₂⟩ ≠ 0)) := by

  obtain ⟨hco, hft⟩ := ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := hft
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := hco

  set XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) with hXQ
  have hwinv : 𝔛.w.inv ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj := by
    rw [Iso.inv_comp_eq, 𝔛.w_over]
  let wbar : XQ ⟶ XQ := pullback.lift (pullback.fst _ _ ≫ 𝔛.w.hom) (pullback.snd _ _)
    (by rw [Category.assoc, 𝔛.w_over, pullback.condition])
  let wbarinv : XQ ⟶ XQ := pullback.lift (pullback.fst _ _ ≫ 𝔛.w.inv) (pullback.snd _ _)
    (by rw [Category.assoc, hwinv, pullback.condition])
  have hwbar_fst : wbar ≫ pullback.fst _ _ = pullback.fst _ _ ≫ 𝔛.w.hom := pullback.lift_fst _ _ _
  have hwbar_snd : wbar ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hwbarinv_fst : wbarinv ≫ pullback.fst _ _ = pullback.fst _ _ ≫ 𝔛.w.inv := pullback.lift_fst _ _ _
  have hwbarinv_snd : wbarinv ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  haveI : IsIso wbar := ⟨⟨wbarinv, by
      apply pullback.hom_ext
      · rw [Category.assoc, hwbarinv_fst, ← Category.assoc, hwbar_fst, Category.assoc, Iso.hom_inv_id, Category.comp_id,
          Category.id_comp]
      · rw [Category.assoc, hwbarinv_snd, hwbar_snd, Category.id_comp], by
      apply pullback.hom_ext
      · rw [Category.assoc, hwbar_fst, ← Category.assoc, hwbarinv_fst, Category.assoc, Iso.inv_hom_id, Category.comp_id,
          Category.id_comp]
      · rw [Category.assoc, hwbar_snd, hwbarinv_snd, Category.id_comp]⟩⟩
  let ψ : 𝔛.Meta.C ⟶ 𝔛.Meta.C := 𝔛.eeta ≫ wbar ≫ inv 𝔛.eeta
  haveI : IsIso ψ := by dsimp only [ψ]; infer_instance
  have hinv_base : inv 𝔛.eeta ≫ 𝔛.Meta.toBase = pullback.snd _ _ := by rw [IsIso.inv_comp_eq, 𝔛.heeta]
  have hψ : ψ ≫ 𝔛.Meta.toBase = 𝔛.Meta.toBase := by
    simp only [ψ, Category.assoc, hinv_base, hwbar_snd, 𝔛.heeta]

  have hwgen0 : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut (thetaAlg 𝔛.Meta ψ hψ) • 𝔛.Meta.pointEquivPlace y := by
    intro y y' h
    refine pointEquivPlace_eq_smul 𝔛.Meta ψ hψ y y' ?_
    have h1 : y'.1 ≫ 𝔛.eeta ≫ wbar = y.1 ≫ 𝔛.eeta := by
      apply pullback.hom_ext
      · simpa only [Category.assoc, hwbar_fst] using h
      · simp only [Category.assoc, hwbar_snd, 𝔛.heeta]
        rw [y'.2, y.2]
    simp only [ψ]
    rw [← Category.assoc y'.1, ← Category.assoc, Category.assoc y'.1, h1, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hθ : θ = thetaAlg 𝔛.Meta ψ hψ :=
    ModularCurve.XHDRModelAtP.algEquiv_eq_of_forall_pointEquivPlace_eq_ofAlgAut_smul_of_comp_w_eq p M H hpM hj 𝔛 θ
      (thetaAlg 𝔛.Meta ψ hψ) hwgen hwgen0
  have hθ' : ∀ f, θ f = 𝔛.Meta.ffEquiv.symm ((ffIso 𝔛.Meta ψ).hom (𝔛.Meta.ffEquiv f)) := fun f => by
    rw [hθ]; rfl

  let wA : XO (ΓM M H) hj ρ ⟶ XO (ΓM M H) hj ρ := pullback.lift (pullback.fst _ _ ≫ 𝔛.w.hom) (pullback.snd _ _)
    (by rw [Category.assoc, 𝔛.w_over, pullback.condition])
  have hwA_fst : wA ≫ pullback.fst _ _ = pullback.fst _ _ ≫ 𝔛.w.hom := pullback.lift_fst _ _ _
  have hwA_snd : wA ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  let prA : XQ ⟶ XO (ΓM M H) hj ρ :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
  have hprA_fst : prA ≫ pullback.fst _ _ = pullback.fst _ _ ≫ 𝟙 _ := pullback.lift_fst _ _ _
  have hprA_snd : prA ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom A.subtype) := pullback.lift_snd _ _ _

  have hsqQ : wbar ≫ prA = prA ≫ wA := by
    apply pullback.hom_ext
    · rw [Category.assoc, hprA_fst, Category.comp_id, hwbar_fst, Category.assoc, hwA_fst, ← Category.assoc, hprA_fst,
        Category.comp_id]
    · rw [Category.assoc, hprA_snd, ← Category.assoc, hwbar_snd, Category.assoc, hwA_snd, hprA_snd]
  have hcomm : ψ ≫ 𝔛.eeta ≫ prA = 𝔛.eeta ≫ prA ≫ wA := by
    simp only [ψ, Category.assoc, IsIso.inv_hom_id_assoc]
    rw [hsqQ]

  have hfm_fst : fibreMap (overOfIso 𝔛.w 𝔛.w_over) ((IsLocalRing.residue ↥A).comp ρ) ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ 𝔛.w.hom := by
    unfold XHDRLevel.fibreMap XHDRLevel.overOfIso
    exact pullback.lift_fst _ _ _
  have hfm_snd : fibreMap (overOfIso 𝔛.w 𝔛.w_over) ((IsLocalRing.residue ↥A).comp ρ) ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ 𝟙 _ := by
    unfold XHDRLevel.fibreMap
    exact pullback.lift_snd _ _ _
  have hsqκ : fibreMap (overOfIso 𝔛.w 𝔛.w_over) ((IsLocalRing.residue ↥A).comp ρ) ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl =
      bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl ≫ wA := by
    apply pullback.hom_ext
    · rw [Category.assoc, bcMap_fst, hfm_fst, Category.assoc, hwA_fst, ← Category.assoc, bcMap_fst]
    · rw [Category.assoc, bcMap_snd, ← Category.assoc, hfm_snd, Category.comp_id, Category.assoc, hwA_snd, bcMap_snd]
  have hc : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl) ≫ wA =
      𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl := by
    rw [← 𝔛.comp_w A hA ρ hρ]
    simp only [Category.assoc, hsqκ]

  intro Hfst V hgenV g h0
  exact ZeroTwinH.transport 𝔛.Meta ψ θ hθ' 𝔛.eeta prA wA hcomm _ _ hc ((𝔛.Mfib A hA ρ hρ).ffEquiv.symm)
    Rpd.R₁.integers Rpd.R₂.integers Rpd.R₁.residue Rpd.R₂.residue Rpd.mem_integers₂_iff Rpd.residue₂_eq Hfst V hgenV g h0

end S_ModularCurve_XHDRModelAtP_forall_readA_mem_integers_snd_of_forall_readA_mem_integers_fst
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_forall_readA_mem_integers_snd_of_forall_readA_mem_integers_fst (solution)
