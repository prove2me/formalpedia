-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.algEquiv_ffEquiv_symm_germToFunctionField_eq_of_pointEquivPlace_eq_ofAlgAut_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a5b6ed5e-6efb-5568-be6d-cded5025368b

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_XHDRModelAtP_algEquiv_eq_of_forall_pointEquivPlace_eq_ofAlgAut_smul_of_comp_w_eq
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_algEquiv_ffEquiv_symm_germToFunctionField_eq_of_pointEquivPlace_eq_ofAlgAut_smul
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel TopCat
open scoped MatrixGroups Pointwise

universe u v

namespace WGenH

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

end Generic

end WGenH

namespace WGenH

section PlaceLaw

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
variable (Mdl : CurveModel K L) (ψ : Mdl.C ⟶ Mdl.C) [IsIso ψ] (hψ : ψ ≫ Mdl.toBase = Mdl.toBase)

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
      (Mdl.ffEquiv.symm : Mdl.C.functionField ≃+* L).toRingHom '' ((ffIso Mdl ψ).hom.hom '' (algebraMap (Mdl.C.presheaf.stalk x.1) Mdl.C.functionField).range) := by
    have := congrArg (fun S : Subring L => (S : Set L)) h'
    simp only [Subring.coe_map] at this
    exact this.symm
  have e2 : ((Mdl.placeOfPoint x).toValuationSubring : Set L) =
      (Mdl.ffEquiv.symm : Mdl.C.functionField ≃+* L).toRingHom '' (algebraMap (Mdl.C.presheaf.stalk x.1) Mdl.C.functionField).range := by
    have := congrArg (fun S : Subring L => (S : Set L)) hx
    simp only [Subring.coe_map] at this
    exact this.symm
  rw [e1, e2, Set.image_image, ← Set.image_smul, Set.image_image]
  refine Set.image_congr' fun f => ?_
  show Mdl.ffEquiv.symm ((ffIso Mdl ψ).hom.hom f) = (thetaAlg Mdl ψ hψ) (Mdl.ffEquiv.symm f)
  rw [thetaAlg_apply, theta_apply, RingEquiv.apply_symm_apply]

end PlaceLaw

end WGenH

namespace WGenH

section Points

variable {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]
variable (Mdl : CurveModel K L) (ψ : Mdl.C ⟶ Mdl.C) [IsIso ψ] (hψ : ψ ≫ Mdl.toBase = Mdl.toBase)

theorem pointEquivPlace_eq_smul (y y' : {q : Spec (CommRingCat.of K) ⟶ Mdl.C // q ≫ Mdl.toBase = 𝟙 _})
    (h : y'.1 ≫ ψ = y.1) :
    Mdl.pointEquivPlace y' = SemilinearAut.ofAlgAut (thetaAlg Mdl ψ hψ) • Mdl.pointEquivPlace y := by
  rw [CurveModel.pointEquivPlace_apply, CurveModel.pointEquivPlace_apply]
  apply placeOfPoint_eq_smul
  have := congrArg (fun f : Spec (CommRingCat.of K) ⟶ Mdl.C => f.base (IsLocalRing.closedPoint K)) h
  simpa using this

end Points

end WGenH

namespace WGenH

theorem app_germ_congr {X Y : Scheme} {f f' : X ⟶ Y} (e : f = f') (U : Y.Opens) (x : X)
    (hx : x ∈ f ⁻¹ᵁ U) (hx' : x ∈ f' ⁻¹ᵁ U) :
    f.app U ≫ X.presheaf.germ (f ⁻¹ᵁ U) x hx = f'.app U ≫ X.presheaf.germ (f' ⁻¹ᵁ U) x hx' := by
  subst e; rfl

theorem app_app_germ_congr {X Y Y' Z : Scheme} {a : X ⟶ Y} {b : Y ⟶ Z} {a' : X ⟶ Y'} {b' : Y' ⟶ Z}
    (e : a ≫ b = a' ≫ b') (U : Z.Opens) (x : X) (hx : x ∈ a ⁻¹ᵁ (b ⁻¹ᵁ U)) (hx' : x ∈ a' ⁻¹ᵁ (b' ⁻¹ᵁ U)) :
    b.app U ≫ a.app (b ⁻¹ᵁ U) ≫ X.presheaf.germ (a ⁻¹ᵁ (b ⁻¹ᵁ U)) x hx =
      b'.app U ≫ a'.app (b' ⁻¹ᵁ U) ≫ X.presheaf.germ (a' ⁻¹ᵁ (b' ⁻¹ᵁ U)) x hx' := by
  have h := app_germ_congr e U x hx hx'
  simp only [Scheme.Hom.comp_app] at h
  exact h

end WGenH

open WGenH in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (U : (X p (ΓM M H) hj).Opens)
    (hU : Nonempty (Scheme.Opens.toScheme ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ U)))
    (hwU : Nonempty (Scheme.Opens.toScheme ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ (𝔛.w.hom ⁻¹ᵁ U))))
    (g : Γ(X p (ΓM M H) hj, U)) :
    θ (haveI := hU; 𝔛.Meta.ffEquiv.symm
          (𝔛.Meta.C.germToFunctionField ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ U) (((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app U).hom g))) =
      (haveI := hwU; 𝔛.Meta.ffEquiv.symm
          (𝔛.Meta.C.germToFunctionField ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ (𝔛.w.hom ⁻¹ᵁ U))
            (((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app (𝔛.w.hom ⁻¹ᵁ U)).hom ((𝔛.w.hom.app U).hom g)))) := by
  obtain ⟨hco, hft⟩ := ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := hft
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := hco

  set X := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) with hX

  have hwinv : 𝔛.w.inv ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj := by
    rw [Iso.inv_comp_eq, 𝔛.w_over]
  let wbar : X ⟶ X := pullback.lift (pullback.fst _ _ ≫ 𝔛.w.hom) (pullback.snd _ _) (by rw [Category.assoc, 𝔛.w_over, pullback.condition])
  let wbarinv : X ⟶ X := pullback.lift (pullback.fst _ _ ≫ 𝔛.w.inv) (pullback.snd _ _) (by rw [Category.assoc, hwinv, pullback.condition])
  have hwbar_fst : wbar ≫ pullback.fst _ _ = pullback.fst _ _ ≫ 𝔛.w.hom := pullback.lift_fst _ _ _
  have hwbar_snd : wbar ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hwbarinv_fst : wbarinv ≫ pullback.fst _ _ = pullback.fst _ _ ≫ 𝔛.w.inv := pullback.lift_fst _ _ _
  have hwbarinv_snd : wbarinv ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  haveI : IsIso wbar := ⟨⟨wbarinv, by
      apply pullback.hom_ext
      · rw [Category.assoc, hwbarinv_fst, ← Category.assoc, hwbar_fst, Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
      · rw [Category.assoc, hwbarinv_snd, hwbar_snd, Category.id_comp], by
      apply pullback.hom_ext
      · rw [Category.assoc, hwbar_fst, ← Category.assoc, hwbarinv_fst, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
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
  rw [hθ, thetaAlg_apply, theta_apply, RingEquiv.apply_symm_apply]
  refine congrArg 𝔛.Meta.ffEquiv.symm ?_

  have hcomm : ψ ≫ (𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) =
      (𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ≫ 𝔛.w.hom := by
    simp only [ψ, Category.assoc, IsIso.inv_hom_id_assoc, hwbar_fst]

  have memgen : ∀ (V : 𝔛.Meta.C.Opens), Nonempty V → genericPoint 𝔛.Meta.C ∈ V := fun V hV =>
    ((genericPoint_spec 𝔛.Meta.C).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  have h1 := memgen _ hU
  have h2 := memgen _ hwU
  have h3 := genericPoint_mem_preimage 𝔛.Meta ψ h1
  have key :
      (𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app U ≫
          𝔛.Meta.C.presheaf.germ _ (genericPoint 𝔛.Meta.C) h1 ≫ (ffIso 𝔛.Meta ψ).hom =
        𝔛.w.hom.app U ≫
          (𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app (𝔛.w.hom ⁻¹ᵁ U) ≫
            𝔛.Meta.C.presheaf.germ _ (genericPoint 𝔛.Meta.C) h2 := by
    rw [germ_ffIso 𝔛.Meta ψ h1 h3]
    exact app_app_germ_congr hcomm U (genericPoint 𝔛.Meta.C) h3 h2
  have e := congrFun (congrArg DFunLike.coe (CommRingCat.hom_ext_iff.mp key)) g
  simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using e

#print axioms solution

end S_ModularCurve_XHDRModelAtP_algEquiv_ffEquiv_symm_germToFunctionField_eq_of_pointEquivPlace_eq_ofAlgAut_smul
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_algEquiv_ffEquiv_symm_germToFunctionField_eq_of_pointEquivPlace_eq_ofAlgAut_smul (solution)
