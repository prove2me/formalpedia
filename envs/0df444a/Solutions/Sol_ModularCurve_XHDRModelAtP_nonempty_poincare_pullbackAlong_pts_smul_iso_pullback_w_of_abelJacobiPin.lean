-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.nonempty_poincare_pullbackAlong_pts_smul_iso_pullback_w_of_abelJacobiPin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/3f65986f-08e3-5a07-a7db-ed161e7d03ed

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_ev_app_tensorUnit
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_one_iso
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_nonempty_poincare_pullbackAlong_pts_smul_iso_pullback_w_of_abelJacobiPin
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard

namespace WGenH

theorem nonempty_iso_unit_of_isLocalRing {A : Type u} [CommRing A] [IsLocalRing A]
    (L : (Spec (CommRingCat.of A)).Modules) (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (L ≅ SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf) := by
  obtain ⟨U, hU, ⟨e⟩⟩ := hL.exists_trivialization (IsLocalRing.closedPoint A)
  have hUtop : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hU
  subst hUtop

  let X : Scheme.{u} := Spec (CommRingCat.of A)
  let ι : (⊤ : X.Opens).toScheme ⟶ X := (⊤ : X.Opens).ι
  let j : X ⟶ (⊤ : X.Opens).toScheme := X.topIso.inv
  have hj : j ≫ ι = 𝟙 X := X.toIso_inv_ι
  refine ⟨?_⟩
  exact ((Scheme.Modules.pullbackId X).app L).symm ≪≫
    ((Scheme.Modules.pullbackCongr hj).app L).symm ≪≫
    ((Scheme.Modules.pullbackComp j ι).app L).symm ≪≫
    (Scheme.Modules.pullback j).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso j

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

noncomputable def prodMap (v : SchemeHomOver c c) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    pullback c t ⟶ pullback c t :=
  pullback.map c t c t v.1 (𝟙 T) (𝟙 _) (by rw [v.2, Category.comp_id]) (by simp)

@[reassoc (attr := simp)]
theorem prodMap_fst (v : SchemeHomOver c c) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    prodMap v t ≫ pullback.fst c t = pullback.fst c t ≫ v.1 := by
  simp only [prodMap, pullback.map, pullback.lift_fst]

@[reassoc (attr := simp)]
theorem prodMap_snd (v : SchemeHomOver c c) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    prodMap v t ≫ pullback.snd c t = pullback.snd c t := by
  simp only [prodMap, pullback.map, pullback.lift_snd, Category.comp_id]

theorem baseChangeSnd_prodMap (v : SchemeHomOver c c) {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    baseChangeSnd c ψ ≫ prodMap v t = prodMap v t' ≫ baseChangeSnd c ψ := by
  apply pullback.hom_ext <;>
    simp only [prodMap, baseChangeSnd, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id]

noncomputable def pullbackProdMapBaseChangeSndIso (v : SchemeHomOver c c) {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t)
    (L : (pullback c t).Modules) :
    (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj ((Scheme.Modules.pullback (prodMap v t)).obj L) ≅
      (Scheme.Modules.pullback (prodMap v t')).obj ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj L) :=
  (Scheme.Modules.pullbackComp _ _).app L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_prodMap v ψ)).app L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app L).symm

theorem fibrewiseAlgEquivZero_pullback_prodMap (v : SchemeHomOver c c) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M)
    (M' : RigidifiedLineBundle c ε t) (e : M'.L ≅ (Scheme.Modules.pullback (prodMap v t)).obj M.L) :
    FibrewiseAlgEquivZero M' := by
  intro k _ _ s

  let vk : Limits.pullback (pullback.snd c t) s ⟶ Limits.pullback (pullback.snd c t) s :=
    pullback.map _ _ _ _ (prodMap v t) (𝟙 _) (𝟙 T) (by rw [prodMap_snd, Category.comp_id]) (by simp)
  have hvk : vk ≫ fibreAt c t s = fibreAt c t s := by
    simp only [vk, fibreAt, pullback.lift_snd, Category.comp_id]
  have hfst : vk ≫ pullback.fst (pullback.snd c t) s = pullback.fst (pullback.snd c t) s ≫ prodMap v t := by
    simp only [vk, pullback.lift_fst]
  refine IsAlgEquivZero.of_iso ?_ ((hM k s).pullback vk hvk)
  exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr hfst).app M.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.L).symm ≪≫
    ((Scheme.Modules.pullback _).mapIso e).symm

noncomputable def translate (v : SchemeHomOver c c) {A : Type u} [CommRing A] [IsLocalRing A]
    {t : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t) :
    RigidifiedLineBundle c ε t where
  L := (Scheme.Modules.pullback (prodMap v t)).obj M.L
  isInvertible := M.isInvertible.pullback _
  rigidified := nonempty_iso_unit_of_isLocalRing _ ((M.isInvertible.pullback _).pullback _)

theorem translate_L (v : SchemeHomOver c c) {A : Type u} [CommRing A] [IsLocalRing A]
    {t : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t) :
    (translate v M).L = (Scheme.Modules.pullback (prodMap v t)).obj M.L := rfl

theorem exists_extension_of_translate {D : GoodReductionJacobian.RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (v : SchemeHomOver c c)
    {A : Type u} [CommRing A] [IsLocalRing A] (σ : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    {K : Type u} [CommRing K] [IsLocalRing K] {τ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)}
    (b : SchemeHomOver τ σ)
    (y y' : SchemeHomOver τ D.toBase)
    (hy' : Nonempty ((h.poincare.pullbackAlong y').L ≅
      (Scheme.Modules.pullback (prodMap v τ)).obj (h.poincare.pullbackAlong y).L))
    (s : SchemeHomOver σ D.toBase) (hs : y.1 = b.1 ≫ s.1) :
    ∃ s' : SchemeHomOver σ D.toBase, y'.1 = b.1 ≫ s'.1 := by

  let M : RigidifiedLineBundle c ε σ := h.poincare.pullbackAlong s
  have hM : FibrewiseAlgEquivZero M := (algEquivZeroCut c ε).pullback_mem _ _ s _ h.poincare_mem
  let M' : RigidifiedLineBundle c ε σ := translate v M
  have hM' : FibrewiseAlgEquivZero M' := fibrewiseAlgEquivZero_pullback_prodMap v M hM M' (Iso.refl _)

  obtain ⟨s', ⟨es'⟩, -⟩ := h.univ σ M' hM'
  refine ⟨s', ?_⟩

  have hyb : y = postComp s b := Subtype.ext hs
  let y'' : SchemeHomOver τ D.toBase := postComp s' b
  suffices y' = y'' from congrArg Subtype.val this
  refine h.ext_of_iso τ y' y'' ⟨hy'.some ≪≫ ?_⟩

  refine (Scheme.Modules.pullback (prodMap v τ)).mapIso
      (((Scheme.Modules.pullbackCongr (congrArg (baseChangeSnd c) hyb)).app h.poincare.L) ≪≫
        ((Scheme.Modules.pullbackCongr (baseChangeSnd_comp c s b).symm).app h.poincare.L) ≪≫
        ((Scheme.Modules.pullbackComp _ _).app h.poincare.L).symm) ≪≫ ?_
  refine (pullbackProdMapBaseChangeSndIso v b _).symm ≪≫ ?_
  refine (Scheme.Modules.pullback (baseChangeSnd c b)).mapIso es'.symm ≪≫ ?_
  exact (Scheme.Modules.pullbackComp _ _).app h.poincare.L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c s' b)).app h.poincare.L

end WGenH

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

noncomputable section

namespace WGenC

def isoOfTensorIsoUnit {V : Scheme.{u}} (X Y Y' : V.Modules) (i : X ⊗ Y ≅ 𝟙_ _) (i' : X ⊗ Y' ≅ 𝟙_ _) :
    Y ≅ Y' :=
  (λ_ Y).symm ≪≫ (i'.symm ⊗ᵢ Iso.refl Y) ≪≫ ((β_ X Y') ⊗ᵢ Iso.refl Y) ≪≫ α_ Y' X Y ≪≫
    (Iso.refl Y' ⊗ᵢ i) ≪≫ ρ_ Y'

def isoOfTensorIsoUnit' {V : Scheme.{u}} (X Y Y' : V.Modules) (i : Y ⊗ X ≅ 𝟙_ _) (i' : Y' ⊗ X ≅ 𝟙_ _) :
    Y ≅ Y' :=
  isoOfTensorIsoUnit X Y Y' (β_ X Y ≪≫ i) (β_ X Y' ≪≫ i')

def pullbackTensorIsoUnit {V W : Scheme.{u}} (φ : W ⟶ V) {X Y : V.Modules} (i : X ⊗ Y ≅ 𝟙_ _) :
    (Scheme.Modules.pullback φ).obj X ⊗ (Scheme.Modules.pullback φ).obj Y ≅ 𝟙_ _ :=
  (Scheme.Modules.pullbackTensorObjIso φ X Y).symm ≪≫ (Scheme.Modules.pullback φ).mapIso i ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso φ

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) {T : Scheme.{u}} {g : T ⟶ S}

def ptTranslate (e : pullback f g ≅ pullback f g) (a : T ⟶ 𝒞) (ha : a ≫ f = g) : T ⟶ 𝒞 :=
  graphOver f a ha ≫ e.inv ≫ pullback.fst f g

variable {f}

theorem ptTranslate_comp {e : pullback f g ≅ pullback f g} (he : e.inv ≫ pullback.snd f g = pullback.snd f g)
    (a : T ⟶ 𝒞) (ha : a ≫ f = g) : ptTranslate f e a ha ≫ f = g := by
  simp only [ptTranslate, Category.assoc, pullback.condition]
  rw [reassoc_of% he, graphOver_snd_assoc]

theorem graphOver_ptTranslate {e : pullback f g ≅ pullback f g} (he : e.inv ≫ pullback.snd f g = pullback.snd f g)
    (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    graphOver f (ptTranslate f e a ha) (ptTranslate_comp he a ha) = graphOver f a ha ≫ e.inv := by
  apply pullback.hom_ext
  · simp only [graphOver_fst, ptTranslate, Category.assoc]
  · simp only [graphOver_snd, Category.assoc]
    rw [he, graphOver_snd]

variable [IsSeparated f]

theorem comap_ofPoint_I {e : pullback f g ≅ pullback f g} (he : e.inv ≫ pullback.snd f g = pullback.snd f g)
    (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    (RelEffCartierDiv.ofPoint f a ha).I.comap e.hom =
      (RelEffCartierDiv.ofPoint f (ptTranslate f e a ha) (ptTranslate_comp he a ha)).I := by
  simp only [RelEffCartierDiv.ofPoint_I]
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, graphOver_ptTranslate he]
  have hfst : pullback.fst e.hom (graphOver f a ha) =
      pullback.snd e.hom (graphOver f a ha) ≫ graphOver f a ha ≫ e.inv := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hfst, Scheme.Hom.ker_comp_of_isIso]

variable [SmoothOfRelativeDimension 1 f]

theorem nonempty_pullback_lineBundle_iso {e : pullback f g ≅ pullback f g}
    (he : e.inv ≫ pullback.snd f g = pullback.snd f g) (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    Nonempty ((Scheme.Modules.pullback e.hom).obj (RelEffCartierDiv.ofPoint f a ha).lineBundle ≅
      (RelEffCartierDiv.ofPoint f (ptTranslate f e a ha) (ptTranslate_comp he a ha)).lineBundle) := by
  have hI := (RelEffCartierDiv.ofPoint f a ha).isInvertible_I
  have hI' : ((RelEffCartierDiv.ofPoint f a ha).I.comap e.hom).IsInvertible := by
    rw [comap_ofPoint_I he]
    exact RelEffCartierDiv.isInvertible_I _
  obtain ⟨i⟩ := hI.nonempty_pullback_invModule_iso e.hom hI'
  exact ⟨i ≪≫ eqToIso (by rw [comap_ofPoint_I he])⟩

omit [IsSeparated f] [SmoothOfRelativeDimension 1 f] in

theorem nonempty_idealModule_tensor_lineBundle_iso {r : ℕ} (D : RelEffCartierDiv f r g) (hD : D.I.IsInvertible) :
    Nonempty (D.idealModule ⊗ D.lineBundle ≅ 𝟙_ _) := by
  have h := hD.isInvertible_module.isIso_ev_app_tensorUnit
  exact ⟨@asIso _ _ _ _ _ h⟩

theorem nonempty_pullback_idealModule_iso {e : pullback f g ≅ pullback f g}
    (he : e.inv ≫ pullback.snd f g = pullback.snd f g) (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    Nonempty ((Scheme.Modules.pullback e.hom).obj (RelEffCartierDiv.ofPoint f a ha).idealModule ≅
      (RelEffCartierDiv.ofPoint f (ptTranslate f e a ha) (ptTranslate_comp he a ha)).idealModule) := by
  obtain ⟨j⟩ := nonempty_pullback_lineBundle_iso he a ha
  obtain ⟨i₁⟩ := nonempty_idealModule_tensor_lineBundle_iso (RelEffCartierDiv.ofPoint f a ha)
    (RelEffCartierDiv.isInvertible_I _)
  obtain ⟨i₂⟩ := nonempty_idealModule_tensor_lineBundle_iso
    (RelEffCartierDiv.ofPoint f (ptTranslate f e a ha) (ptTranslate_comp he a ha)) (RelEffCartierDiv.isInvertible_I _)

  refine ⟨isoOfTensorIsoUnit' _ _ _ ?_ i₂⟩
  exact (Iso.refl _ ⊗ᵢ j.symm) ≪≫ pullbackTensorIsoUnit e.hom i₁

end WGenC

end

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian

noncomputable section

namespace WGenC

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (R' : Type u) [CommRing R'] [Algebra R R']

def fstOver (D : RelativePic0Designation R c) :
    SchemeHomOver ((D.baseChange R').toBase ≫ specMap R R') D.toBase :=
  ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩

theorem nonempty_poincare_pullbackAlong_postComp_fstOver_iso {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R' (h.poincare.pullbackAlong (fstOver c R' D))).L))
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R')} (a : SchemeHomOver t (D.baseChange R').toBase) :
    Nonempty ((h.poincare.pullbackAlong (postComp (fstOver c R' D) (BaseChange.overR R' a))).L ≅
      (Scheme.Modules.pullback (BaseChange.κ c R' t).inv).obj (h'.poincare.pullbackAlong a).L) := by
  obtain ⟨eP⟩ := hP
  refine ⟨?_⟩
  refine ((Scheme.Modules.pullbackCongr (baseChangeSnd_comp c (fstOver c R' D) (BaseChange.overR R' a)).symm).app
      h.poincare.L) ≪≫ ((Scheme.Modules.pullbackComp _ _).app h.poincare.L).symm ≪≫ ?_

  refine (Scheme.Modules.pullback (baseChangeSnd c (BaseChange.overR R' a))).mapIso
      (BaseChange.toR_ofR_iso c ε R' (h.poincare.pullbackAlong (fstOver c R' D))).symm ≪≫ ?_
  refine BaseChange.toR_pullbackAlong_iso c ε R' a (BaseChange.ofR c ε R' (h.poincare.pullbackAlong (fstOver c R' D))) ≪≫ ?_

  exact (Scheme.Modules.pullback (BaseChange.κ c R' t).inv).mapIso
    ((Scheme.Modules.pullback (baseChangeSnd (baseChange R c R') a)).mapIso eP.symm)

def endoBaseChange (v : SchemeHomOver c c) : SchemeHomOver (baseChange R c R') (baseChange R c R') :=
  ⟨pullback.map c (specMap R R') c (specMap R R') v.1 (𝟙 _) (𝟙 _) (by rw [v.2, Category.comp_id]) (by simp),
    by simp only [pullback.map, pullback.lift_snd, Category.comp_id]⟩

@[reassoc]
theorem endoBaseChange_fst (v : SchemeHomOver c c) :
    (endoBaseChange c R' v).1 ≫ pullback.fst c (specMap R R') = pullback.fst c (specMap R R') ≫ v.1 := by
  simp only [endoBaseChange, pullback.map, pullback.lift_fst]

theorem κ_hom_prodMap (v : SchemeHomOver c c) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) :
    (BaseChange.κ c R' t).hom ≫ WGenH.prodMap v (t ≫ specMap R R') =
      WGenH.prodMap (endoBaseChange c R' v) t ≫ (BaseChange.κ c R' t).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, WGenH.prodMap_fst, ← Category.assoc, BaseChange.κ_hom_fst, Category.assoc,
      Category.assoc, BaseChange.κ_hom_fst, WGenH.prodMap_fst_assoc, endoBaseChange_fst]
  · rw [Category.assoc, WGenH.prodMap_snd, BaseChange.κ_hom_snd, Category.assoc, BaseChange.κ_hom_snd,
      WGenH.prodMap_snd]

theorem prodMap_κ_inv (v : SchemeHomOver c c) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) :
    WGenH.prodMap v (t ≫ specMap R R') ≫ (BaseChange.κ c R' t).inv =
      (BaseChange.κ c R' t).inv ≫ WGenH.prodMap (endoBaseChange c R' v) t := by
  rw [Iso.comp_inv_eq, Category.assoc, ← κ_hom_prodMap, Iso.inv_hom_id_assoc]

def pullbackProdMapκInvIso (v : SchemeHomOver c c) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
    (N : (pullback (baseChange R c R') t).Modules) :
    (Scheme.Modules.pullback (WGenH.prodMap v (t ≫ specMap R R'))).obj
        ((Scheme.Modules.pullback (BaseChange.κ c R' t).inv).obj N) ≅
      (Scheme.Modules.pullback (BaseChange.κ c R' t).inv).obj
        ((Scheme.Modules.pullback (WGenH.prodMap (endoBaseChange c R' v) t)).obj N) :=
  (Scheme.Modules.pullbackComp _ _).app N ≪≫ (Scheme.Modules.pullbackCongr (prodMap_κ_inv c R' v t)).app N ≪≫
    ((Scheme.Modules.pullbackComp _ _).app N).symm

def prodMapIso (w : C ≅ C) (hw : w.hom ≫ c = c) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) :
    pullback (baseChange R c R') t ≅ pullback (baseChange R c R') t where
  hom := WGenH.prodMap (endoBaseChange c R' ⟨w.hom, hw⟩) t
  inv := WGenH.prodMap (endoBaseChange c R' ⟨w.inv, by rw [Iso.inv_comp_eq, hw]⟩) t
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, WGenH.prodMap_fst, WGenH.prodMap_fst_assoc, Category.id_comp]
      apply pullback.hom_ext
      · simp only [Category.assoc, endoBaseChange_fst, endoBaseChange_fst_assoc, Iso.hom_inv_id, Category.comp_id]
      · rw [Category.assoc, Category.assoc, (endoBaseChange c R' _).2, (endoBaseChange c R' _).2]
    · simp only [Category.assoc, WGenH.prodMap_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, WGenH.prodMap_fst, WGenH.prodMap_fst_assoc, Category.id_comp]
      apply pullback.hom_ext
      · simp only [Category.assoc, endoBaseChange_fst, endoBaseChange_fst_assoc, Iso.inv_hom_id, Category.comp_id]
      · rw [Category.assoc, Category.assoc, (endoBaseChange c R' _).2, (endoBaseChange c R' _).2]
    · simp only [Category.assoc, WGenH.prodMap_snd, Category.id_comp]

theorem prodMapIso_hom (w : C ≅ C) (hw : w.hom ≫ c = c) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) :
    (prodMapIso c R' w hw t).hom = WGenH.prodMap (endoBaseChange c R' ⟨w.hom, hw⟩) t := rfl

theorem prodMapIso_inv_snd (w : C ≅ C) (hw : w.hom ≫ c = c) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) :
    (prodMapIso c R' w hw t).inv ≫ pullback.snd _ _ = pullback.snd _ _ :=
  WGenH.prodMap_snd _ _

theorem prodMapIso_inv_fst (w : C ≅ C) (hw : w.hom ≫ c = c) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) :
    (prodMapIso c R' w hw t).inv ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (endoBaseChange c R' ⟨w.inv, by rw [Iso.inv_comp_eq, hw]⟩).1 :=
  WGenH.prodMap_fst _ _

def κτ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) {τ : T ⟶ Spec (CommRingCat.of R)}
    (hτ : τ = t ≫ specMap R R') : pullback (baseChange R c R') t ≅ pullback c τ :=
  BaseChange.κ c R' t ≪≫ pullback.congrHom rfl hτ.symm

theorem κτ_hom_fst {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) {τ : T ⟶ Spec (CommRingCat.of R)}
    (hτ : τ = t ≫ specMap R R') :
    (κτ c R' t hτ).hom ≫ pullback.fst c τ = pullback.fst (baseChange R c R') t ≫ pullback.fst c (specMap R R') := by
  subst hτ
  simp only [κτ, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
    BaseChange.κ_hom_fst]

theorem κτ_hom_snd {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) {τ : T ⟶ Spec (CommRingCat.of R)}
    (hτ : τ = t ≫ specMap R R') :
    (κτ c R' t hτ).hom ≫ pullback.snd c τ = pullback.snd (baseChange R c R') t := by
  subst hτ
  simp only [κτ, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
    BaseChange.κ_hom_snd]

theorem κτ_rfl_hom {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) :
    (κτ c R' t (rfl : t ≫ specMap R R' = _)).hom = (BaseChange.κ c R' t).hom := by
  apply pullback.hom_ext
  · rw [κτ_hom_fst, BaseChange.κ_hom_fst]
  · rw [κτ_hom_snd, BaseChange.κ_hom_snd]

theorem κτ_rfl_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) :
    (κτ c R' t (rfl : t ≫ specMap R R' = _)).inv = (BaseChange.κ c R' t).inv := by
  have h : κτ c R' t (rfl : t ≫ specMap R R' = _) = BaseChange.κ c R' t := Iso.ext (κτ_rfl_hom c R' t)
  rw [h]

theorem nonempty_poincare_pullbackAlong_iso_of_eq_fst {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R' (h.poincare.pullbackAlong (fstOver c R' D))).L))
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R')} {τ : T ⟶ Spec (CommRingCat.of R)} (hτ : τ = t ≫ specMap R R')
    (a : SchemeHomOver t (D.baseChange R').toBase) (y : SchemeHomOver τ D.toBase)
    (hy : y.1 = a.1 ≫ pullback.fst D.toBase (specMap R R')) :
    Nonempty ((h.poincare.pullbackAlong y).L ≅
      (Scheme.Modules.pullback (κτ c R' t hτ).inv).obj (h'.poincare.pullbackAlong a).L) := by
  subst hτ
  have hy' : y = postComp (fstOver c R' D) (BaseChange.overR R' a) := Subtype.ext hy
  subst hy'
  rw [κτ_rfl_inv]
  exact nonempty_poincare_pullbackAlong_postComp_fstOver_iso c ε R' h h' hP a

theorem prodMap_κτ_inv (v : SchemeHomOver c c) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
    {τ : T ⟶ Spec (CommRingCat.of R)} (hτ : τ = t ≫ specMap R R') :
    WGenH.prodMap v τ ≫ (κτ c R' t hτ).inv = (κτ c R' t hτ).inv ≫ WGenH.prodMap (endoBaseChange c R' v) t := by
  subst hτ
  rw [κτ_rfl_inv]
  exact prodMap_κ_inv c R' v t

def pullbackProdMapκτInvIso (v : SchemeHomOver c c) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
    {τ : T ⟶ Spec (CommRingCat.of R)} (hτ : τ = t ≫ specMap R R') (N : (pullback (baseChange R c R') t).Modules) :
    (Scheme.Modules.pullback (WGenH.prodMap v τ)).obj ((Scheme.Modules.pullback (κτ c R' t hτ).inv).obj N) ≅
      (Scheme.Modules.pullback (κτ c R' t hτ).inv).obj
        ((Scheme.Modules.pullback (WGenH.prodMap (endoBaseChange c R' v) t)).obj N) :=
  (Scheme.Modules.pullbackComp _ _).app N ≪≫ (Scheme.Modules.pullbackCongr (prodMap_κτ_inv c R' v t hτ)).app N ≪≫
    ((Scheme.Modules.pullbackComp _ _).app N).symm

end WGenC

end

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard GoodReductionJacobian"

noncomputable section

namespace WGenC

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {D : RelativePic0Designation R c}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)

abbrev lawD : RelativeGroupLaw R D.toBase :=
  RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h

theorem nonempty_poincare_mul_iso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t D.toBase) :
    Nonempty ((h.poincare.pullbackAlong ((lawD h).mul t x y)).L ≅
      (h.poincare.pullbackAlong x).L ⊗ (h.poincare.pullbackAlong y).L) :=
  RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso (P := algEquivZeroGroupCut c ε) h
    (T := Over.mk t) (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)

theorem nonempty_poincare_one_iso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Nonempty ((h.poincare.pullbackAlong ((lawD h).one t)).L ≅ 𝟙_ _) :=
  RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso (P := algEquivZeroGroupCut c ε) h (Over.mk t)

theorem eq_one_of_mul_self {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) (hx : G.mul t x x = x) :
    x = G.one t := by
  calc x = G.mul t (G.one t) x := (G.one_mul t x).symm
    _ = G.mul t (G.mul t (G.inv t x) x) x := by rw [G.inv_mul_cancel]
    _ = G.mul t (G.inv t x) (G.mul t x x) := G.mul_assoc t _ _ _
    _ = G.one t := by rw [hx, G.inv_mul_cancel]

variable {J : Type*} [AddCommGroup J] {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
  (pts : J → SchemeHomOver t D.toBase) (hpts : ∀ x y : J, pts (x + y) = (lawD h).mul t (pts x) (pts y))

include hpts in
theorem pts_zero : pts 0 = (lawD h).one t :=
  eq_one_of_mul_self (lawD h) t (pts 0) (by rw [← hpts, add_zero])

include hpts in
theorem nonempty_poincare_pts_zero_iso : Nonempty ((h.poincare.pullbackAlong (pts 0)).L ≅ 𝟙_ _) := by
  rw [pts_zero h pts hpts]
  exact nonempty_poincare_one_iso h t

include hpts in

theorem nonempty_poincare_pts_neg_tensor_iso (x : J) :
    Nonempty ((h.poincare.pullbackAlong (pts (-x))).L ⊗ (h.poincare.pullbackAlong (pts x)).L ≅ 𝟙_ _) := by
  obtain ⟨e₁⟩ := nonempty_poincare_mul_iso h t (pts (-x)) (pts x)
  obtain ⟨e₀⟩ := nonempty_poincare_pts_zero_iso h pts hpts
  rw [← hpts, neg_add_cancel] at e₁
  exact ⟨e₁.symm ≪≫ e₀⟩

include hpts in

theorem nonempty_poincare_pts_sub_tensor_iso (x y : J) :
    Nonempty ((h.poincare.pullbackAlong (pts (x - y))).L ⊗ (h.poincare.pullbackAlong (pts y)).L ≅
      (h.poincare.pullbackAlong (pts x)).L) := by
  obtain ⟨e₁⟩ := nonempty_poincare_mul_iso h t (pts (x - y)) (pts y)
  rw [← hpts, sub_add_cancel] at e₁
  exact ⟨e₁.symm⟩

def isoOfTensorRightIso {V : Scheme.{u}} {Z Z' A A' : V.Modules} (i : Z ⊗ A ≅ Z' ⊗ A) (j : A ⊗ A' ≅ 𝟙_ _) : Z ≅ Z' :=
  (ρ_ Z).symm ≪≫ (Iso.refl Z ⊗ᵢ j.symm) ≪≫ (α_ Z A A').symm ≪≫ (i ⊗ᵢ Iso.refl A') ≪≫ α_ Z' A A' ≪≫
    (Iso.refl Z' ⊗ᵢ j) ≪≫ ρ_ Z'

variable (Φ : (pullback c t).Modules ⥤ (pullback c t).Modules) [Φ.Monoidal] (W : J →+ J)

def Compat (x : J) : Prop :=
  Nonempty ((h.poincare.pullbackAlong (pts (W x))).L ≅ Φ.obj (h.poincare.pullbackAlong (pts x)).L)

include hpts in
theorem compat_zero : Compat h pts Φ W 0 := by
  obtain ⟨e₀⟩ := nonempty_poincare_pts_zero_iso h pts hpts
  rw [Compat, map_zero]
  exact ⟨e₀ ≪≫ (Functor.Monoidal.εIso Φ) ≪≫ Φ.mapIso e₀.symm⟩

include hpts in
theorem compat_add {x y : J} (hx : Compat h pts Φ W x) (hy : Compat h pts Φ W y) : Compat h pts Φ W (x + y) := by
  obtain ⟨ex⟩ := hx
  obtain ⟨ey⟩ := hy
  obtain ⟨m⟩ := nonempty_poincare_mul_iso h t (pts x) (pts y)
  obtain ⟨mW⟩ := nonempty_poincare_mul_iso h t (pts (W x)) (pts (W y))
  rw [← hpts] at m mW
  rw [Compat, map_add]
  exact ⟨mW ≪≫ (ex ⊗ᵢ ey) ≪≫ Functor.Monoidal.μIso Φ _ _ ≪≫ Φ.mapIso m.symm⟩

include hpts in
theorem compat_neg {x : J} (hx : Compat h pts Φ W x) : Compat h pts Φ W (-x) := by
  obtain ⟨ex⟩ := hx
  obtain ⟨n⟩ := nonempty_poincare_pts_neg_tensor_iso h pts hpts x
  obtain ⟨nW⟩ := nonempty_poincare_pts_neg_tensor_iso h pts hpts (W x)
  rw [Compat, map_neg]

  refine ⟨isoOfTensorIsoUnit' _ _ _ nW ?_⟩
  exact (Iso.refl _ ⊗ᵢ ex) ≪≫ Functor.Monoidal.μIso Φ _ _ ≪≫ Φ.mapIso n ≪≫ (Functor.Monoidal.εIso Φ).symm

include hpts in

theorem compat_of_mem_closure {S : Set J} (hS : ∀ x ∈ S, Compat h pts Φ W x) {x : J} (hx : x ∈ AddSubgroup.closure S) :
    Compat h pts Φ W x := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy => exact hS y hy
  | zero => exact compat_zero h pts hpts Φ W
  | add a b _ _ ha hb => exact compat_add h pts hpts Φ W ha hb
  | neg a _ ha => exact compat_neg h pts hpts Φ W ha

end WGenC

end

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

noncomputable section

namespace WGenC

theorem mem_closure_of_forall_sub_single {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hdeg : ∀ v : Place K F, v.deg = 1) (e : Place K F) (G : Place K F → Divisor.degZero (K := K) (F := F))
    (hG : ∀ v, (G v : Divisor K F) = Finsupp.single v 1 - Finsupp.single e 1)
    (S : Set (Pic0 K F)) (hS : ∀ v, Pic0.mk (G v) ∈ S) (x : Pic0 K F) : x ∈ AddSubgroup.closure S := by
  obtain ⟨Dv, rfl⟩ := Pic0.mk_surjective x
  set D : Divisor K F := (Dv : Divisor K F) with hD

  have hsum : (∑ v ∈ D.support, D v) = 0 := by
    have h0 : Divisor.degree D = 0 := Dv.2
    unfold Divisor.degree at h0
    rw [Finsupp.liftAddHom_apply, Finsupp.sum] at h0
    simpa [hdeg] using h0

  have hDv : Dv = ∑ v ∈ D.support, (D v) • G v := by
    apply Subtype.ext
    rw [AddSubgroup.val_finsetSum]
    simp only [AddSubgroupClass.coe_zsmul, hG, smul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul, hsum, zero_smul, sub_zero]
    simp only [Finsupp.smul_single_one]
    exact (Finsupp.sum_single D).symm
  rw [hDv]
  change (QuotientAddGroup.mk' _) (∑ v ∈ D.support, (D v) • G v) ∈ _
  rw [map_sum]
  refine AddSubgroup.sum_mem _ fun v _ => ?_
  rw [map_zsmul]
  exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (hS v)) _

section Frame

set_option linter.unusedSectionVars false

variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

theorem genPt_eq : genPt p = specMap ℚ (AlgebraicClosure ℚ) ≫ specMap (R p) ℚ := by
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  first | rfl | (congr 2; exact IsScalarTower.algebraMap_eq _ _ _)

structure AJFrame (𝔛 : XHDRModelAtP p M H hpM hj) where
  D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)
  pts : JH M H → SchemeHomOver (genPt p) D.toBase
  hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D
  hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ)
  hsep : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)
  ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (D.baseChange ℚ).toBase
  kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ)
  ajbar : 𝔛.Meta.C ⟶ D.P
  εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}
  hpoinc : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L)
  hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
        ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
        ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
        (Category.comp_id t)))).idealModule)
  hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p)
  hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) =
    pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ)
  hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ)
  hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1
  hpts_law : ∀ x y : JH M H,
    pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y)
  hAJ : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar
  wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)
  hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y

variable {p M H hpM hj} {𝔛 : XHDRModelAtP p M H hpM hj} (F : AJFrame p M H hpM hj 𝔛)

abbrev Pt (𝔛 : XHDRModelAtP p M H hpM hj) : Type :=
  {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}

namespace AJFrame

abbrev wOver (𝔛 : XHDRModelAtP p M H hpM hj) : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓM M H) hj) :=
  ⟨𝔛.w.hom, 𝔛.w_over⟩

abbrev wInvOver (𝔛 : XHDRModelAtP p M H hpM hj) : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓM M H) hj) :=
  ⟨𝔛.w.inv, by rw [Iso.inv_comp_eq, 𝔛.w_over]⟩

theorem inv_eeta_toBase : inv 𝔛.eeta ≫ 𝔛.Meta.toBase = pullback.snd _ _ := by
  rw [← 𝔛.heeta, IsIso.inv_hom_id_assoc]

def prePt (y : Pt 𝔛) : Pt 𝔛 :=
  ⟨y.1 ≫ 𝔛.eeta ≫ WGenH.prodMap (wInvOver 𝔛) (genPt p) ≫ inv 𝔛.eeta, by
    rw [Category.assoc, Category.assoc, Category.assoc, inv_eeta_toBase, WGenH.prodMap_snd, 𝔛.heeta, y.2]⟩

theorem prePt_eeta (y : Pt 𝔛) :
    (prePt y).1 ≫ 𝔛.eeta = y.1 ≫ 𝔛.eeta ≫ WGenH.prodMap (wInvOver 𝔛) (genPt p) := by
  simp only [prePt, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

theorem prePt_w (y : Pt 𝔛) :
    (prePt y).1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ := by
  rw [← Category.assoc, prePt_eeta, Category.assoc, Category.assoc, WGenH.prodMap_fst_assoc, Iso.inv_hom_id,
    Category.comp_id]

theorem pointEquivPlace_prePt (y : Pt 𝔛) : 𝔛.Meta.pointEquivPlace (prePt y) = F.wgen • 𝔛.Meta.pointEquivPlace y :=
  F.hwgen y (prePt y) (prePt_w y)

def xQ (y : Pt 𝔛) : SchemeHomOver (specMap ℚ (AlgebraicClosure ℚ)) (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) :=
  ⟨y.1 ≫ 𝔛.eeta ≫ F.kQ, by
    rw [Category.assoc, Category.assoc, F.hkQ₂, reassoc_of% 𝔛.heeta, reassoc_of% y.2]⟩

abbrev eQ (𝔛 : XHDRModelAtP p M H hpM hj) :
    pullback (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) ≅
      pullback (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) :=
  prodMapIso (toBase p (ΓM M H) hj) ℚ 𝔛.w 𝔛.w_over (specMap ℚ (AlgebraicClosure ℚ))

theorem eQ_inv_snd : (eQ 𝔛).inv ≫ pullback.snd _ _ = pullback.snd _ _ :=
  prodMapIso_inv_snd _ _ _ _ _

theorem prodMap_wInv_kQ :
    WGenH.prodMap (wInvOver 𝔛) (genPt p) ≫ F.kQ =
      F.kQ ≫ (endoBaseChange (toBase p (ΓM M H) hj) ℚ (wInvOver 𝔛)).1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, F.hkQ₁, WGenH.prodMap_fst, Category.assoc, endoBaseChange_fst, ← Category.assoc, F.hkQ₁]
  · rw [Category.assoc, F.hkQ₂, WGenH.prodMap_snd_assoc, Category.assoc, (endoBaseChange _ ℚ _).2, F.hkQ₂]

theorem xQ_prePt (y : Pt 𝔛) :
    (F.xQ (prePt y)).1 = ptTranslate (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (eQ 𝔛) (F.xQ y).1 (F.xQ y).2 := by
  rw [ptTranslate, prodMapIso_inv_fst, graphOver_fst_assoc]
  change (prePt y).1 ≫ 𝔛.eeta ≫ F.kQ = (y.1 ≫ 𝔛.eeta ≫ F.kQ) ≫ _
  rw [← Category.assoc, prePt_eeta]
  simp only [Category.assoc]
  rw [F.prodMap_wInv_kQ]

theorem xQ_εbar : (F.xQ F.εbar).1 = specMap ℚ (AlgebraicClosure ℚ) ≫ (sectionBaseChange ℚ 𝔛.εinf).1 := by
  apply pullback.hom_ext
  · change ((F.εbar).1 ≫ 𝔛.eeta ≫ F.kQ) ≫ _ = _
    rw [Category.assoc, Category.assoc, F.hkQ₁, F.hεbar, Category.assoc, sectionBaseChange_coe_fst, genPt_eq,
      Category.assoc]
  · change ((F.εbar).1 ≫ 𝔛.eeta ≫ F.kQ) ≫ _ = _
    rw [Category.assoc, Category.assoc, F.hkQ₂, reassoc_of% 𝔛.heeta, reassoc_of% (F.εbar).2,
      Category.assoc, sectionBaseChange_coe_snd, Category.comp_id]

def DvOf (y : Pt 𝔛) : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) :=
  (F.hAJ y F.εbar F.hεbar).choose

theorem coe_DvOf (y : Pt 𝔛) :
    (F.DvOf y : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
      Finsupp.single (𝔛.Meta.pointEquivPlace y) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace F.εbar) 1 :=
  (F.hAJ y F.εbar F.hεbar).choose_spec.1

theorem pts_mk_DvOf (y : Pt 𝔛) : (F.pts (Pic0.mk (F.DvOf y))).1 = y.1 ≫ F.ajbar :=
  (F.hAJ y F.εbar F.hεbar).choose_spec.2

abbrev gOf (y : Pt 𝔛) : JH M H := Pic0.mk (F.DvOf y)

theorem mem_closure_range_gOf (x : JH M H) : x ∈ AddSubgroup.closure (Set.range F.gOf) := by
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one 𝔛.Meta.toBase 𝔛.Meta.ffEquiv 𝔛.Meta.ffEquiv_algebraMap
  refine mem_closure_of_forall_sub_single (IsCurveOver.deg_eq_one_of_isAlgClosed) (𝔛.Meta.pointEquivPlace F.εbar)
    (fun v => F.DvOf (𝔛.Meta.pointEquivPlace.symm v)) (fun v => ?_) (Set.range F.gOf) (fun v => Set.mem_range_self _) x
  rw [coe_DvOf, Equiv.apply_symm_apply]

theorem smul_gOf (y : Pt 𝔛) : F.wgen • F.gOf y = F.gOf (prePt y) - F.gOf (prePt F.εbar) := by
  rw [SemilinearAut.pic0_smul_mk]
  change Pic0.mk _ = (QuotientAddGroup.mk' _) _ - (QuotientAddGroup.mk' _) _
  rw [← map_sub]
  change Pic0.mk _ = Pic0.mk _
  congr 1
  apply Subtype.ext
  rw [SemilinearAut.coe_degZeroSMulHom, AddSubgroupClass.coe_sub, coe_DvOf, coe_DvOf, coe_DvOf, smul_sub,
    SemilinearAut.smul_single, SemilinearAut.smul_single, ← F.pointEquivPlace_prePt, ← F.pointEquivPlace_prePt]
  abel

set_option linter.unusedVariables false in

abbrev cQ (𝔛 : XHDRModelAtP p M H hpM hj) : pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ) ⟶ Spec (CommRingCat.of ℚ) :=
  baseChange (R p) (toBase p (ΓM M H) hj) ℚ

def aQ (y : Pt 𝔛) : SchemeHomOver (specMap ℚ (AlgebraicClosure ℚ)) (F.D.baseChange ℚ).toBase :=
  ⟨(F.xQ y).1 ≫ F.ajQ.1, (Category.assoc _ _ _).trans ((congrArg ((F.xQ y).1 ≫ ·) F.ajQ.2).trans (F.xQ y).2)⟩

theorem εK_comp :
    (specMap ℚ (AlgebraicClosure ℚ) ≫ (sectionBaseChange ℚ 𝔛.εinf).1) ≫ cQ 𝔛 = specMap ℚ (AlgebraicClosure ℚ) :=
  (Category.assoc _ _ _).trans ((congrArg (specMap ℚ (AlgebraicClosure ℚ) ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
    (Category.comp_id _))

abbrev Omod [IsSeparated (cQ 𝔛)] (z : Pt 𝔛) :
    (pullback (cQ 𝔛) (specMap ℚ (AlgebraicClosure ℚ))).Modules :=
  (RelEffCartierDiv.ofPoint (cQ 𝔛) (F.xQ z).1 (F.xQ z).2).lineBundle

abbrev Imod [IsSeparated (cQ 𝔛)] (z : Pt 𝔛) :
    (pullback (cQ 𝔛) (specMap ℚ (AlgebraicClosure ℚ))).Modules :=
  (RelEffCartierDiv.ofPoint (cQ 𝔛) (F.xQ z).1 (F.xQ z).2).idealModule

abbrev IεK (𝔛 : XHDRModelAtP p M H hpM hj) [IsSeparated (cQ 𝔛)] :
    (pullback (cQ 𝔛) (specMap ℚ (AlgebraicClosure ℚ))).Modules :=
  (RelEffCartierDiv.ofPoint (cQ 𝔛) (specMap ℚ (AlgebraicClosure ℚ) ≫ (sectionBaseChange ℚ 𝔛.εinf).1) εK_comp).idealModule

abbrev κ' (𝔛 : XHDRModelAtP p M H hpM hj) :
    pullback (cQ 𝔛) (specMap ℚ (AlgebraicClosure ℚ)) ≅ pullback (toBase p (ΓM M H) hj) (genPt p) :=
  κτ (toBase p (ΓM M H) hj) ℚ (specMap ℚ (AlgebraicClosure ℚ)) (genPt_eq p)

theorem nonempty_poincare_gOf_iso [IsSeparated (cQ 𝔛)] (y : Pt 𝔛) :
    Nonempty ((F.hD.poincare.pullbackAlong (F.pts (F.gOf y))).L ≅
      (Scheme.Modules.pullback (κ' 𝔛).inv).obj (F.Omod y ⊗ IεK 𝔛)) := by
  have hy : (F.pts (F.gOf y)).1 = (F.aQ y).1 ≫ pullback.fst F.D.toBase (specMap (R p) ℚ) := by
    rw [pts_mk_DvOf, F.hajbar]
    simp only [aQ, xQ, Category.assoc]
  obtain ⟨i₁⟩ := nonempty_poincare_pullbackAlong_iso_of_eq_fst (toBase p (ΓM M H) hj) 𝔛.εinf ℚ F.hD F.hDQ F.hpoinc
    (genPt_eq p) (F.aQ y) _ hy
  obtain ⟨i₂⟩ := F.hajQ (AlgebraicClosure ℚ) (specMap ℚ (AlgebraicClosure ℚ)) (F.xQ y)
  exact ⟨i₁ ≪≫ (Scheme.Modules.pullback (κ' 𝔛).inv).mapIso i₂⟩

private theorem _root_.WGenC.ptTranslate_congr {𝒞 S : Scheme.{0}} (f : 𝒞 ⟶ S) {T : Scheme.{0}} {g : T ⟶ S}
    (e : pullback f g ≅ pullback f g) {a a' : T ⟶ 𝒞} (h : a = a') (ha : a ≫ f = g) (ha' : a' ≫ f = g) :
    ptTranslate f e a ha = ptTranslate f e a' ha' := by
  subst h; rfl

p2m_alias "P2MW.S_ModularCurve_XHDRModelAtP_nonempty_poincare_pullbackAlong_pts_smul_iso_pullback_w_of_abelJacobiPin.WGenC.ptTranslate_congr" "WGenC.ptTranslate_congr"
private theorem _root_.WGenC.ofPoint_congr {𝒞 S : Scheme.{0}} (f : 𝒞 ⟶ S) [IsSeparated f] {T : Scheme.{0}} {g : T ⟶ S}
    {a a' : T ⟶ 𝒞} (h : a = a') (ha : a ≫ f = g) (ha' : a' ≫ f = g) :
    RelEffCartierDiv.ofPoint f a ha = RelEffCartierDiv.ofPoint f a' ha' := by
  subst h; rfl

p2m_alias "P2MW.S_ModularCurve_XHDRModelAtP_nonempty_poincare_pullbackAlong_pts_smul_iso_pullback_w_of_abelJacobiPin.WGenC.ofPoint_congr" "WGenC.ofPoint_congr"

theorem compat_gOf (y : Pt 𝔛) :
    Compat F.hD F.pts (Scheme.Modules.pullback (WGenH.prodMap (wOver 𝔛) (genPt p)))
      (DistribSMul.toAddMonoidHom (JH M H) F.wgen) (F.gOf y) := by
  haveI := F.hsep
  haveI : SmoothOfRelativeDimension 1 (cQ 𝔛) := 𝔛.smooth_generic

  let y' := prePt y
  let e' := prePt F.εbar
  let B : JH M H → (pullback (toBase p (ΓM M H) hj) (genPt p)).Modules := fun z => (F.hD.poincare.pullbackAlong (F.pts z)).L
  let Φ := Scheme.Modules.pullback (WGenH.prodMap (wOver 𝔛) (genPt p))
  let κi := Scheme.Modules.pullback (κ' 𝔛).inv

  obtain ⟨iy⟩ := F.nonempty_poincare_gOf_iso y
  obtain ⟨iy'⟩ := F.nonempty_poincare_gOf_iso y'
  obtain ⟨ie'⟩ := F.nonempty_poincare_gOf_iso e'

  have he : (eQ 𝔛).inv ≫ pullback.snd _ _ = pullback.snd _ _ := eQ_inv_snd
  obtain ⟨jO⟩ := nonempty_pullback_lineBundle_iso (f := cQ 𝔛) he (F.xQ y).1 (F.xQ y).2
  obtain ⟨jI⟩ := nonempty_pullback_idealModule_iso (f := cQ 𝔛) he
    (specMap ℚ (AlgebraicClosure ℚ) ≫ (sectionBaseChange ℚ 𝔛.εinf).1) εK_comp
  have hpty : ptTranslate (cQ 𝔛) (eQ 𝔛) (F.xQ y).1 (F.xQ y).2 = (F.xQ y').1 := (F.xQ_prePt y).symm
  have hptε : ptTranslate (cQ 𝔛) (eQ 𝔛) (specMap ℚ (AlgebraicClosure ℚ) ≫ (sectionBaseChange ℚ 𝔛.εinf).1) εK_comp =
      (F.xQ e').1 := by
    rw [F.xQ_prePt, ptTranslate_congr (cQ 𝔛) (eQ 𝔛) F.xQ_εbar.symm εK_comp (F.xQ F.εbar).2]
  have jO' : (Scheme.Modules.pullback (eQ 𝔛).hom).obj (F.Omod y) ≅ F.Omod y' :=
    jO ≪≫ eqToIso (congrArg RelEffCartierDiv.lineBundle (ofPoint_congr (cQ 𝔛) hpty _ _))
  have jI' : (Scheme.Modules.pullback (eQ 𝔛).hom).obj (IεK 𝔛) ≅ F.Imod e' :=
    jI ≪≫ eqToIso (congrArg RelEffCartierDiv.idealModule (ofPoint_congr (cQ 𝔛) hptε _ _))
  have T2 : (Scheme.Modules.pullback (eQ 𝔛).hom).obj (F.Omod y ⊗ IεK 𝔛) ≅ F.Omod y' ⊗ F.Imod e' :=
    Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (jO' ⊗ᵢ jI')

  have T3 : Φ.obj (B (F.gOf y)) ≅ κi.obj (F.Omod y' ⊗ F.Imod e') :=
    Φ.mapIso iy ≪≫ pullbackProdMapκτInvIso (toBase p (ΓM M H) hj) ℚ (wOver 𝔛) (specMap ℚ (AlgebraicClosure ℚ))
      (genPt_eq p) _ ≪≫ κi.mapIso T2

  obtain ⟨sub⟩ := nonempty_poincare_pts_sub_tensor_iso F.hD F.pts F.hpts_law (F.gOf y') (F.gOf e')
  obtain ⟨neg⟩ := nonempty_poincare_pts_neg_tensor_iso F.hD F.pts F.hpts_law (F.gOf e')
  obtain ⟨ie⟩ := nonempty_idealModule_tensor_lineBundle_iso
    (RelEffCartierDiv.ofPoint (cQ 𝔛) (F.xQ e').1 (F.xQ e').2) (RelEffCartierDiv.isInvertible_I _)
  have inner : (F.Omod y' ⊗ F.Imod e') ⊗ (F.Omod e' ⊗ IεK 𝔛) ≅ F.Omod y' ⊗ IεK 𝔛 :=
    α_ _ _ _ ≪≫ (Iso.refl _ ⊗ᵢ ((α_ _ _ _).symm ≪≫ (ie ⊗ᵢ Iso.refl _) ≪≫ λ_ _))
  have i4 : B (F.gOf y' - F.gOf e') ⊗ B (F.gOf e') ≅ κi.obj (F.Omod y' ⊗ F.Imod e') ⊗ B (F.gOf e') :=
    sub ≪≫ iy' ≪≫ κi.mapIso inner.symm ≪≫ (Functor.Monoidal.μIso κi _ _).symm ≪≫ (Iso.refl _ ⊗ᵢ ie'.symm)
  have Ziso : B (F.gOf y' - F.gOf e') ≅ κi.obj (F.Omod y' ⊗ F.Imod e') := isoOfTensorRightIso i4 (β_ _ _ ≪≫ neg)

  show Nonempty ((F.hD.poincare.pullbackAlong (F.pts (F.wgen • F.gOf y))).L ≅ Φ.obj (B (F.gOf y)))
  rw [smul_gOf]
  exact ⟨Ziso ≪≫ T3.symm⟩

theorem compat (x : JH M H) :
    Nonempty ((F.hD.poincare.pullbackAlong (F.pts (F.wgen • x))).L ≅
      (Scheme.Modules.pullback (WGenH.prodMap (wOver 𝔛) (genPt p))).obj (F.hD.poincare.pullbackAlong (F.pts x)).L) := by
  have h := compat_of_mem_closure F.hD F.pts F.hpts_law (Scheme.Modules.pullback (WGenH.prodMap (wOver 𝔛) (genPt p)))
    (DistribSMul.toAddMonoidHom (JH M H) F.wgen) (S := Set.range F.gOf) ?_ (F.mem_closure_range_gOf x)
  · exact h
  · rintro _ ⟨y, rfl⟩
    exact F.compat_gOf y

end AJFrame

end Frame

end WGenC

end

set_option maxHeartbeats 3200000 in
open ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP in
theorem solution
    (p : ℕ)
    [Fact p.Prime]
    (M : ℕ)
    [NeZero M]
    (H : Subgroup (ZMod M)ˣ)
    (hpM : p ∣ M)
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (pts : ModularCurve.JH M H → SchemeHomOver (genPt p) D.toBase)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
    (hsep : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (D.baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ D.P)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hpoinc : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))
    (hajQ : (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
        ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
        ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
        (Category.comp_id t)))).idealModule)))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hpts_law : (∀ x y : JH M H,
        pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y)))
    (hAJ : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y) :
    ∀ x : ModularCurve.JH M H,
      Nonempty ((hD.poincare.pullbackAlong (pts (wgen • x))).L ≅
        (Scheme.Modules.pullback
          (pullback.map (toBase p (ΓM M H) hj) (genPt p) (toBase p (ΓM M H) hj) (genPt p) 𝔛.w.hom (𝟙 _) (𝟙 _)
            (by rw [𝔛.w_over, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp]))).obj
          (hD.poincare.pullbackAlong (pts x)).L) := by
  intro x
  exact WGenC.AJFrame.compat
    (𝔛 := 𝔛) ⟨D, pts, hD, hDQ, hsep, ajQ, kQ, ajbar, εbar, hpoinc, hajQ, hkQ₁, hkQ₂, hajbar, hεbar, hpts_law, hAJ, wgen, hwgen⟩ x

end S_ModularCurve_XHDRModelAtP_nonempty_poincare_pullbackAlong_pts_smul_iso_pullback_w_of_abelJacobiPin
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_nonempty_poincare_pullbackAlong_pts_smul_iso_pullback_w_of_abelJacobiPin (solution)
