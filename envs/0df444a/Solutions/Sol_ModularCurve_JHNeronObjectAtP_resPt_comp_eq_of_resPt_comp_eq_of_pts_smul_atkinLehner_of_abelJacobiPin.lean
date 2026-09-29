-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.resPt_comp_eq_of_resPt_comp_eq_of_pts_smul_atkinLehner_of_abelJacobiPin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/10734141-7898-5244-878d-7c13514a5df1

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Theorems.Thm_ModularCurve_XHDRModelAtP_nonempty_poincare_pullbackAlong_pts_smul_iso_pullback_w_of_abelJacobiPin
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_addSubgroup_extendsToPlace_addMonoidHom_gluedPic0_eq_ptsSp_symm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_resPt_comp_eq_of_resPt_comp_eq_of_pts_smul_atkinLehner_of_abelJacobiPin
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard

namespace KStabH

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

theorem exists_translate_section {D : GoodReductionJacobian.RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (v : SchemeHomOver c c)
    {A : Type u} [CommRing A] [IsLocalRing A] (σ : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    {K : Type u} [CommRing K] [IsLocalRing K] {τ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)}
    (b : SchemeHomOver τ σ)
    (y y' : SchemeHomOver τ D.toBase)
    (hy' : Nonempty ((h.poincare.pullbackAlong y').L ≅
      (Scheme.Modules.pullback (prodMap v τ)).obj (h.poincare.pullbackAlong y).L))
    (s : SchemeHomOver σ D.toBase) (hs : y.1 = b.1 ≫ s.1) :
    ∃ s' : SchemeHomOver σ D.toBase, y'.1 = b.1 ≫ s'.1 ∧
      Nonempty ((h.poincare.pullbackAlong s').L ≅
        (Scheme.Modules.pullback (prodMap v σ)).obj (h.poincare.pullbackAlong s).L) := by
  let M : RigidifiedLineBundle c ε σ := h.poincare.pullbackAlong s
  have hM : FibrewiseAlgEquivZero M := (algEquivZeroCut c ε).pullback_mem _ _ s _ h.poincare_mem
  let M' : RigidifiedLineBundle c ε σ := translate v M
  have hM' : FibrewiseAlgEquivZero M' := fibrewiseAlgEquivZero_pullback_prodMap v M hM M' (Iso.refl _)
  obtain ⟨s', ⟨es'⟩, -⟩ := h.univ σ M' hM'
  refine ⟨s', ?_, ⟨es'⟩⟩
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

noncomputable def pullbackAlong_postComp_iso {D : GoodReductionJacobian.RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (v : SchemeHomOver c c)
    {T T' : Scheme.{u}} {σ : T ⟶ Spec (CommRingCat.of R)} {τ : T' ⟶ Spec (CommRingCat.of R)}
    (r : SchemeHomOver τ σ) (s t : SchemeHomOver σ D.toBase)
    (e : (h.poincare.pullbackAlong t).L ≅ (Scheme.Modules.pullback (prodMap v σ)).obj (h.poincare.pullbackAlong s).L) :
    (h.poincare.pullbackAlong (postComp t r)).L ≅
      (Scheme.Modules.pullback (prodMap v τ)).obj
        ((Scheme.Modules.pullback (baseChangeSnd c (postComp s r))).obj h.poincare.L) :=
  ((Scheme.Modules.pullbackCongr (baseChangeSnd_comp c t r).symm).app h.poincare.L) ≪≫
    ((Scheme.Modules.pullbackComp (baseChangeSnd c r) (baseChangeSnd c t)).app h.poincare.L).symm ≪≫
    (Scheme.Modules.pullback (baseChangeSnd c r)).mapIso e ≪≫
    pullbackProdMapBaseChangeSndIso v r _ ≪≫
    (Scheme.Modules.pullback (prodMap v τ)).mapIso
      (((Scheme.Modules.pullbackComp (baseChangeSnd c r) (baseChangeSnd c s)).app h.poincare.L) ≪≫
        (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c s r)).app h.poincare.L)

theorem postComp_eq_of_translate {D : GoodReductionJacobian.RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (v : SchemeHomOver c c)
    {T T' : Scheme.{u}} {σ : T ⟶ Spec (CommRingCat.of R)} {τ : T' ⟶ Spec (CommRingCat.of R)}
    (r : SchemeHomOver τ σ) (s₁ s₂ t₁ t₂ : SchemeHomOver σ D.toBase)
    (e₁ : (h.poincare.pullbackAlong t₁).L ≅ (Scheme.Modules.pullback (prodMap v σ)).obj (h.poincare.pullbackAlong s₁).L)
    (e₂ : (h.poincare.pullbackAlong t₂).L ≅ (Scheme.Modules.pullback (prodMap v σ)).obj (h.poincare.pullbackAlong s₂).L)
    (hs : postComp s₁ r = postComp s₂ r) : postComp t₁ r = postComp t₂ r :=
  h.ext_of_iso τ _ _ ⟨pullbackAlong_postComp_iso h v r s₁ t₁ e₁ ≪≫
    (Scheme.Modules.pullback (prodMap v τ)).mapIso
      ((Scheme.Modules.pullbackCongr (congrArg (baseChangeSnd c) hs)).app h.poincare.L) ≪≫
    (pullbackAlong_postComp_iso h v r s₂ t₂ e₂).symm⟩

end KStabH

set_option autoImplicit false
open scoped MatrixGroups
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

set_option maxHeartbeats 6400000 in
open ModularCurve in
set_option linter.unusedVariables false in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ))
    (hsep : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ O.G)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hpoinc : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L))
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
    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst O.g (specMap (R p) ℚ))
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hpts_law : (∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)))
    (hAJ : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y) :
    ∀ (x₁ x₂ : ModularCurve.JH M H) (s₁ s₂ s₁' s₂' : NeronModelInfra.SchemeHomOver Λ.σA O.g),
      (O.pts x₁).1 = barPt Pl ≫ s₁.1 → (O.pts x₂).1 = barPt Pl ≫ s₂.1 →
      (O.pts (wgen • x₁)).1 = barPt Pl ≫ s₁'.1 → (O.pts (wgen • x₂)).1 = barPt Pl ≫ s₂'.1 →
      resPt Pl ≫ s₁.1 = resPt Pl ≫ s₂.1 → resPt Pl ≫ s₁'.1 = resPt Pl ≫ s₂'.1 := by

  intro x₁ x₂ s₁ s₂ s₁' s₂' hs₁ hs₂ hs₁' hs₂' hres

  obtain ⟨dom, sp, hdom, hspv, -, -, -, -⟩ :=
    ModularCurve.JHNeronObjectAtP.exists_addSubgroup_extendsToPlace_addMonoidHom_gluedPic0_eq_ptsSp_symm
      p M H hpM Pl hPl Λ O

  have hgen := ModularCurve.XHDRModelAtP.nonempty_poincare_pullbackAlong_pts_smul_iso_pullback_w_of_abelJacobiPin
    p M H hpM hj 𝔛 ⟨O.G, O.g, (O.L.one (𝟙 _)).1, (O.L.one (𝟙 _)).2⟩ O.pts hD hDQ hsep ajQ kQ ajbar εbar hpoinc hajQ
    hkQ₁ hkQ₂ hajbar hεbar hpts_law hAJ wgen hwgen

  obtain ⟨t₁, ht₁, ⟨e₁⟩⟩ := KStabH.exists_translate_section hD ⟨𝔛.w.hom, 𝔛.w_over⟩ Λ.σA
    (⟨barPt Pl, Λ.hσA⟩ : SchemeHomOver (genPt p) Λ.σA) (O.pts x₁) (O.pts (wgen • x₁)) (hgen x₁) s₁ hs₁
  obtain ⟨t₂, ht₂, ⟨e₂⟩⟩ := KStabH.exists_translate_section hD ⟨𝔛.w.hom, 𝔛.w_over⟩ Λ.σA
    (⟨barPt Pl, Λ.hσA⟩ : SchemeHomOver (genPt p) Λ.σA) (O.pts x₂) (O.pts (wgen • x₂)) (hgen x₂) s₂ hs₂

  have h12 : resPt Pl ≫ t₁.1 = resPt Pl ≫ t₂.1 :=
    congrArg Subtype.val (KStabH.postComp_eq_of_translate hD ⟨𝔛.w.hom, 𝔛.w_over⟩
      (⟨resPt Pl, rfl⟩ : SchemeHomOver (resPt Pl ≫ Λ.σA) Λ.σA) s₁ s₂ t₁ t₂ e₁ e₂ (Subtype.ext hres))

  have hwd : ∀ (z : JH M H) (t t' : SchemeHomOver Λ.σA O.g),
      (O.pts z).1 = barPt Pl ≫ t.1 → (O.pts z).1 = barPt Pl ≫ t'.1 → resPt Pl ≫ t.1 = resPt Pl ≫ t'.1 := by
    intro z t t' ht ht'
    have hz : z ∈ dom := (hdom z).2 ⟨t, ht⟩
    have e := (hspv ⟨z, hz⟩ t ht).symm.trans (hspv ⟨z, hz⟩ t' ht')
    exact congrArg Subtype.val (O.ptsSp.symm.injective e)
  rw [← hwd _ t₁ s₁' ht₁ hs₁', ← hwd _ t₂ s₂' ht₂ hs₂', h12]

end S_ModularCurve_JHNeronObjectAtP_resPt_comp_eq_of_resPt_comp_eq_of_pts_smul_atkinLehner_of_abelJacobiPin
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_resPt_comp_eq_of_resPt_comp_eq_of_pts_smul_atkinLehner_of_abelJacobiPin (solution)
