-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_divisor_ord_presentation_poincare_pullbackAlong_eq_of_barPt_comp_eq_pts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/c707bf67-d1ad-515d-b1aa-430170b4dff7

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_forall_eq_mul_of_presentations
import Theorems.Thm_ModularCurve_XHDRModelAtP_isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_forall_divisor_congrRingEquiv_eq_add_ord_of_range_eq_lSpaceOn_restrict_poincare_pullbackAlong_of_barPt_comp_eq_pts
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_divisor_ord_presentation_poincare_pullbackAlong_eq_of_barPt_comp_eq_pts
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false
open scoped MatrixGroups
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

universe u

noncomputable section

namespace GPH

section Transfer

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X) [IsOpenImmersion f]

theorem exists_presentation_restrict (L : X.Modules)
    (φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L, U), φ V (L.presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (eK : X.functionField →+* Y.functionField)
    (heK : ∀ (U : X.Opens) (hne : Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ U))) (a : Γ(X, U)),
      haveI : Nonempty (Scheme.Opens.toScheme U) := by
        obtain ⟨⟨y, hy⟩⟩ := hne
        exact ⟨⟨f.base y, hy⟩⟩
      eK (X.germToFunctionField U a) = Y.germToFunctionField (f ⁻¹ᵁ U) ((f.app U).hom a)) :
    ∃ φ₀ : ∀ V : Y.Opens, Γ(L.restrict f, V) →+ (Y.functionField : Type u),
      (∀ (U V : Y.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(L.restrict f, U), φ₀ V ((L.restrict f).presheaf.map (homOfLE h).op m) = φ₀ U m) ∧
      (∀ (U : Y.Opens) [Nonempty U] (a : Γ(Y, U)) (m : Γ(L.restrict f, U)),
          φ₀ U (a • m) = algebraMap Γ(Y, U) Y.functionField a * φ₀ U m) ∧
      (∀ U : Y.Opens, Nonempty U → Function.Injective (φ₀ U)) ∧
      (∀ (V : Y.Opens) (m : Γ(L, f ''ᵁ V)), φ₀ V m = eK (φ (f ''ᵁ V) m)) := by
  classical
  have himNE : ∀ V : Y.Opens, Nonempty V → Nonempty (Scheme.Opens.toScheme (f ''ᵁ V)) := fun V ⟨⟨v, hv⟩⟩ =>
    ⟨⟨f.base v, ⟨v, hv, rfl⟩⟩⟩
  refine ⟨fun V => (eK : X.functionField →+ Y.functionField).comp (show Γ(L, f ''ᵁ V) →+ (X.functionField : Type u) from φ (f ''ᵁ V)),
    ?_, ?_, ?_, ?_⟩
  · intro U V h hV m
    haveI := himNE V hV
    show eK (φ (f ''ᵁ V) ((L.restrict f).presheaf.map (homOfLE h).op m)) = eK (φ (f ''ᵁ U) m)
    rw [Scheme.Modules.restrict_map]
    have hle : f ''ᵁ V ≤ f ''ᵁ U := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, h hx, rfl⟩
    rw [show (f.opensFunctor.map (homOfLE h)).op = (homOfLE hle).op from rfl]
    exact congrArg eK (hnat (f ''ᵁ U) (f ''ᵁ V) hle inferInstance m)
  · intro V hV a m
    haveI := himNE V hV
    have hne' : Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ f ''ᵁ V)) := by
      obtain ⟨⟨v, hv⟩⟩ := hV
      exact ⟨⟨v, show f.base v ∈ f ''ᵁ V from ⟨v, hv, rfl⟩⟩⟩
    show eK (φ (f ''ᵁ V) (a • m)) = algebraMap Γ(Y, V) Y.functionField a * eK (φ (f ''ᵁ V) m)
    have hsm : (a • m : Γ(L.restrict f, V)) = (((f.appIso V).inv.hom a • (show Γ(L, f ''ᵁ V) from m)) : Γ(L, f ''ᵁ V)) := rfl
    rw [hsm, hsmul, map_mul]
    congr 1
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
    have h1 := heK (f ''ᵁ V) hne' ((f.appIso V).inv.hom a)
    simp only at h1
    rw [h1]
    show (((f.appIso V).inv ≫ f.app (f ''ᵁ V)) ≫ Y.germToFunctionField (f ⁻¹ᵁ f ''ᵁ V)).hom a = (Y.germToFunctionField V).hom a
    rw [Scheme.Hom.appIso_inv_app]
    unfold Scheme.germToFunctionField
    rw [TopCat.Presheaf.germ_res]
  · intro V hV
    haveI := himNE V hV
    exact eK.injective.comp (hinj (f ''ᵁ V) inferInstance)
  · intro V m
    rfl

end Transfer

section Helpers

variable {X : Scheme.{u}}

theorem isInvertible_of_iso {M N : X.Modules} (e : M ≅ N) (hM : Scheme.Modules.IsInvertible M) :
    Scheme.Modules.IsInvertible N := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hM.1 x
  exact ⟨U, hxU, ⟨((Scheme.Modules.pullback U.ι).mapIso e).symm ≪≫ eU⟩⟩

theorem ne_zero_of_isFrameOn {M : X.Modules} {U : X.Opens} [Nontrivial Γ(X, U)] {s : Γ(M, U)}
    (hs : Scheme.Modules.IsFrameOn s U) : s ≠ 0 := by
  intro h
  have h1 : (1 : Γ(X, U)) • M.presheaf.map (homOfLE (le_refl U)).op s = 0 := by
    rw [h, map_zero, smul_zero]
  have := (hs.smul_eq_zero_iff le_rfl le_rfl (1 : Γ(X, U))).mp h1
  exact one_ne_zero this

theorem ord_eq_neg_of_exp_eq_adicValuation {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) (f : F) (d : ℤ) (h : WithZero.exp d = v.adicValuation f) : v.ord f = -d := by
  unfold AlgebraicCurve.Place.ord
  rw [← h, WithZero.log_exp]

end Helpers

end GPH

end

set_option maxHeartbeats 3200000 in
open ModularCurve in

theorem solution
    (p : ℕ)
    [Fact p.Prime]
    (M : ℕ)
    [NeZero M]
    (hpM : p ∣ M)
    (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p]
    [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
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
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).zeroSection)
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
    (hajbar_over : ajbar ≫ O.g = 𝔛.Meta.toBase ≫ genPt p)
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1)
    (hpts_law : (∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)))
    (hAJ : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))
    (ρ : ModularCurve.XHDRLevel.R p →+* ↥Pl)
    (hρ : Pl.subtype.comp ρ = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    [hint : IsIntegral (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))]

    (z : ModularCurve.JH M H)
    (D' : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H)))
    (hD' : AlgebraicCurve.Pic0.mk D' = z)
    (σ : NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) O.g)
    (hσ : ModularCurve.JZeroNeronObjectAtP.barPt Pl ≫ σ.1 = (O.pts z).1)

    (φ : ∀ U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, Γ((hD.poincare.pullbackAlong σ).L, U) →+ ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField : Type))
    (hφnat : ∀ (U V : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ((hD.poincare.pullbackAlong σ).L, U), φ V ((hD.poincare.pullbackAlong σ).L.presheaf.map (homOfLE h).op m) = φ U m)
    (hφsmul : ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) [Nonempty U] (a : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)) (m : Γ((hD.poincare.pullbackAlong σ).L, U)),
      φ U (a • m) = algebraMap Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U) (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField a * φ U m)
    (hφinj : ∀ U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, Nonempty U → Function.Injective (φ U))

    (e : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField ≃+* ↥(ModularCurve.xHFunctionFieldBar M H))
    (he : ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (hne : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))) (a : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)),
      haveI : Nonempty (Scheme.Opens.toScheme U) := by
        obtain ⟨⟨x, hx⟩⟩ := hne
        exact ⟨⟨gA.base x, hx⟩⟩
      e ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField U a) =
        𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom a))) :
    ∃ (Dφ : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))
      (g₁ : ↥(ModularCurve.xHFunctionFieldBar M H)), g₁ ≠ 0 ∧

      (∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
        Dφ v = (D' : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) v + v.ord g₁) ∧

      ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (q : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (hq : gA.base (q.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) ∈ U) (m : Γ((hD.poincare.pullbackAlong σ).L, U)),
        haveI : Nonempty (Scheme.Opens.toScheme U) := ⟨⟨_, hq⟩⟩
        (φ U m ≠ 0 → -Dφ (𝔛.Meta.pointEquivPlace q) ≤ (𝔛.Meta.pointEquivPlace q).ord (e (φ U m))) ∧
        ((∀ (W : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (hW : W ≤ U), gA.base (q.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) ∈ W →
            ∀ m' : Γ((hD.poincare.pullbackAlong σ).L, W), ∃ a : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), W), m' = a • (hD.poincare.pullbackAlong σ).L.presheaf.map (homOfLE hW).op m) →
          (𝔛.Meta.pointEquivPlace q).ord (e (φ U m)) = -Dφ (𝔛.Meta.pointEquivPlace q)) := by
  classical
  letI := 𝔛.Meta.functionFieldAlgebra

  obtain ⟨-, hdense, hgAo⟩ := ModularCurve.XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
    p M hpM H Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂
  haveI := hgAo

  have hL0 : Scheme.Modules.IsInvertible (((hD.poincare.pullbackAlong σ).L).restrict gA) :=
    GPH.isInvertible_of_iso ((Scheme.Modules.restrictFunctorIsoPullback gA).app _).symm
      ((hD.poincare.pullbackAlong σ).isInvertible.pullback gA)

  have heK : ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
      (hne : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))) (a : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)),
      haveI : Nonempty (Scheme.Opens.toScheme U) := by
        obtain ⟨⟨y, hy⟩⟩ := hne
        exact ⟨⟨gA.base y, hy⟩⟩
      ((𝔛.Meta.ffEquiv : ↥(ModularCurve.xHFunctionFieldBar M H) →+* 𝔛.Meta.C.functionField).comp (e : _ →+* _))
        ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField U a) =
        𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom a) := by
    intro U hne a
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, he U hne a, RingEquiv.apply_symm_apply]
  obtain ⟨φ₀, h0nat, h0smul, h0inj, h0eq⟩ := GPH.exists_presentation_restrict gA ((hD.poincare.pullbackAlong σ).L) φ hφnat hφsmul hφinj
    ((𝔛.Meta.ffEquiv : ↥(ModularCurve.xHFunctionFieldBar M H) →+* 𝔛.Meta.C.functionField).comp (e : _ →+* _)) heK

  obtain ⟨D₁, φ₁, h1nat, h1smul, h1inj, h1range, h1gen⟩ :=
    Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn 𝔛.Meta.toBase (((hD.poincare.pullbackAlong σ).L).restrict gA) hL0

  have hsec : ∃ (U : 𝔛.Meta.C.Opens) (m : Γ(((hD.poincare.pullbackAlong σ).L).restrict gA, U)), m ≠ 0 := by
    obtain ⟨U₁, s₁, hη₁, hs₁⟩ := hL0.exists_isFrameOn (genericPoint 𝔛.Meta.C)
    haveI : Nonempty U₁ := ⟨⟨_, hη₁⟩⟩
    exact ⟨U₁, s₁, GPH.ne_zero_of_isFrameOn hs₁⟩
  obtain ⟨g, hg0, hg⟩ := Scheme.Modules.exists_forall_eq_mul_of_presentations (((hD.poincare.pullbackAlong σ).L).restrict gA) φ₁ φ₀
    h1nat h0nat (fun U _ a m => h1smul U a m) (fun U _ a m => h0smul U a m) h1inj h0inj hsec

  obtain ⟨g₂, hg₂, hD₁⟩ := ModularCurve.JHNeronObjectAtP.exists_forall_divisor_congrRingEquiv_eq_add_ord_of_range_eq_lSpaceOn_restrict_poincare_pullbackAlong_of_barPt_comp_eq_pts
      p M hpM hpM2 H hHp Pl hPl hj 𝔛 Λ O hD hDQ hsep ajQ kQ ajbar εbar hpoinc hajQε hajQ hkQ₁ hkQ₂
    hajbar hajbar_over hεbar hεbar_aj hpts_law hAJ ρ hρ gA hgA₁ hgA₂ z D' hD' σ hσ D₁ φ₁ h1nat (fun U _ a m => h1smul U a m) h1inj h1range

  let cK := fun v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) =>
    AlgebraicCurve.Place.congrRingEquiv 𝔛.Meta.ffEquiv 𝔛.Meta.ffEquiv_algebraMap v

  haveI : AlgebraicCurve.IsCurveOver (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) :=
    AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      𝔛.Meta.toBase 𝔛.Meta.ffEquiv 𝔛.Meta.ffEquiv_algebraMap
  have hgK0 : 𝔛.Meta.ffEquiv.symm g ≠ 0 := (map_ne_zero _).2 hg0
  obtain ⟨Dg, hDg, -⟩ := AlgebraicCurve.HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (𝔛.Meta.ffEquiv.symm g) hgK0
  let cKE : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) ≃
      AlgebraicCurve.Place (AlgebraicClosure ℚ) 𝔛.Meta.C.functionField :=
    AlgebraicCurve.Place.congrEquiv 𝔛.Meta.ffEquiv 𝔛.Meta.ffEquiv_algebraMap
  have hordg : ∀ v, (cK v).ord g = v.ord (𝔛.Meta.ffEquiv.symm g) := fun v => by
    rw [← AlgebraicCurve.Place.ord_congrRingEquiv 𝔛.Meta.ffEquiv 𝔛.Meta.ffEquiv_algebraMap v, RingEquiv.apply_symm_apply]
  have hDφ : ∀ v, (Finsupp.equivMapDomain cKE.symm D₁ - Dg) v = D₁ (cK v) - (cK v).ord g := fun v => by
    rw [Finsupp.sub_apply, Finsupp.equivMapDomain_apply, Equiv.symm_symm, hDg v, hordg]
    rfl
  refine ⟨Finsupp.equivMapDomain cKE.symm D₁ - Dg, 𝔛.Meta.ffEquiv.symm (g₂ / g),
    (map_ne_zero _).2 (div_ne_zero hg₂ hg0), ?_, ?_⟩
  · intro v
    have h := hD₁ v
    have hord : v.ord (𝔛.Meta.ffEquiv.symm (g₂ / g)) = (cK v).ord g₂ - (cK v).ord g := by
      rw [← AlgebraicCurve.Place.ord_congrRingEquiv 𝔛.Meta.ffEquiv 𝔛.Meta.ffEquiv_algebraMap v,
        RingEquiv.apply_symm_apply, div_eq_mul_inv, AlgebraicCurve.Place.ord_mul _ hg₂ (inv_ne_zero hg0),
        AlgebraicCurve.Place.ord_inv]
      ring
    rw [hDφ v, hord]
    simp only [cK] at h ⊢
    rw [h]
    ring
  · intro U q hq m

    set y : 𝔛.Meta.C := q.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) with hy
    have hyc : IsClosed ({y} : Set 𝔛.Meta.C) := (pointEquivClosedPoint 𝔛.Meta.toBase q).2
    set V : 𝔛.Meta.C.Opens := gA ⁻¹ᵁ U with hV
    have hyV : y ∈ V := hq
    haveI hVne : Nonempty V := ⟨⟨y, hyV⟩⟩
    have hVU : gA ''ᵁ V ≤ U := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    haveI : Nonempty (Scheme.Opens.toScheme (gA ''ᵁ V)) := ⟨⟨gA.base y, ⟨y, hyV, rfl⟩⟩⟩
    let m₀ : Γ(((hD.poincare.pullbackAlong σ).L).restrict gA, V) :=
      (hD.poincare.pullbackAlong σ).L.presheaf.map (homOfLE hVU).op m

    set w := cK (𝔛.Meta.pointEquivPlace q) with hw
    have hqy : pointEquivClosedPoint 𝔛.Meta.toBase q = ⟨y, hyc⟩ := Subtype.ext rfl
    have hplace : 𝔛.Meta.pointEquivPlace q = 𝔛.Meta.placeOfPoint ⟨y, hyc⟩ := by
      rw [AlgebraicCurve.CurveModel.pointEquivPlace_apply, hqy]
    have hwr : (algebraMap (𝔛.Meta.C.presheaf.stalk y) 𝔛.Meta.C.functionField).range = w.toValuationSubring.toSubring := by
      have hr := 𝔛.Meta.range_stalk_eq ⟨y, hyc⟩
      ext x
      simp only [hw, cK, AlgebraicCurve.Place.congrRingEquiv_toValuationSubring]
      constructor
      · rintro ⟨t, rfl⟩
        show 𝔛.Meta.ffEquiv.symm _ ∈ (𝔛.Meta.pointEquivPlace q).toValuationSubring
        rw [hplace]
        have : (𝔛.Meta.ffEquiv.symm : 𝔛.Meta.C.functionField ≃+* _).toRingHom.comp
            (algebraMap (𝔛.Meta.C.presheaf.stalk y) 𝔛.Meta.C.functionField) t ∈
            (𝔛.Meta.placeOfPoint ⟨y, hyc⟩).toValuationSubring.toSubring := by
          rw [← hr]; exact ⟨t, rfl⟩
        exact this
      · intro hx
        have hx' : 𝔛.Meta.ffEquiv.symm x ∈ (𝔛.Meta.placeOfPoint ⟨y, hyc⟩).toValuationSubring.toSubring := by
          rw [← hplace]; exact hx
        rw [← hr] at hx'
        obtain ⟨t, ht⟩ := hx'
        refine ⟨t, ?_⟩
        have := congrArg 𝔛.Meta.ffEquiv ht
        simpa using this

    have hread : 𝔛.Meta.ffEquiv (e (φ U m)) = g * φ₁ V m₀ := by
      rw [← hg V m₀, h0eq V m₀, hφnat U (gA ''ᵁ V) hVU inferInstance m]
      rfl
    have hordK : (𝔛.Meta.pointEquivPlace q).ord (e (φ U m)) = w.ord (𝔛.Meta.ffEquiv (e (φ U m))) := by
      rw [hw]
      exact (AlgebraicCurve.Place.ord_congrRingEquiv 𝔛.Meta.ffEquiv 𝔛.Meta.ffEquiv_algebraMap _ _).symm
    have hDφq : (Finsupp.equivMapDomain cKE.symm D₁ - Dg) (𝔛.Meta.pointEquivPlace q) = D₁ w - w.ord g := hDφ _
    constructor
    ·
      intro hm0
      obtain ⟨V', hV'aff, hyV', hV'V⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp 𝔛.Meta.C.isBasis_affineOpens) hyV
      replace hV'aff : IsAffineOpen V' := hV'aff
      haveI : Nonempty V' := ⟨⟨y, hyV'⟩⟩
      have hmem : φ₁ V' ((((hD.poincare.pullbackAlong σ).L).restrict gA).presheaf.map (homOfLE hV'V).op m₀) ∈
          (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf 𝔛.Meta.toBase V') D₁ : Set 𝔛.Meta.C.functionField) := by
        rw [← h1range V' hV'aff inferInstance]
        exact ⟨_, rfl⟩
      rw [h1nat V V' hV'V inferInstance m₀] at hmem
      have hwV' : w ∈ AlgebraicCurve.placesOf 𝔛.Meta.toBase V' := ⟨y, hyV', hyc, hwr⟩
      have h2 := (AlgebraicCurve.mem_lSpaceOn_iff_ord.mp hmem) w hwV'
      have hφ1ne : φ₁ V m₀ ≠ 0 := by
        intro h0
        apply hm0
        have : 𝔛.Meta.ffEquiv (e (φ U m)) = 0 := by rw [hread, h0, mul_zero]
        simpa using this
      rcases h2 with h2 | h2
      · exact absurd h2 hφ1ne
      rw [hordK, hread, AlgebraicCurve.Place.ord_mul _ hg0 hφ1ne, hDφq]
      linarith
    ·
      intro hgenm
      have hgen0 : ∀ (W₀ : 𝔛.Meta.C.Opens) (h : W₀ ≤ V), y ∈ W₀ →
          ∀ m' : Γ(((hD.poincare.pullbackAlong σ).L).restrict gA, W₀),
            ∃ a : Γ(𝔛.Meta.C, W₀), m' = a • (((hD.poincare.pullbackAlong σ).L).restrict gA).presheaf.map (homOfLE h).op m₀ := by
        intro W₀ h hyW₀ m'
        have hW₀U : gA ''ᵁ W₀ ≤ U := by
          rintro _ ⟨x, hx, rfl⟩
          exact h hx
        obtain ⟨a, ha⟩ := hgenm (gA ''ᵁ W₀) hW₀U ⟨y, hyW₀, rfl⟩ m'
        refine ⟨(gA.appIso W₀).hom.hom a, ?_⟩
        rw [ha]
        have hsm : ∀ (b : Γ(𝔛.Meta.C, W₀)) (n : Γ(((hD.poincare.pullbackAlong σ).L).restrict gA, W₀)),
            (b • n : Γ(((hD.poincare.pullbackAlong σ).L).restrict gA, W₀)) =
              (((gA.appIso W₀).inv.hom b • (show Γ((hD.poincare.pullbackAlong σ).L, gA ''ᵁ W₀) from n)) :
                Γ((hD.poincare.pullbackAlong σ).L, gA ''ᵁ W₀)) := fun _ _ => rfl
        rw [hsm, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
        congr 1
        show _ = (hD.poincare.pullbackAlong σ).L.presheaf.map (gA.opensFunctor.map (homOfLE h)).op
          ((hD.poincare.pullbackAlong σ).L.presheaf.map (homOfLE hVU).op m)
        rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
        rfl
      have hexp := h1gen V m₀ y hyV hyc hgen0 w hwr
      have hord1 : w.ord (φ₁ V m₀) = -D₁ w := GPH.ord_eq_neg_of_exp_eq_adicValuation w _ _ hexp
      have hφ1ne : φ₁ V m₀ ≠ 0 := by
        intro h0
        have := congrArg w.adicValuation h0
        rw [← hexp, map_zero] at this
        exact WithZero.coe_ne_zero this
      rw [hordK, hread, AlgebraicCurve.Place.ord_mul _ hg0 hφ1ne, hord1, hDφq]
      ring

end S_ModularCurve_JHNeronObjectAtP_exists_divisor_ord_presentation_poincare_pullbackAlong_eq_of_barPt_comp_eq_pts
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_divisor_ord_presentation_poincare_pullbackAlong_eq_of_barPt_comp_eq_pts (solution)
