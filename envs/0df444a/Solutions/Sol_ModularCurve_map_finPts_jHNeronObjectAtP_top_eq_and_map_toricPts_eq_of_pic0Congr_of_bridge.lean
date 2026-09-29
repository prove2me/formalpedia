-- Prove2me | solution 1 for ModularCurve.map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/5d114de3-af13-526c-93c6-3e85cf21737c

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_SheafOfModules_Monoidal
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_mem_finPts_iff_and_isTorsionPoint_section_and_specialPt
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_mem_finPts_iff
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_pullbackHom_inv_comp_pullbackHom_hom_of_iso
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_CharacterLatticePairings
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Theorems.Thm_ModularCurve_jZeroNeronObjectAtP_pts_pic0Congr_eq_pts_comp_pullbackHom_of_modelIso_levelData
import Theorems.Thm_NeronSpecialFibreInfra_exists_mapDomainRingHom_comp_eq_comp_of_comp_one_of_forall_torsion_mul
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_forall_muPt_comp_eq_comp_of_torusMatrix_of_rigid
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_schemeHomOverComp_mul_torusPt_fibreRestrictAlong_of_torsion
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_baseChange_of_field
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_eq_of_muBaseChange_residue_comp_eq
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_eq_of_muBaseChange_residue_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge
p2m_attr_erase "instance" "PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.normModuleFunctor_obj AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"
p2m_attr_erase "simp" "CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing

p2m_open "ModularCurve P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard CategoryTheory.MonoidalCategory"
open scoped MatrixGroups

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve ModularCurve.JZeroNeronObjectAtP"

namespace ModularCurve
p2m_export "ModularCurve" "JHNeronObjectAtP.LevelData JHNeronObjectAtP JHNeronObjectAtP.toricPoint JHNeronObjectAtP.toricPts JZeroNeronObjectAtP.baseRing JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP JZeroNeronObjectAtP.toricPoint JZeroNeronObjectAtP.toricPts jZeroTorsion heckeModuleBar HeckeAlphaBarIntegral HeckeBetaBarIntegral modularFunctionFieldBar JZero qExpand ModularPolynomialData modularFunctionFieldFullC jqModC modularFunctionFieldC inertiaInvariants instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable nodePairsOfPlaces KroneckerCongruence infSubgroup xHFunctionFieldBar JH qExpFunctionFieldC JHNeronObjectAtP.mem_finPts_iff_and_isTorsionPoint_section_and_specialPt JZeroNeronObjectAtP.mem_finPts_iff XHDRLevel.R XHDRLevel.X XHDRLevel.toBase XHDRLevel.ΓM XHDRModelAtP arithFrobC PlaceSpecialization PlaceSpecialization.ProlongationTuple DRLevel.X DRLevel.toBase DRModelPackageLevel jZeroNeronObjectAtP_pts_pic0Congr_eq_pts_comp_pullbackHom_of_modelIso_levelData JZeroNeronObjectAtP.exists_forall_muPt_comp_eq_comp_of_torusMatrix_of_rigid JZeroNeronObjectAtP.schemeHomOverComp_mul_torusPt_fibreRestrictAlong_of_torsion JHNeronObjectAtP.eq_of_muBaseChange_residue_comp_eq JZeroNeronObjectAtP.eq_of_muBaseChange_residue_comp_eq"
namespace NeronCompare
namespace Tor
p2m_open "ModularCurve"

section fibre2

variable {R : Type} [CommRing R] {C : Scheme.{0}}
  {G G₀ : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)} {g₀ : G₀ ⟶ Spec (CommRingCat.of R)}

noncomputable def fibreRestrict₂ {ι ι₀ : C ⟶ Spec (CommRingCat.of R)} (hι : ι = ι₀) (Ψ : SchemeHomOver g g₀) :
    SchemeHomOver (pullback.snd g ι) (pullback.snd g₀ ι₀) :=
  ⟨pullback.lift (pullback.fst g ι ≫ Ψ.1) (pullback.snd g ι) (by rw [Category.assoc, Ψ.2, pullback.condition, hι]),
    pullback.lift_snd _ _ _⟩

@[scoped simp] theorem fibreRestrict₂_fst {ι ι₀ : C ⟶ Spec (CommRingCat.of R)} (hι : ι = ι₀) (Ψ : SchemeHomOver g g₀) :
    (fibreRestrict₂ hι Ψ).1 ≫ pullback.fst g₀ ι₀ = pullback.fst g ι ≫ Ψ.1 := by
  simp only [fibreRestrict₂, pullback.lift_fst]

@[scoped simp] theorem fibreRestrict₂_snd {ι ι₀ : C ⟶ Spec (CommRingCat.of R)} (hι : ι = ι₀) (Ψ : SchemeHomOver g g₀) :
    (fibreRestrict₂ hι Ψ).1 ≫ pullback.snd g₀ ι₀ = pullback.snd g ι := by
  simp only [fibreRestrict₂, pullback.lift_snd]

theorem fibreRestrict₂_rfl (ι : C ⟶ Spec (CommRingCat.of R)) (Ψ : SchemeHomOver g g₀) :
    fibreRestrict₂ (rfl : ι = ι) Ψ = fibreRestrictAlong ι g₀ g Ψ := rfl

end fibre2

section fibre2pts

variable {R R' : Type} [CommRing R] [CommRing R']
  {G G₀ : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)} {g₀ : G₀ ⟶ Spec (CommRingCat.of R)}

theorem toBase_comp_fibreRestrict₂ {ι ι₀ : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} (hι : ι = ι₀)
    (Ψ : SchemeHomOver g g₀) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R'))
    (x : SchemeHomOver s (RelativeGroupLaw.baseChangeStr ι g)) :
    RelativeGroupLaw.baseChangePointToBase ι₀ (NeronModelInfra.schemeHomOverComp x (fibreRestrict₂ hι Ψ)) =
      castOver (by rw [hι]) (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase ι x) Ψ) := by
  subst hι
  rw [fibreRestrict₂_rfl, RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong]
  rfl

theorem fibreRestrict₂_mul {ι ι₀ : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} (hι : ι = ι₀)
    (L : RelativeGroupLaw R g) (L₀ : RelativeGroupLaw R g₀) (Ψ : SchemeHomOver g g₀)
    {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R'))
    (hΨ : ∀ x y : SchemeHomOver (s ≫ ι) g, NeronModelInfra.schemeHomOverComp (L.mul _ x y) Ψ =
      L₀.mul _ (NeronModelInfra.schemeHomOverComp x Ψ) (NeronModelInfra.schemeHomOverComp y Ψ))
    (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr ι g)) :
    NeronModelInfra.schemeHomOverComp ((L.baseChange ι).mul s x y) (fibreRestrict₂ hι Ψ) =
      (L₀.baseChange ι₀).mul s (NeronModelInfra.schemeHomOverComp x (fibreRestrict₂ hι Ψ))
        (NeronModelInfra.schemeHomOverComp y (fibreRestrict₂ hι Ψ)) := by
  subst hι
  rw [fibreRestrict₂_rfl]
  apply (RelativeGroupLaw.baseChangePointEquiv ι s).injective
  change RelativeGroupLaw.baseChangePointToBase ι _ = RelativeGroupLaw.baseChangePointToBase ι _
  rw [RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong, RelativeGroupLaw.baseChangePointToBase_mul,
    hΨ, RelativeGroupLaw.baseChangePointToBase_mul, RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong,
    RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong]

end fibre2pts

section laws

variable {R : Type} [CommRing R] {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}

theorem mul_eq_mul_of_eq (L Lc : RelativeGroupLaw R g) {T : Scheme.{0}} {s s' : T ⟶ Spec (CommRingCat.of R)}
    (h : s' = s) (hs : ∀ a b : SchemeHomOver s g, L.mul s a b = Lc.mul s a b) :
    ∀ a b : SchemeHomOver s' g, L.mul s' a b = Lc.mul s' a b := by
  subst h; exact hs

theorem mul_eq_mul_of_pts (L Lc : RelativeGroupLaw R g) {V : Type} [Add V] {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ _}
    (pts : V ≃ SchemeHomOver s g)
    (hL : ∀ v w : V, pts (v + w) = L.mul _ (pts v) (pts w)) (hLc : ∀ v w : V, pts (v + w) = Lc.mul _ (pts v) (pts w)) :
    ∀ a b : SchemeHomOver s g, L.mul s a b = Lc.mul s a b := by
  intro a b
  obtain ⟨v, rfl⟩ := pts.surjective a
  obtain ⟨w, rfl⟩ := pts.surjective b
  rw [← hL, hLc]

end laws

section glue

variable {p : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
  {G G₀ : Scheme.{0}} {g : G ⟶ base p} {g₀ : G₀ ⟶ base p}

theorem comp_mul_of_pts {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ base p}
    (L : RelativeGroupLaw (baseRing p) g) (L₀ : RelativeGroupLaw (baseRing p) g₀) (Ψ : SchemeHomOver g g₀)
    {V V₀ : Type} [AddCommGroup V] [AddCommGroup V₀] (pts : V ≃ SchemeHomOver s g) (pts₀ : V₀ ≃ SchemeHomOver s g₀)
    (e : V →+ V₀) (he : ∀ v, (pts₀ (e v)).1 = (pts v).1 ≫ Ψ.1)
    (hadd : ∀ v w, pts (v + w) = L.mul _ (pts v) (pts w)) (hadd₀ : ∀ v w, pts₀ (v + w) = L₀.mul _ (pts₀ v) (pts₀ w)) :
    ∀ x y : SchemeHomOver s g, NeronModelInfra.schemeHomOverComp (L.mul _ x y) Ψ =
      L₀.mul _ (NeronModelInfra.schemeHomOverComp x Ψ) (NeronModelInfra.schemeHomOverComp y Ψ) := by
  have he' : ∀ v, NeronModelInfra.schemeHomOverComp (pts v) Ψ = pts₀ (e v) := fun v ↦ Subtype.ext (he v).symm
  intro x y
  obtain ⟨v, rfl⟩ := pts.surjective x
  obtain ⟨w, rfl⟩ := pts.surjective y
  rw [← hadd, he', he', he', map_add, hadd₀]

theorem comp_mul_of_eq (L : RelativeGroupLaw (baseRing p) g) (L₀ : RelativeGroupLaw (baseRing p) g₀) (Ψ : SchemeHomOver g g₀)
    {T : Scheme.{0}} {s s' : T ⟶ base p} (h : s' = s)
    (hs : ∀ x y : SchemeHomOver s g, NeronModelInfra.schemeHomOverComp (L.mul _ x y) Ψ =
      L₀.mul _ (NeronModelInfra.schemeHomOverComp x Ψ) (NeronModelInfra.schemeHomOverComp y Ψ)) :
    ∀ x y : SchemeHomOver s' g, NeronModelInfra.schemeHomOverComp (L.mul _ x y) Ψ =
      L₀.mul _ (NeronModelInfra.schemeHomOverComp x Ψ) (NeronModelInfra.schemeHomOverComp y Ψ) := by
  subst h; exact hs

theorem inv_comp_mul (L : RelativeGroupLaw (baseRing p) g) (L₀ : RelativeGroupLaw (baseRing p) g₀)
    (Ψ : SchemeHomOver g g₀) (Ψ' : SchemeHomOver g₀ g) (hΨΨ' : Ψ.1 ≫ Ψ'.1 = 𝟙 G) (hΨ'Ψ : Ψ'.1 ≫ Ψ.1 = 𝟙 G₀)
    {T : Scheme.{0}} (s : T ⟶ base p)
    (h : ∀ x y : SchemeHomOver s g, NeronModelInfra.schemeHomOverComp (L.mul s x y) Ψ =
      L₀.mul s (NeronModelInfra.schemeHomOverComp x Ψ) (NeronModelInfra.schemeHomOverComp y Ψ)) :
    ∀ x y : SchemeHomOver s g₀, NeronModelInfra.schemeHomOverComp (L₀.mul s x y) Ψ' =
      L.mul s (NeronModelInfra.schemeHomOverComp x Ψ') (NeronModelInfra.schemeHomOverComp y Ψ') := by
  have hback : ∀ z : SchemeHomOver s g₀, NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp z Ψ') Ψ = z :=
    fun z ↦ Subtype.ext (by simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, hΨ'Ψ, Category.comp_id])
  have hback' : ∀ z : SchemeHomOver s g, NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp z Ψ) Ψ' = z :=
    fun z ↦ Subtype.ext (by simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, hΨΨ', Category.comp_id])
  have hinj : Function.Injective fun z : SchemeHomOver s g ↦ NeronModelInfra.schemeHomOverComp z Ψ := by
    intro a b hab
    have := congrArg (fun z ↦ NeronModelInfra.schemeHomOverComp z Ψ') hab
    simpa only [hback'] using this
  intro x y
  apply hinj
  change NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (L₀.mul s x y) Ψ') Ψ =
    NeronModelInfra.schemeHomOverComp (L.mul s _ _) Ψ
  rw [hback, h, hback, hback]

theorem comp_mul_torusPt_of_torsion₂ (σ σ₀ : Spec (CommRingCat.of ↥A) ⟶ base p) (hσ : σ = σ₀)
    [IsSeparated g] [IsSeparated g₀]
    (L Lc : RelativeGroupLaw (baseRing p) g) (L₀ Lc₀ : RelativeGroupLaw (baseRing p) g₀) (Ψ : SchemeHomOver g g₀)
    (hΨc : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s g),
      NeronModelInfra.schemeHomOverComp (Lc.mul s x y) Ψ =
        Lc₀.mul s (NeronModelInfra.schemeHomOverComp x Ψ) (NeronModelInfra.schemeHomOverComp y Ψ))
    (hL : ∀ a b : SchemeHomOver (barPt A ≫ σ) g, L.mul _ a b = Lc.mul _ a b)
    (hL₀ : ∀ a b : SchemeHomOver (barPt A ≫ σ₀) g₀, L₀.mul _ a b = Lc₀.mul _ a b)
    {t : ℕ} (τ : SchemeHomOver (torusStr (ResidueField ↥A) t) (RelativeGroupLaw.baseChangeStr (resPt A ≫ σ) g))
    (ιm : ∀ m : ℕ, 0 < m → SchemeHomOver (muStr ↥A t m) (RelativeGroupLaw.baseChangeStr σ g))
    (hιm_sp : ∀ (m : ℕ) (hm : 0 < m), muBaseChange (residue ↥A) t m ≫ (ιm m hm).1 ≫ pullback.fst g σ =
      muToTorus (ResidueField ↥A) t m ≫ τ.1 ≫ pullback.fst g (resPt A ≫ σ))
    (χ χ' : torusCoord (ResidueField ↥A) t →ₐ[ResidueField ↥A] ResidueField ↥A)
    (hχ : ∃ n : ℕ, (n : ResidueField ↥A) ≠ 0 ∧ ∀ v : Fin t → ℤ, χ (AddMonoidAlgebra.single v 1) ^ n = 1)
    (hχ' : ∃ n : ℕ, (n : ResidueField ↥A) ≠ 0 ∧ ∀ v : Fin t → ℤ, χ' (AddMonoidAlgebra.single v 1) ^ n = 1) :
    NeronModelInfra.schemeHomOverComp ((L.baseChange (resPt A ≫ σ)).mul (𝟙 _)
        (NeronModelInfra.schemeHomOverComp (torusPt _ t χ) τ) (NeronModelInfra.schemeHomOverComp (torusPt _ t χ') τ))
        (fibreRestrict₂ (show resPt A ≫ σ = resPt A ≫ σ₀ by rw [hσ]) Ψ) =
      (L₀.baseChange (resPt A ≫ σ₀)).mul (𝟙 _)
        (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (torusPt _ t χ) τ)
          (fibreRestrict₂ (show resPt A ≫ σ = resPt A ≫ σ₀ by rw [hσ]) Ψ))
        (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (torusPt _ t χ') τ)
          (fibreRestrict₂ (show resPt A ≫ σ = resPt A ≫ σ₀ by rw [hσ]) Ψ)) := by
  subst hσ
  exact ModularCurve.JZeroNeronObjectAtP.schemeHomOverComp_mul_torusPt_fibreRestrictAlong_of_torsion σ L Lc L₀ Lc₀ Ψ hΨc hL hL₀ τ ιm hιm_sp χ χ' hχ hχ'

theorem exists_specMap_mapDomain_comp_torusFibre_eq {ι ι₀ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ base p} (hι : ι = ι₀)
    [IsAlgClosed (ResidueField ↥A)]
    {X₀ : Scheme.{0}} {f₀ : X₀ ⟶ base p}
    (L : RelativeGroupLaw (baseRing p) g) (L₀ : RelativeGroupLaw (baseRing p) g₀) (Lf₀ : RelativeGroupLaw (baseRing p) f₀)
    (hAκ₀ : AbelianSchemePropertyBundle (ResidueField ↥A) (RelativeGroupLaw.baseChangeStr ι₀ f₀))
    {t t₀ : ℕ}
    (τ : SchemeHomOver (torusStr (ResidueField ↥A) t) (RelativeGroupLaw.baseChangeStr ι g))
    (hτmul : ∀ χ χ' : WithConv (torusCoord (ResidueField ↥A) t →ₐ[ResidueField ↥A] ResidueField ↥A),
      NeronModelInfra.schemeHomOverComp (torusPt _ _ (χ * χ').ofConv) τ =
        (L.baseChange ι).mul _ (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) τ)
          (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ'.ofConv) τ))
    (τ₀ : SchemeHomOver (torusStr (ResidueField ↥A) t₀) (RelativeGroupLaw.baseChangeStr ι₀ g₀)) (hτ₀ : IsClosedImmersion τ₀.1)
    (hτ₀mul : ∀ χ χ' : WithConv (torusCoord (ResidueField ↥A) t₀ →ₐ[ResidueField ↥A] ResidueField ↥A),
      NeronModelInfra.schemeHomOverComp (torusPt _ _ (χ * χ').ofConv) τ₀ =
        (L₀.baseChange ι₀).mul _ (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) τ₀)
          (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ'.ofConv) τ₀))
    (abq₀ : Fin 2 → SchemeHomOver (RelativeGroupLaw.baseChangeStr ι₀ g₀) (RelativeGroupLaw.baseChangeStr ι₀ f₀))
    (abq₀_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ResidueField ↥A)))
      (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr ι₀ g₀)),
      NeronModelInfra.schemeHomOverComp ((L₀.baseChange ι₀).mul s x y) (abq₀ i) =
        (Lf₀.baseChange ι₀).mul s (NeronModelInfra.schemeHomOverComp x (abq₀ i))
          (NeronModelInfra.schemeHomOverComp y (abq₀ i)))
    (abq₀_eq_one_iff : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ResidueField ↥A)))
      (x : SchemeHomOver s (RelativeGroupLaw.baseChangeStr ι₀ g₀)),
      (∀ i, NeronModelInfra.schemeHomOverComp x (abq₀ i) = (Lf₀.baseChange ι₀).one s) ↔
        ∃ y : SchemeHomOver s (torusStr (ResidueField ↥A) t₀), NeronModelInfra.schemeHomOverComp y τ₀ = x)
    (Ψ : SchemeHomOver g g₀)
    (hΨκ : ∀ χ χ' : torusCoord (ResidueField ↥A) t →ₐ[ResidueField ↥A] ResidueField ↥A,
      (∃ n : ℕ, (n : ResidueField ↥A) ≠ 0 ∧ ∀ v : Fin t → ℤ, χ (AddMonoidAlgebra.single v 1) ^ n = 1) →
      (∃ n : ℕ, (n : ResidueField ↥A) ≠ 0 ∧ ∀ v : Fin t → ℤ, χ' (AddMonoidAlgebra.single v 1) ^ n = 1) →
      NeronModelInfra.schemeHomOverComp ((L.baseChange ι).mul (𝟙 _)
          (NeronModelInfra.schemeHomOverComp (torusPt _ t χ) τ) (NeronModelInfra.schemeHomOverComp (torusPt _ t χ') τ))
          (fibreRestrict₂ hι Ψ) =
        (L₀.baseChange ι₀).mul (𝟙 _)
          (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (torusPt _ t χ) τ) (fibreRestrict₂ hι Ψ))
          (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (torusPt _ t χ') τ) (fibreRestrict₂ hι Ψ))) :
    ∃ M₀ : (Fin t₀ → ℤ) →+ (Fin t → ℤ),
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀)) ≫ τ₀.1 ≫ pullback.fst g₀ ι₀ =
        τ.1 ≫ pullback.fst g ι ≫ Ψ.1 := by
  obtain ⟨M₀, hM₀⟩ := NeronSpecialFibreInfra.exists_mapDomainRingHom_comp_eq_comp_of_comp_one_of_forall_torsion_mul ι ι₀ L L₀ Lf₀ hAκ₀ τ hτmul τ₀ hτ₀ hτ₀mul abq₀ abq₀_mul abq₀_eq_one_iff
    (fibreRestrict₂ hι Ψ) hΨκ
  refine ⟨M₀, ?_⟩
  have h := congrArg (· ≫ pullback.fst g₀ ι₀) hM₀
  simp only [Category.assoc, fibreRestrict₂_fst] at h
  exact h

end glue

end ModularCurve.NeronCompare.Tor
p2m_reactivate "P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare.Tor"
p2m_reactivate "P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare"
p2m_reactivate "P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "JHNeronObjectAtP.LevelData JHNeronObjectAtP JHNeronObjectAtP.toricPoint JHNeronObjectAtP.toricPts JZeroNeronObjectAtP.baseRing JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP JZeroNeronObjectAtP.toricPoint JZeroNeronObjectAtP.toricPts jZeroTorsion heckeModuleBar HeckeAlphaBarIntegral HeckeBetaBarIntegral modularFunctionFieldBar JZero qExpand ModularPolynomialData modularFunctionFieldFullC jqModC modularFunctionFieldC inertiaInvariants instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable nodePairsOfPlaces KroneckerCongruence infSubgroup xHFunctionFieldBar JH qExpFunctionFieldC JHNeronObjectAtP.mem_finPts_iff_and_isTorsionPoint_section_and_specialPt JZeroNeronObjectAtP.mem_finPts_iff XHDRLevel.R XHDRLevel.X XHDRLevel.toBase XHDRLevel.ΓM XHDRModelAtP arithFrobC PlaceSpecialization PlaceSpecialization.ProlongationTuple DRLevel.X DRLevel.toBase DRModelPackageLevel jZeroNeronObjectAtP_pts_pic0Congr_eq_pts_comp_pullbackHom_of_modelIso_levelData JZeroNeronObjectAtP.exists_forall_muPt_comp_eq_comp_of_torusMatrix_of_rigid JZeroNeronObjectAtP.schemeHomOverComp_mul_torusPt_fibreRestrictAlong_of_torsion JHNeronObjectAtP.eq_of_muBaseChange_residue_comp_eq JZeroNeronObjectAtP.eq_of_muBaseChange_residue_comp_eq"
namespace NeronCompare
p2m_open "ModularCurve"

namespace RepIso

universe u

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
  {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}

private theorem _root_.ModularCurve.NeronCompare.RepIso.inv_over (e : C ≅ C') (he : e.hom ≫ c' = c) : e.inv ≫ c = c' := by
  rw [← he, Iso.inv_hom_id_assoc]

p2m_export "ModularCurve.NeronCompare.RepIso" "inv_over"
theorem inv_section (e : C ≅ C') (hε : ε.1 ≫ e.hom = ε'.1) : ε'.1 ≫ e.inv = ε.1 := by
  rw [← hε, Category.assoc, Iso.hom_inv_id, Category.comp_id]

noncomputable def isoOfIso (e : C ≅ C') (he : e.hom ≫ c' = c) (hε : ε.1 ≫ e.hom = ε'.1)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D') :
    D.P ≅ D'.P where
  hom := (RepresentsRelSubPic.pullbackHom e.inv (inv_over e he) (inv_section e hε) h h').1
  inv := (RepresentsRelSubPic.pullbackHom e.hom he hε h' h).1
  hom_inv_id := (AlgebraicGeometry.RelPicard.RepresentsRelSubPic.pullbackHom_inv_comp_pullbackHom_hom_of_iso
    e he (inv_over e he) hε (inv_section e hε) h h').1
  inv_hom_id := (AlgebraicGeometry.RelPicard.RepresentsRelSubPic.pullbackHom_inv_comp_pullbackHom_hom_of_iso
    e he (inv_over e he) hε (inv_section e hε) h h').2

theorem isoOfIso_hom_over (e : C ≅ C') (he : e.hom ≫ c' = c) (hε : ε.1 ≫ e.hom = ε'.1)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D') :
    (isoOfIso e he hε h h').hom ≫ D'.toBase = D.toBase :=
  (RepresentsRelSubPic.pullbackHom e.inv (inv_over e he) (inv_section e hε) h h').2

theorem isoOfIso_inv_over (e : C ≅ C') (he : e.hom ≫ c' = c) (hε : ε.1 ≫ e.hom = ε'.1)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D') :
    (isoOfIso e he hε h h').inv ≫ D.toBase = D'.toBase :=
  (RepresentsRelSubPic.pullbackHom e.hom he hε h' h).2

theorem isoOfIso_hom_eq (e : C ≅ C') (he : e.hom ≫ c' = c) (hε : ε.1 ≫ e.hom = ε'.1)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D') :
    (isoOfIso e he hε h h').hom = (RepresentsRelSubPic.pullbackHom e.inv (inv_over e he) (inv_section e hε) h h').1 := rfl

section PullbackHomMul

open scoped CategoryTheory.MonObj

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
  {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}

theorem nonempty_tensor_pullbackCurve_iso (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (L M : RigidifiedLineBundle c ε t) :
    Nonempty (((L.tensor M).pullbackCurve f hf hε).L ≅ ((L.pullbackCurve f hf hε).tensor (M.pullbackCurve f hf hε)).L) :=
  ⟨Scheme.Modules.pullbackTensorObjIso _ _ _⟩

theorem nonempty_pullbackAlong_mul_iso (P : SubPicGroupCondition c ε) (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : SchemeHomOver t D.toBase) :
    Nonempty ((h.poincare.pullbackAlong (h.relativeGroupLaw.mul t a b)).L ≅
      ((h.poincare.pullbackAlong a).tensor (h.poincare.pullbackAlong b)).L) := by
  letI := h.grpObj
  letI := P.commGroupObj (Opposite.op (Over.mk t))
  have key := congrArg Subtype.val (h.homEquiv_mul (Over.mk t) (schemeHomOverToOverHom a) (schemeHomOverToOverHom b))

  have hl : (h.representableBy.homEquiv (schemeHomOverToOverHom a * schemeHomOverToOverHom b)).1 =
      Quotient.mk _ (h.poincare.pullbackAlong (h.relativeGroupLaw.mul t a b)) := rfl
  have hr : ((h.representableBy.homEquiv (schemeHomOverToOverHom a)) *
      (h.representableBy.homEquiv (schemeHomOverToOverHom b))).1 =
      Quotient.mk _ ((h.poincare.pullbackAlong a).tensor (h.poincare.pullbackAlong b)) := rfl
  rw [hl, hr] at key
  exact Quotient.exact key

theorem nonempty_pullbackAlong_postComp_pullbackHom_iso (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t D.toBase) :
    Nonempty ((h'.poincare.pullbackAlong (postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') x)).L ≅
      ((h.poincare.pullbackAlong x).pullbackCurve f hf hε).L) := by
  have hPx : (algEquivZeroCut c ε).P t (h.poincare.pullbackAlong x) :=
    (algEquivZeroCut c ε).pullback_mem _ _ x _ h.poincare_mem
  have hx : x = h.classify t (h.poincare.pullbackAlong x) hPx := h.classify_unique t _ hPx x ⟨Iso.refl _⟩
  have hx' : postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') x =
      h'.classify t ((h.poincare.pullbackAlong x).pullbackCurve f hf hε)
        (FibrewiseAlgEquivZero.pullbackCurve f hf hε hPx) := by
    conv_lhs => rw [hx]
    exact RepresentsRelSubPic.postComp_pullbackHom_classify f hf hε h h' t _ hPx
  rw [hx']
  exact h'.classify_spec t _ _

theorem postComp_pullbackHom_mul (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : SchemeHomOver t D.toBase) :
    postComp (RepresentsRelSubPic.pullbackHom f hf hε h h')
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t a b) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c' ε') h').mul t
        (postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') a)
        (postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') b) := by
  refine h'.ext_of_iso t _ _ ?_
  obtain ⟨i1⟩ := nonempty_pullbackAlong_postComp_pullbackHom_iso f hf hε h h' t
    ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t a b)
  obtain ⟨i2⟩ := nonempty_pullbackAlong_mul_iso (algEquivZeroGroupCut c ε) h t a b
  obtain ⟨i3⟩ := nonempty_tensor_pullbackCurve_iso f hf hε (h.poincare.pullbackAlong a) (h.poincare.pullbackAlong b)
  obtain ⟨ia⟩ := nonempty_pullbackAlong_postComp_pullbackHom_iso f hf hε h h' t a
  obtain ⟨ib⟩ := nonempty_pullbackAlong_postComp_pullbackHom_iso f hf hε h h' t b
  obtain ⟨i4⟩ := nonempty_pullbackAlong_mul_iso (algEquivZeroGroupCut c' ε') h' t
    (postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') a) (postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') b)
  exact ⟨i1 ≪≫ (Scheme.Modules.pullback _).mapIso i2 ≪≫ i3 ≪≫ (ia.symm ⊗ᵢ ib.symm) ≪≫ i4.symm⟩

end PullbackHomMul
p2m_reactivate "P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare.Tor"

end RepIso
p2m_reactivate "P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare.Tor"

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀} [NeZero (N₀ * p)] {hpM : p ∣ N₀ * p}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p (N₀ * p) ⊤ hpM A} {Λ₀ : JZeroNeronObjectAtP.LevelData N₀ p A}

structure NeronObjectIso (O : JHNeronObjectAtP p (N₀ * p) ⊤ hpM A hA Λ) (O₀ : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ₀)
    (e : JH (N₀ * p) ⊤ ≃+ JZero (N₀ * p)) where

  iso : O.G ≅ O₀.G

  hom_over : iso.hom ≫ O₀.g = O.g
  inv_over : iso.inv ≫ O.g = O₀.g

  Lc : RelativeGroupLaw (baseRing p) O.g
  Lc₀ : RelativeGroupLaw (baseRing p) O₀.g

  hom_mul : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g),
    NeronModelInfra.schemeHomOverComp (Lc.mul s x y) (⟨iso.hom, hom_over⟩ : SchemeHomOver O.g O₀.g) =
      Lc₀.mul s (NeronModelInfra.schemeHomOverComp x ⟨iso.hom, hom_over⟩)
        (NeronModelInfra.schemeHomOverComp y ⟨iso.hom, hom_over⟩)

  pts_law : ∀ x y : JH (N₀ * p) ⊤, O.pts (x + y) = Lc.mul _ (O.pts x) (O.pts y)
  pts_law₀ : ∀ x y : JZero (N₀ * p), O₀.pts (x + y) = Lc₀.mul _ (O₀.pts x) (O₀.pts y)

  pts_comp : ∀ y : JH (N₀ * p) ⊤, (O₀.pts (e y)).1 = (O.pts y).1 ≫ iso.hom

  σA_eq : Λ.σA = Λ₀.σA

namespace NeronObjectIso

variable {O : JHNeronObjectAtP p (N₀ * p) ⊤ hpM A hA Λ} {O₀ : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ₀}
  {e : JH (N₀ * p) ⊤ ≃+ JZero (N₀ * p)}

def Ψ (I : NeronObjectIso O O₀ e) : SchemeHomOver O.g O₀.g := ⟨I.iso.hom, I.hom_over⟩

def Ψinv (I : NeronObjectIso O O₀ e) : SchemeHomOver O₀.g O.g := ⟨I.iso.inv, I.inv_over⟩

@[scoped simp] theorem Ψ_val (I : NeronObjectIso O O₀ e) : I.Ψ.1 = I.iso.hom := rfl
@[scoped simp] theorem Ψinv_val (I : NeronObjectIso O O₀ e) : I.Ψinv.1 = I.iso.inv := rfl

theorem pts_symm_comp (I : NeronObjectIso O O₀ e) (x : JZero (N₀ * p)) :
    (O.pts (e.symm x)).1 = (O₀.pts x).1 ≫ I.iso.inv := by
  have h := I.pts_comp (e.symm x)
  rw [AddEquiv.apply_symm_apply] at h
  rw [h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end NeronObjectIso
p2m_reactivate "P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare.Tor P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare.NeronObjectIso"

namespace NeronObjectIso

variable {O : JHNeronObjectAtP p (N₀ * p) ⊤ hpM A hA Λ} {O₀ : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ₀}
  {e : JH (N₀ * p) ⊤ ≃+ JZero (N₀ * p)}

theorem mem_jZeroTorsion_iff (m : ℕ) (y : JH (N₀ * p) ⊤) :
    e y ∈ jZeroTorsion (N₀ * p) m ↔ y ∈ Pic0.torsion (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (N₀ * p) ⊤) m := by
  rw [Pic0.mem_torsion]
  show (m : ℤ) • e y = 0 ↔ (m : ℤ) • y = 0
  rw [← map_zsmul, AddEquiv.map_eq_zero_iff]

theorem extendsToPlace_iff (I : NeronObjectIso O O₀ e) (y : JH (N₀ * p) ⊤) :
    ExtendsToPlace A Λ₀.σA (O₀.pts (e y)) ↔ ExtendsToPlace A Λ.σA (O.pts y) := by
  rw [← I.σA_eq]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨NeronModelInfra.schemeHomOverComp s I.Ψinv, ?_⟩
    show (O.pts y).1 = barPt A ≫ (s.1 ≫ I.iso.inv)
    rw [← Category.assoc, ← hs, I.pts_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rintro ⟨s, hs⟩
    refine ⟨NeronModelInfra.schemeHomOverComp s I.Ψ, ?_⟩
    show (O₀.pts (e y)).1 = barPt A ≫ (s.1 ≫ I.iso.hom)
    rw [I.pts_comp, hs, Category.assoc]

end NeronObjectIso
p2m_reactivate "P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare.Tor P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare.NeronObjectIso"

theorem map_finPts_eq_of_neronObjectIso
    (O : JHNeronObjectAtP p (N₀ * p) ⊤ hpM A hA Λ) (O₀ : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ₀)
    (e : JH (N₀ * p) ⊤ ≃+ JZero (N₀ * p)) (I : NeronObjectIso O O₀ e) (m : ℕ) :
    (O.finPts m).map e.toAddMonoidHom = O₀.finPts m := by
  have hJH := (ModularCurve.JHNeronObjectAtP.mem_finPts_iff_and_isTorsionPoint_section_and_specialPt
    p (N₀ * p) ⊤ hpM A hA Λ O m).1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, hJH] at hy
    rw [AddEquiv.coe_toAddMonoidHom, ModularCurve.JZeroNeronObjectAtP.mem_finPts_iff]
    exact ⟨(NeronObjectIso.mem_jZeroTorsion_iff m y).mpr hy.1, (I.extendsToPlace_iff y).mpr hy.2⟩
  · intro hx
    rw [ModularCurve.JZeroNeronObjectAtP.mem_finPts_iff] at hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    rw [SetLike.mem_coe, hJH]
    have h1 := (NeronObjectIso.mem_jZeroTorsion_iff (e := e) m (e.symm x))
    have h2 := I.extendsToPlace_iff (e.symm x)
    rw [AddEquiv.apply_symm_apply] at h1 h2
    exact ⟨h1.mp hx.1, h2.mp hx.2⟩

namespace NeronObjectIso

open ModularCurve.NeronCompare.Tor

variable {O : JHNeronObjectAtP p (N₀ * p) ⊤ hpM A hA Λ} {O₀ : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ₀}
  {e : JH (N₀ * p) ⊤ ≃+ JZero (N₀ * p)}

theorem hom_inv (I : NeronObjectIso O O₀ e) : I.Ψ.1 ≫ I.Ψinv.1 = 𝟙 _ := I.iso.hom_inv_id
theorem inv_hom (I : NeronObjectIso O O₀ e) : I.Ψinv.1 ≫ I.Ψ.1 = 𝟙 _ := I.iso.inv_hom_id

theorem comp_mul_gen (I : NeronObjectIso O O₀ e) : ∀ x y : SchemeHomOver (genPt p) O.g,
    NeronModelInfra.schemeHomOverComp (O.L.mul _ x y) I.Ψ =
      O₀.L.mul _ (NeronModelInfra.schemeHomOverComp x I.Ψ) (NeronModelInfra.schemeHomOverComp y I.Ψ) :=
  comp_mul_of_pts O.L O₀.L I.Ψ O.pts O₀.pts e.toAddMonoidHom (fun v ↦ I.pts_comp v) O.pts_add O₀.pts_add

theorem inv_comp_mul_gen (I : NeronObjectIso O O₀ e) : ∀ x y : SchemeHomOver (genPt p) O₀.g,
    NeronModelInfra.schemeHomOverComp (O₀.L.mul _ x y) I.Ψinv =
      O.L.mul _ (NeronModelInfra.schemeHomOverComp x I.Ψinv) (NeronModelInfra.schemeHomOverComp y I.Ψinv) :=
  comp_mul_of_pts O₀.L O.L I.Ψinv O₀.pts O.pts e.symm.toAddMonoidHom (fun v ↦ I.pts_symm_comp v) O₀.pts_add O.pts_add

theorem law_agree (I : NeronObjectIso O O₀ e) : ∀ a b : SchemeHomOver (barPt A ≫ Λ.σA) O.g, O.L.mul _ a b = I.Lc.mul _ a b :=
  mul_eq_mul_of_eq O.L I.Lc Λ.hσA (mul_eq_mul_of_pts O.L I.Lc O.pts O.pts_add I.pts_law)

theorem law_agree₀ (I : NeronObjectIso O O₀ e) : ∀ a b : SchemeHomOver (barPt A ≫ Λ₀.σA) O₀.g, O₀.L.mul _ a b = I.Lc₀.mul _ a b :=
  mul_eq_mul_of_eq O₀.L I.Lc₀ Λ₀.hσA (mul_eq_mul_of_pts O₀.L I.Lc₀ O₀.pts O₀.pts_add I.pts_law₀)

theorem hom_mul' (I : NeronObjectIso O O₀ e) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g) :
    NeronModelInfra.schemeHomOverComp (I.Lc.mul s x y) I.Ψ =
      I.Lc₀.mul s (NeronModelInfra.schemeHomOverComp x I.Ψ) (NeronModelInfra.schemeHomOverComp y I.Ψ) := I.hom_mul s x y

theorem inv_hom_mul' (I : NeronObjectIso O O₀ e) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O₀.g) :
    NeronModelInfra.schemeHomOverComp (I.Lc₀.mul s x y) I.Ψinv =
      I.Lc.mul s (NeronModelInfra.schemeHomOverComp x I.Ψinv) (NeronModelInfra.schemeHomOverComp y I.Ψinv) :=
  inv_comp_mul I.Lc I.Lc₀ I.Ψ I.Ψinv I.hom_inv I.inv_hom s (I.hom_mul s) x y

theorem exists_mapDomain_torusFibre₀_eq (I : NeronObjectIso O O₀ e) (hΛ₀ : Λ₀.IsJacobian) :
    ∃ M₀ : (Fin O₀.toricRank → ℤ) →+ (Fin O.toricRank → ℤ),
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀)) ≫ O₀.torusFibre.1 ≫
          pullback.fst O₀.g (resPt A ≫ Λ₀.σA) =
        O.torusFibre.1 ≫ pullback.fst O.g (resPt A ≫ Λ.σA) ≫ I.Ψ.1 := by
  haveI : IsSeparated O.g := O.separated
  haveI : IsSeparated O₀.g := O₀.separated
  have hι : resPt A ≫ Λ.σA = resPt A ≫ Λ₀.σA := by rw [I.σA_eq]
  exact exists_specMap_mapDomain_comp_torusFibre_eq hι O.L O₀.L Λ₀.L
    (GoodReductionJacobian.AbelianSchemePropertyBundle.baseChange_of_field hΛ₀.1 _)
    O.torusFibre O.torusFibre_mul O₀.torusFibre O₀.torusFibre_isClosedImmersion O₀.torusFibre_mul
    O₀.abqFibre O₀.abqFibre_mul O₀.abqFibre_eq_one_iff I.Ψ
    (fun χ χ' hχ hχ' ↦ comp_mul_torusPt_of_torsion₂ Λ.σA Λ₀.σA I.σA_eq O.L I.Lc O₀.L I.Lc₀ I.Ψ I.hom_mul'
      I.law_agree I.law_agree₀ O.torusFibre O.toricLift O.toricLift_special χ χ' hχ hχ')

theorem exists_mapDomain_torusFibre_eq (I : NeronObjectIso O O₀ e)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f) :
    ∃ M₀' : (Fin O.toricRank → ℤ) →+ (Fin O₀.toricRank → ℤ),
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀')) ≫ O.torusFibre.1 ≫
          pullback.fst O.g (resPt A ≫ Λ.σA) =
        O₀.torusFibre.1 ≫ pullback.fst O₀.g (resPt A ≫ Λ₀.σA) ≫ I.Ψinv.1 := by
  haveI : IsSeparated O.g := O.separated
  haveI : IsSeparated O₀.g := O₀.separated
  have hι : resPt A ≫ Λ₀.σA = resPt A ≫ Λ.σA := by rw [I.σA_eq]
  exact exists_specMap_mapDomain_comp_torusFibre_eq hι O₀.L O.L Λ.L
    (GoodReductionJacobian.AbelianSchemePropertyBundle.baseChange_of_field hΛ _)
    O₀.torusFibre O₀.torusFibre_mul O.torusFibre O.torusFibre_isClosedImmersion O.torusFibre_mul
    O.abqFibre O.abqFibre_mul O.abqFibre_eq_one_iff I.Ψinv
    (fun χ χ' hχ hχ' ↦ comp_mul_torusPt_of_torsion₂ Λ₀.σA Λ.σA I.σA_eq.symm O₀.L I.Lc₀ O.L I.Lc I.Ψinv I.inv_hom_mul'
      I.law_agree₀ I.law_agree O₀.torusFibre O₀.toricLift O₀.toricLift_special χ χ' hχ hχ')

theorem exists_toricLift_comp_eq (I : NeronObjectIso O O₀ e)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f) (hΛ₀ : Λ₀.IsJacobian) (m : ℕ) (hm : 0 < m) :
    ∃ Mbar : (Fin O₀.toricRank → ZMod m) →+ (Fin O.toricRank → ZMod m),
      ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
        (muPt A O.toricRank m χ).1 ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA ≫ I.Ψ.1 =
          (muPt A O₀.toricRank m (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar))).1 ≫ (O₀.toricLift m hm).1 ≫
            pullback.fst O₀.g Λ₀.σA := by
  obtain ⟨M₀, hM₀⟩ := I.exists_mapDomain_torusFibre₀_eq hΛ₀
  obtain ⟨M₀', hM₀'⟩ := I.exists_mapDomain_torusFibre_eq hΛ
  obtain ⟨Mbar, -, h⟩ := ModularCurve.JZeroNeronObjectAtP.exists_forall_muPt_comp_eq_comp_of_torusMatrix_of_rigid Λ.σA Λ₀.σA I.σA_eq O.L O₀.L I.Ψ I.Ψinv I.hom_inv I.inv_hom
    (comp_mul_of_eq O₀.L O.L I.Ψinv Λ₀.hσA I.inv_comp_mul_gen)
    m hm (O.toricLift m hm) (O₀.toricLift m hm) (O.toricLift_mul m hm) (O₀.toricLift_mul m hm)
    O.torusFibre O₀.torusFibre (O.toricLift_special m hm) (O₀.toricLift_special m hm) M₀ hM₀ M₀' hM₀'
    (ModularCurve.JHNeronObjectAtP.eq_of_muBaseChange_residue_comp_eq p (N₀ * p) ⊤ hpM A hA Λ O m hm)
  exact ⟨Mbar, h⟩

theorem exists_toricLift₀_comp_eq (I : NeronObjectIso O O₀ e)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f) (hΛ₀ : Λ₀.IsJacobian) (m : ℕ) (hm : 0 < m) :
    ∃ Mbar' : (Fin O.toricRank → ZMod m) →+ (Fin O₀.toricRank → ZMod m),
      ∀ χ : muCoord ↥A O₀.toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
        (muPt A O₀.toricRank m χ).1 ≫ (O₀.toricLift m hm).1 ≫ pullback.fst O₀.g Λ₀.σA ≫ I.Ψinv.1 =
          (muPt A O.toricRank m (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar'))).1 ≫ (O.toricLift m hm).1 ≫
            pullback.fst O.g Λ.σA := by
  obtain ⟨M₀, hM₀⟩ := I.exists_mapDomain_torusFibre₀_eq hΛ₀
  obtain ⟨M₀', hM₀'⟩ := I.exists_mapDomain_torusFibre_eq hΛ
  obtain ⟨Mbar, -, h⟩ := ModularCurve.JZeroNeronObjectAtP.exists_forall_muPt_comp_eq_comp_of_torusMatrix_of_rigid Λ₀.σA Λ.σA I.σA_eq.symm O₀.L O.L I.Ψinv I.Ψ I.inv_hom I.hom_inv
    (comp_mul_of_eq O.L O₀.L I.Ψ Λ.hσA I.comp_mul_gen)
    m hm (O₀.toricLift m hm) (O.toricLift m hm) (O₀.toricLift_mul m hm) (O.toricLift_mul m hm)
    O₀.torusFibre O.torusFibre (O₀.toricLift_special m hm) (O.toricLift_special m hm) M₀' hM₀' M₀ hM₀
    (ModularCurve.JZeroNeronObjectAtP.eq_of_muBaseChange_residue_comp_eq N₀ p hpN₀ A hA Λ₀ hΛ₀ O₀ m hm)
  exact ⟨Mbar, h⟩

theorem apply_toricPoint (I : NeronObjectIso O O₀ e)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f) (hΛ₀ : Λ₀.IsJacobian) (m : ℕ) (hm : 0 < m) :
    ∃ Mbar : (Fin O₀.toricRank → ZMod m) →+ (Fin O.toricRank → ZMod m),
      ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
        e (O.toricPoint m hm χ) = O₀.toricPoint m hm (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar)) := by
  obtain ⟨Mbar, h⟩ := I.exists_toricLift_comp_eq hΛ hΛ₀ m hm
  refine ⟨Mbar, fun χ ↦ ?_⟩
  apply O₀.pts.injective
  apply Subtype.ext
  rw [I.pts_comp]
  have hχ := h χ
  simp only [JHNeronObjectAtP.toricPoint, JZeroNeronObjectAtP.toricPoint, Equiv.apply_symm_apply, genOfBaseChangePt, castOver,
    RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc, Ψ_val] at hχ ⊢
  exact hχ

theorem symm_apply_toricPoint (I : NeronObjectIso O O₀ e)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f) (hΛ₀ : Λ₀.IsJacobian) (m : ℕ) (hm : 0 < m) :
    ∃ Mbar' : (Fin O.toricRank → ZMod m) →+ (Fin O₀.toricRank → ZMod m),
      ∀ χ : muCoord ↥A O₀.toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
        e.symm (O₀.toricPoint m hm χ) = O.toricPoint m hm (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar')) := by
  obtain ⟨Mbar, h⟩ := I.exists_toricLift₀_comp_eq hΛ hΛ₀ m hm
  refine ⟨Mbar, fun χ ↦ ?_⟩
  apply O.pts.injective
  apply Subtype.ext
  rw [I.pts_symm_comp]
  have hχ := h χ
  simp only [JHNeronObjectAtP.toricPoint, JZeroNeronObjectAtP.toricPoint, Equiv.apply_symm_apply, genOfBaseChangePt, castOver,
    RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc, Ψinv_val] at hχ ⊢
  exact hχ

end NeronObjectIso
p2m_reactivate "P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare.Tor P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare.NeronObjectIso"

theorem map_toricPts_eq_of_neronObjectIso
    (O : JHNeronObjectAtP p (N₀ * p) ⊤ hpM A hA Λ) (O₀ : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ₀)
    (e : JH (N₀ * p) ⊤ ≃+ JZero (N₀ * p)) (I : NeronObjectIso O O₀ e)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f) (hΛ₀ : Λ₀.IsJacobian) (m : ℕ) (hm : 0 < m) :
    (O.toricPts m).map e.toAddMonoidHom = O₀.toricPts m := by
  obtain ⟨Mbar, h₁⟩ := I.apply_toricPoint hΛ hΛ₀ m hm
  obtain ⟨Mbar', h₂⟩ := I.symm_apply_toricPoint hΛ hΛ₀ m hm
  apply le_antisymm
  · rw [AddSubgroup.map_le_iff_le_comap, JHNeronObjectAtP.toricPts, dif_pos hm, AddSubgroup.closure_le]
    rintro _ ⟨χ, rfl⟩
    rw [AddSubgroup.coe_comap, Set.mem_preimage, AddEquiv.coe_toAddMonoidHom, h₁, JZeroNeronObjectAtP.toricPts, dif_pos hm]
    exact AddSubgroup.subset_closure ⟨_, rfl⟩
  · rw [JZeroNeronObjectAtP.toricPts, dif_pos hm, AddSubgroup.closure_le]
    rintro _ ⟨χ, rfl⟩
    refine ⟨e.symm (O₀.toricPoint m hm χ), ?_, e.apply_symm_apply _⟩
    rw [h₂, SetLike.mem_coe, JHNeronObjectAtP.toricPts, dif_pos hm]
    exact AddSubgroup.subset_closure ⟨_, rfl⟩

end ModularCurve.NeronCompare
p2m_reactivate "P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare.Tor P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare.NeronObjectIso"
p2m_reactivate "P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare.Tor P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare.NeronObjectIso"

end
p2m_reactivate "P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare.Tor P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare.NeronObjectIso"

section Assembly

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.DRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice"

open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) [NeZero (N₀ * p)]
    (hpM : p ∣ N₀ * p) (hpM2 : ¬ p ^ 2 ∣ N₀ * p) [NeZero (N₀ * p / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) [IsAlgClosed (ResidueField ↥A)] :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := heckeModuleBar (N₀ * p)
    letI := heckeModuleBar N₀
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N₀
    letI : Algebra (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀) :=
      (modularFunctionFieldFullC (ResidueField ↥A) N₀).algebra

    ∀ (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p (N₀ * p) ⊤ hpM hj)
    (θ : ↥(xHFunctionFieldBar (N₀ * p) ⊤) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar (N₀ * p) ⊤))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar (N₀ * p) ⊤)) (u : ↥(xHFunctionFieldBar ((N₀ * p) / p) (infSubgroup p (N₀ * p) ⊤ hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar (N₀ * p) ⊤)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (Λ : JHNeronObjectAtP.LevelData p (N₀ * p) ⊤ hpM A) (O : JHNeronObjectAtP p (N₀ * p) ⊤ hpM A hA Λ)
    (hD : RepresentsRelSubPic (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) 𝔛.εinf (algEquivZeroCut (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj)))

    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (hσ : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

      (hDQT : RepresentsRelSubPic (baseChange (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
          (algEquivZeroCut (baseChange (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj))).baseChange ℚ))
      (_ : IsSeparated (baseChange (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) ℚ))
      (ajQT : SchemeHomOver (baseChange (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj))).baseChange ℚ).toBase)
      (kQT : pullback (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (genPt p) ⟶ pullback (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (specMap (R p) ℚ))
      (ajbarT : 𝔛.Meta.C ⟶ O.G)
      (εbarT : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (HAJ :

      Nonempty (hDQT.poincare.L ≅ (BaseChange.ofR (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L) ∧

      (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQT.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj))).baseChange ℚ).zeroSection ∧

      (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
          (x : SchemeHomOver t (baseChange (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) ℚ)),
        Nonempty ((hDQT.poincare.pullbackAlong
            ⟨x.1 ≫ ajQT.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQT.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) ℚ) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange (R p) (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
                (Category.comp_id t)))).idealModule)) ∧

      kQT ≫ pullback.fst (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (specMap (R p) ℚ) = pullback.fst (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (genPt p) ∧
      kQT ≫ pullback.snd (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (specMap (R p) ℚ) = pullback.snd (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ) ∧

      ajbarT = 𝔛.eeta ≫ kQT ≫ ajQT.1 ≫ pullback.fst O.g (specMap (R p) ℚ) ∧
      ajbarT ≫ O.g = 𝔛.Meta.toBase ≫ genPt p ∧
      εbarT.1 ≫ 𝔛.eeta ≫ pullback.fst (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 ∧
      εbarT.1 ≫ ajbarT = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1 ∧

      (∀ x y : JH (N₀ * p) ⊤,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)) ∧

      (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (N₀ * p) ⊤)),
          (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (N₀ * p) ⊤)) =
            Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
          (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbarT)),

    ∀ (Λ₀ : JZeroNeronObjectAtP.LevelData N₀ p A) (_ : Λ₀.IsJacobian) (O₀ : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ₀)
      (𝔓 : DRModelPackageLevel N₀ p hpN₀),
      (

      (let D : RelativePic0Designation (R p) (toBase N₀ p) :=
          ⟨O₀.G, O₀.g, (O₀.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O₀.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩
        ∃ (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)
        (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
            (algEquivZeroCut (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
        (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf ℚ
            (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

        (_ : IsSeparated (baseChange (R p) (toBase N₀ p) ℚ))

        (ajQ : SchemeHomOver (baseChange (R p) (toBase N₀ p) ℚ) (D.baseChange ℚ).toBase)
        (hajQε : (sectionBaseChange ℚ 𝔓.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
        (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
            (x : SchemeHomOver t (baseChange (R p) (toBase N₀ p) ℚ)),
          Nonempty ((hDQ.poincare.pullbackAlong
              ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
            (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) x.1 x.2).lineBundle ⊗
              (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔓.εinf).1)
                ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔓.εinf).2).trans
                  (Category.comp_id t)))).idealModule))

        (kQ : pullback (toBase N₀ p) (genPt p) ⟶ pullback (toBase N₀ p) (specMap (R p) ℚ))
        (hkQ₁ : kQ ≫ pullback.fst (toBase N₀ p) (specMap (R p) ℚ) = pullback.fst (toBase N₀ p) (genPt p))
        (hkQ₂ : kQ ≫ pullback.snd (toBase N₀ p) (specMap (R p) ℚ) = pullback.snd (toBase N₀ p) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

        (ajbar : 𝔓.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔓.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
        (hajbar_over : ajbar ≫ D.toBase = 𝔓.Meta.toBase ≫ genPt p)
        (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
        (hεbar : εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1) (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection),

        (∀ x y : JZero (N₀ * p),
          O₀.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O₀.pts x) (O₀.pts y)) ∧
        (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
          s.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
          ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
            (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
              Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
            (O₀.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)) ∧

      (∃ (ρ : R p →+* ↥A) (_ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
          (_ : Λ₀.σA = Spec.map (CommRingCat.ofHom ρ))
          (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
          (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ p)
          (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ p)
          (P : PlaceSpecialization A p N₀ data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
          (Rt : PlaceSpecialization.ProlongationTuple P) (_ : Rt.IsModel) (_ : Rt.RegularityLaw O₀.ssFinset)
          (_ : Rt.NodeValueLaw O₀.ssFinset) (_ : Rt.OrderLawFixed)
          (sp : ↥(inertiaInvariants A (N₀ * p)) →+
            GluedPic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀) (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) O₀.ssFinset))
          (_ : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) O₀.ssFinset) sp)

          (hE : modularFunctionFieldC (ResidueField ↥A) N₀ = modularFunctionFieldFullC (ResidueField ↥A) N₀),

        O₀.frob = arithFrobC p (ResidueField ↥A) N₀ ∧

        (∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
            (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
            (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
            (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp ρ))
            (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
            (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
            (P0 : closedPoints (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).C),
            (𝔓.efib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).base P0.1 =
                (uκ ≫ fibreMap0 𝔓.π ((IsLocalRing.residue ↥A).comp ρ)).base (IsLocalRing.closedPoint (ResidueField ↥A)) →
              (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).placeOfPoint P0 = P.reduceFst (𝔓.Meta.pointEquivPlace y)) ∧
        (∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
            (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
            (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
            (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp ρ))
            (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
            (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
            (P1 : closedPoints (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).C),
            (𝔓.efib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).base P1.1 =
                (uκ ≫ fibreMap 𝔓.w.hom 𝔓.w_over ((IsLocalRing.residue ↥A).comp ρ) ≫ fibreMap0 𝔓.π ((IsLocalRing.residue ↥A).comp ρ)).base
                  (IsLocalRing.closedPoint (ResidueField ↥A)) →
              (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).placeOfPoint P1 = P.reduceSnd (𝔓.Meta.pointEquivPlace y)) ∧

        (∀ x : ↥(inertiaInvariants A (N₀ * p)),
          ExtendsToPlace A Λ₀.σA (O₀.pts (x : JZero (N₀ * p))) ↔ P.IsGoodClass (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) O₀.ssFinset) (x : JZero (N₀ * p))) ∧

        (∀ (x : ↥(inertiaInvariants A (N₀ * p))) (s : SchemeHomOver Λ₀.σA O₀.g),
          (O₀.pts (x : JZero (N₀ * p))).1 = barPt A ≫ s.1 →
          ((Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm (Λ₀.ptsSp.symm (fibreMap (O₀.abqFibre 0) (NeronModelInfra.schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ Λ₀.σA) Λ₀.σA) s))),
            (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm (Λ₀.ptsSp.symm (fibreMap (O₀.abqFibre 1) (NeronModelInfra.schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ Λ₀.σA) Λ₀.σA) s)))) =
            GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) O₀.ssFinset) (sp x)) ∧

        (∀ (x : ↥(inertiaInvariants A (N₀ * p))) (s : SchemeHomOver Λ₀.σA O₀.g),
          (O₀.pts (x : JZero (N₀ * p))).1 = barPt A ≫ s.1 →
          ((∃ y : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O₀.toricRank),
              NeronModelInfra.schemeHomOverComp y O₀.torusFibre = toFibrePt (NeronModelInfra.schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ Λ₀.σA) Λ₀.σA) s)) ↔
            GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) O₀.ssFinset) (sp x) = 0))) ∧

      (∀ (m : ℕ), m.Coprime p →
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ jZeroTorsion (N₀ * p) m, σ • x - x ∈ O₀.toricPts m) ∧
      (∀ (m : ℕ), 0 < m →
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ jZeroTorsion (N₀ * p) m, σ • x - x ∈ O₀.finPts m)) →

    ∀ (hF : xHFunctionFieldBar (N₀ * p) ⊤ = modularFunctionFieldBar (N₀ * p))
      (φ : XHDRLevel.X p (XHDRLevel.ΓM (N₀ * p) ⊤) hj ≅ DRLevel.X N₀ p)
      (_ : φ.hom ≫ DRLevel.toBase N₀ p = XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj)
      (_ : 𝔛.εinf.1 ≫ φ.hom = 𝔓.εinf.1)
      (_ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
          (y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
        y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ φ.hom = y₀.1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ p) (genPt p) →
        𝔓.Meta.pointEquivPlace y₀ =
          Place.congrRingEquiv (IntermediateField.equivOfEq hF).toRingEquiv (fun a => (IntermediateField.equivOfEq hF).commutes a)
            (𝔛.Meta.pointEquivPlace y)),

    ∀ (e : JH (N₀ * p) ⊤ ≃+ JZero (N₀ * p))
      (_ : ∀ x : JH (N₀ * p) ⊤,
        e x = Pic0.congr (IntermediateField.equivOfEq hF).toRingEquiv (fun a => (IntermediateField.equivOfEq hF).commutes a) x),
    ∀ m : ℕ, 0 < m →
      (O.finPts m).map e.toAddMonoidHom = O₀.finPts m ∧ (O.toricPts m).map e.toAddMonoidHom = O₀.toricPts m := by
  haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
  intro hj 𝔛 θ hθ hwgen ρ hρ Λ O hD hΛ hσ hDQT hsepT ajQT kQT ajbarT εbarT HAJ Λ₀ hJ O₀ 𝔓 H₀ hF φ hφb hφε hφpl e he m hm
  have HAJ' := HAJ

  obtain ⟨hpoincT, hajεT, hajclT, hkQ₁T, hkQ₂T, hajbarT, hajbarT_over, hεbarT, hεbarT_aj, hpts_law, hAJT⟩ := HAJ
  obtain ⟨⟨hD₀, hDQ₀, hPQ₀, hsep₀, ajQ₀, hajQε₀, hajQ₀, kQ₀, hkQ₁₀, hkQ₂₀,
      ajbar₀, hajbar₀, hajbar_over₀, εbar₀, hεbar₀, hεbar_aj₀, hpts_law₀, hAJ₀⟩, ⟨ρ₀, hρ₀, hσ₀, hbridge⟩, hiva, hivb⟩ := H₀

  have hρ₀ρ : ρ₀ = ρ := by
    refine RingHom.ext fun r => Subtype.val_injective ?_
    have h1 := congrArg (fun f : XHDRLevel.R p →+* AlgebraicClosure ℚ => f r) hρ
    have h2 := congrArg (fun f : JZeroNeronObjectAtP.baseRing p →+* AlgebraicClosure ℚ => f r) hρ₀
    exact h2.trans h1.symm
  have hσA : Λ.σA = Λ₀.σA := by
    rw [hσ, hσ₀, hρ₀ρ]

  let Ψ : O.G ≅ O₀.G := ModularCurve.NeronCompare.RepIso.isoOfIso φ hφb hφε hD hD₀
  have hover : Ψ.hom ≫ O₀.g = O.g := ModularCurve.NeronCompare.RepIso.isoOfIso_hom_over φ hφb hφε hD hD₀
  have hover' : Ψ.inv ≫ O.g = O₀.g := ModularCurve.NeronCompare.RepIso.isoOfIso_inv_over φ hφb hφε hD hD₀
  have hmul : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s x y)
          (⟨Ψ.hom, hover⟩ : SchemeHomOver O.g O₀.g) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul s
          (NeronModelInfra.schemeHomOverComp x ⟨Ψ.hom, hover⟩) (NeronModelInfra.schemeHomOverComp y ⟨Ψ.hom, hover⟩) :=
    fun s x y =>
      ModularCurve.NeronCompare.RepIso.postComp_pullbackHom_mul φ.inv (ModularCurve.NeronCompare.RepIso.inv_over φ hφb)
        (ModularCurve.NeronCompare.RepIso.inv_section φ hφε) hD hD₀ s x y
  let I : ModularCurve.NeronCompare.NeronObjectIso O O₀ e :=
    { iso := Ψ
      hom_over := hover
      inv_over := hover'
      Lc := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD
      Lc₀ := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀
      hom_mul := hmul
      pts_law := hpts_law
      pts_law₀ := hpts_law₀
      pts_comp := fun y => by
        rw [show Ψ.hom = (RepresentsRelSubPic.pullbackHom φ.inv (ModularCurve.NeronCompare.RepIso.inv_over φ hφb)
            (ModularCurve.NeronCompare.RepIso.inv_section φ hφε) hD hD₀).1 from rfl]
        exact ModularCurve.jZeroNeronObjectAtP_pts_pic0Congr_eq_pts_comp_pullbackHom_of_modelIso_levelData N₀ p hpN₀ hpM hpM2 A hA
          hj 𝔛 Λ O hD hDQT hsepT ajQT kQT ajbarT εbarT HAJ' Λ₀ 𝔓 O₀ hD₀ hDQ₀ hPQ₀ hsep₀ ajQ₀ hajQε₀ hajQ₀ kQ₀ hkQ₁₀ hkQ₂₀
          ajbar₀ hajbar₀ hajbar_over₀ εbar₀ hεbar₀ hεbar_aj₀ hpts_law₀ hAJ₀ hF φ hφb
          (ModularCurve.NeronCompare.RepIso.inv_over φ hφb) hφε (ModularCurve.NeronCompare.RepIso.inv_section φ hφε) hφpl e he y
      σA_eq := hσA }
  exact ⟨ModularCurve.NeronCompare.map_finPts_eq_of_neronObjectIso O O₀ e I m,
    ModularCurve.NeronCompare.map_toricPts_eq_of_neronObjectIso O O₀ e I hΛ hJ m hm⟩

end Assembly
p2m_reactivate "P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare.Tor P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge.ModularCurve.NeronCompare.NeronObjectIso"

end S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge
end P2MW
export P2MW.S_ModularCurve_map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge (solution)
