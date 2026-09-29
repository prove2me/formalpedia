-- Prove2me | solution 1 for ModularCurve.ord_apply_pointEquivPlace_jqModC_pos_of_stalkClosedPointTo_mem_maximalIdeal_of_ffEquiv_symm_stalkMap_eq_jq_cuspSection_of_ratCurveModel_compat_of_neZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/aad28527-f7d7-5f11-9539-bc45b779628b

import Mathlib
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_ModularCurve_HeckeProj
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_JacJ1Iface
import Definitions.Def_ModularCurve_QAdicPlace
import Theorems.Thm_ModularCurve_coe_ffEquiv_symm_stalkMap_eq_coeffEmb_ffEquiv_symm_of_galoisCompat_of_placeCompat
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo
import Theorems.Thm_AlgebraicCurve_Place_mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos
import Theorems.Thm_ModularCurve_IsPlaceReductionModL_coordinate_clauses
import Theorems.Thm_ModularCurve_isRational_place_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_apply_pointEquivPlace_jqModC_pos_of_stalkClosedPointTo_mem_maximalIdeal_of_ffEquiv_symm_stalkMap_eq_jq_cuspSection_of_ratCurveModel_compat_of_neZero
p2m_attr_erase "instance" "NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.germ_stalkClosedPointTo_Spec Scheme.Hom.stalkSpecializes_stalkMap SmoothOfRelativeDimension IsProper Scheme.Hom Scheme.stalkClosedPointTo_comp StructureSheaf.algebraMap_germ stalkClosedPointIso Spec StructureSheaf.toStalk IsIntegral Scheme.Hom.stalkMap_comp Spec.map Scheme Scheme.Hom.stalkMap Scheme.stalkClosedPointTo Scheme.ΓSpecIso_inv stalkClosedPointIso_inv Scheme.ΓSpecIso"
namespace GenericValue
p2m_open "AlgebraicGeometry"

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_ModularCurve_ord_apply_pointEquivPlace_jqModC_pos_of_stalkClosedPointTo_mem_maximalIdeal_of_ffEquiv_symm_stalkMap_eq_jq_cuspSection_of_ratCurveModel_compat_of_neZero.AlgebraicGeometry"

theorem stalkClosedPointTo_stalkSpecializes_eq_algebraMap
    {A K : Type u} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]
    {X : Scheme.{u}} (xA : Spec (.of A) ⟶ X) (φ : Spec (.of K) ⟶ X)
    (hφ : φ = Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ xA)
    (h : φ.base (IsLocalRing.closedPoint K) ⤳ xA.base (IsLocalRing.closedPoint A))
    (g : X.presheaf.stalk (xA.base (IsLocalRing.closedPoint A))) :
    (Scheme.stalkClosedPointTo φ).hom ((X.presheaf.stalkSpecializes h).hom g) =
      algebraMap A K ((Scheme.stalkClosedPointTo xA).hom g) := by
  subst hφ
  have hR : (Spec.map (CommRingCat.ofHom (algebraMap A K))).base (IsLocalRing.closedPoint K) ⤳
      IsLocalRing.closedPoint A := IsLocalRing.specializes_closedPoint _

  have htost : StructureSheaf.toStalk A (IsLocalRing.closedPoint A) =
      (Scheme.ΓSpecIso (.of A)).inv ≫ (Spec (.of A)).presheaf.germ ⊤ (IsLocalRing.closedPoint A) trivial := by
    rw [Scheme.ΓSpecIso_inv]
    exact (StructureSheaf.algebraMap_germ ⊤ _ trivial).symm
  have hw : (Scheme.Hom.stalkMap xA (IsLocalRing.closedPoint A)).hom g =
      ((Spec (.of A)).presheaf.germ ⊤ (IsLocalRing.closedPoint A) trivial).hom
        ((Scheme.ΓSpecIso (.of A)).inv.hom ((Scheme.stalkClosedPointTo xA).hom g)) := by
    have h1 : ((stalkClosedPointIso (.of A)).inv).hom ((Scheme.stalkClosedPointTo xA).hom g) =
        (Scheme.Hom.stalkMap xA (IsLocalRing.closedPoint A)).hom g :=
      CategoryTheory.Iso.hom_inv_id_apply (stalkClosedPointIso (.of A)) _
    rw [← h1, stalkClosedPointIso_inv, htost]
    rfl

  rw [Scheme.stalkClosedPointTo_comp]
  change (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap A K)))).hom
    ((Scheme.Hom.stalkMap xA _).hom ((X.presheaf.stalkSpecializes h).hom g)) = _
  have hnat := congrArg (fun f => f.hom g) (Scheme.Hom.stalkSpecializes_stalkMap xA _ _ hR)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat
  erw [hnat]
  rw [hw, TopCat.Presheaf.germ_stalkSpecializes_apply, ← CommRingCat.comp_apply,
    Scheme.germ_stalkClosedPointTo_Spec]
  change ((Scheme.ΓSpecIso (.of A)).inv ≫ (Scheme.ΓSpecIso (.of A)).hom ≫ CommRingCat.ofHom (algebraMap A K)).hom _ = _
  rw [Iso.inv_hom_id_assoc]
  rfl

end AlgebraicGeometry.GenericValue

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_ord_apply_pointEquivPlace_jqModC_pos_of_stalkClosedPointTo_mem_maximalIdeal_of_ffEquiv_symm_stalkMap_eq_jq_cuspSection_of_ratCurveModel_compat_of_neZero.AlgebraicGeometry NeronModelInfra ModularCurve P2MW.S_ModularCurve_ord_apply_pointEquivPlace_jqModC_pos_of_stalkClosedPointTo_mem_maximalIdeal_of_ffEquiv_symm_stalkMap_eq_jq_cuspSection_of_ratCurveModel_compat_of_neZero.ModularCurve AlgebraicCurve IsLocalRing CuspForm"

namespace ModularCurve p2m_export "ModularCurve" "arithmeticGalois modularFunctionFieldBar jq coeff_jq_neg_one jq_mem modularFunctionFieldFull modularFunctionField_le_full coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange IsPlaceReductionModL modularFunctionFieldFullC jqModC_mem_full jqModC baseChangeEquiv qSeriesBar_algebraMap cuspInftyFull coe_ffEquiv_symm_stalkMap_eq_coeffEmb_ffEquiv_symm_of_galoisCompat_of_placeCompat IsPlaceReductionModL.coordinate_clauses isRational_place_modularFunctionFieldBar" namespace ZeroAtLift end ModularCurve.ZeroAtLift
p2m_open_scoped "ModularCurve" in
theorem ModularCurve.ZeroAtLift.core
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))
    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull N))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)
    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)

    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) g • Mη.pointEquivPlace x)
    (hcompat : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
          pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))))
        (x₀ : closedPoints M₀.C),
      y ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      (y ≫ inv e₀).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 →
      ((Mη.pointEquivPlace x).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
              (B := ↥(modularFunctionFieldFull N))).toRingHom) =
        (M₀.placeOfPoint x₀).toValuationSubring.toSubring))
(A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N))
    (hr : IsPlaceReductionModL A N r)
    (xA1 : Spec (CommRingCat.of ↥A) ⟶ X)
    (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hx : x.1 ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA1)
    (g : X.presheaf.stalk (xA1.base (IsLocalRing.closedPoint ↥A)))
    (hg : (Scheme.stalkClosedPointTo xA1).hom g ∈ IsLocalRing.maximalIdeal ↥A)
    (hgenP : (e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))).base (genericPoint M₀.C) ⤳ xA1.base (IsLocalRing.closedPoint ↥A))
    (hgj : M₀.ffEquiv.symm ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) (genericPoint M₀.C)).hom
        ((X.presheaf.stalkSpecializes hgenP).hom g)) = ⟨jq, modularFunctionField_le_full N (jq_mem N)⟩) :
    0 < (r (Mη.pointEquivPlace x)).ord
        (⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) N⟩ : modularFunctionFieldFullC (ResidueField ↥A) N) := by
  classical

  have hRQB : algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) = (algebraMap ℚ (AlgebraicClosure ℚ)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ) := by
    ext r
    rfl
  have hcondL : pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) ≫ c =
      (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))) := by
    rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hRQB]
  let Lm : pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))) := pullback.lift _ _ hcondL
  let θ : Mη.C ⟶ M₀.C := eη ≫ Lm ≫ inv e₀
  have hθ : θ ≫ e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))) = eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) := by
    change (eη ≫ Lm ≫ inv e₀) ≫ e₀ ≫ pullback.fst c _ = _
    rw [Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]

  have hφ : x.1 ≫ θ ≫ e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))) = Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ))) ≫ xA1 := by
    rw [hθ, hx]
    rfl
  have h2 : (x.1 ≫ θ ≫ e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ⤳ xA1.base (IsLocalRing.closedPoint ↥A) := by
    rw [hφ]
    exact (IsLocalRing.specializes_closedPoint _).map xA1.base.hom.continuous

  obtain ⟨s, hsdef⟩ : ∃ s : M₀.C.presheaf.stalk (θ.base (x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)))),
      s = (Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) (θ.base (x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))))).hom ((X.presheaf.stalkSpecializes h2).hom g) :=
    ⟨_, rfl⟩
  obtain ⟨sη, hsηdef⟩ : ∃ sη : Mη.C.presheaf.stalk (x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))), sη = (Scheme.Hom.stalkMap θ (x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)))).hom s := ⟨_, rfl⟩

  have hval : (Scheme.stalkClosedPointTo x.1).hom sη = ((Scheme.stalkClosedPointTo xA1).hom g : (AlgebraicClosure ℚ)) := by
    have h := AlgebraicGeometry.GenericValue.stalkClosedPointTo_stalkSpecializes_eq_algebraMap xA1
      (x.1 ≫ θ ≫ e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) hφ h2 g
    rw [Scheme.stalkClosedPointTo_comp, Scheme.Hom.stalkMap_comp] at h
    rw [hsηdef, hsdef]
    exact h

  obtain ⟨hmem, -, heval⟩ :=
    AlgebraicCurve.CurveModel.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo Mη x sη
  rw [hval] at heval

  have hs0 : M₀.ffEquiv.symm (algebraMap (M₀.C.presheaf.stalk (θ.base (x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))))) M₀.C.functionField s) =
      ⟨jq, modularFunctionField_le_full N (jq_mem N)⟩ := by
    rw [← hgj]
    congr 1
    rw [hsdef]
    change (M₀.C.presheaf.stalkSpecializes ((genericPoint_spec M₀.C).specializes (by trivial))).hom
      ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) (θ.base (x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))))).hom ((X.presheaf.stalkSpecializes h2).hom g)) = _
    have hnat := congrArg (fun f => f.hom ((X.presheaf.stalkSpecializes h2).hom g))
      (Scheme.Hom.stalkSpecializes_stalkMap (e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) (genericPoint M₀.C) (θ.base (x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))))
        ((genericPoint_spec M₀.C).specializes (by trivial)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat
    erw [← hnat]
    congr 1
    exact TopCat.Presheaf.stalkSpecializes_comp_apply _ _ _ _
  have hff := ModularCurve.coe_ffEquiv_symm_stalkMap_eq_coeffEmb_ffEquiv_symm_of_galoisCompat_of_placeCompat
    N p c M₀ e₀ he₀ Mη eη heη hgal hcompat θ hθ (x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) s
  rw [hs0] at hff
  have hread : Mη.ffEquiv.symm (algebraMap (Mη.C.presheaf.stalk (x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)))) Mη.C.functionField sη) =
      (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩ :
        modularFunctionFieldBar N) := by
    apply Subtype.ext
    rw [hsηdef]
    exact hff
  rw [hread] at hmem heval

  have hrat : (Mη.pointEquivPlace x).IsRational := ModularCurve.isRational_place_modularFunctionFieldBar N _
  have hne : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩ :
        modularFunctionFieldBar N) ≠
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((Scheme.stalkClosedPointTo xA1).hom g : (AlgebraicClosure ℚ)) := by
    intro h
    have hc := congrArg (fun f : modularFunctionFieldBar N => (f : LaurentSeries (AlgebraicClosure ℚ)).coeff (-1)) h
    simp only at hc
    rw [show ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((Scheme.stalkClosedPointTo xA1).hom g : (AlgebraicClosure ℚ)) :
        modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.single 0 ((Scheme.stalkClosedPointTo xA1).hom g : (AlgebraicClosure ℚ))
        from ModularCurve.qSeriesBar_algebraMap _] at hc
    rw [coeffEmb_coeff, coeff_jq_neg_one, map_one, HahnSeries.coeff_single_of_ne (by decide)] at hc
    exact one_ne_zero hc
  have hord := (AlgebraicCurve.Place.mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos (Mη.pointEquivPlace x) hrat _ _ hne).mp ⟨hmem, heval⟩

  have hcl := (ModularCurve.IsPlaceReductionModL.coordinate_clauses N p hpN A hA r hr).1 (Mη.pointEquivPlace x)
    ((Scheme.stalkClosedPointTo xA1).hom g) hord
  rw [(IsLocalRing.residue_eq_zero_iff _).mpr hg, map_zero, sub_zero] at hcl
  exact hcl

theorem solution
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsIntegral X] [IsProper c]
    [SmoothOfRelativeDimension 1 c]

    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull N))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)

    (εinf : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))) c)
    (x₀ : closedPoints M₀.C)
    (y : Spec (CommRingCat.of ℚ) ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))))
    (hx₀ : M₀.placeOfPoint x₀ = cuspInftyFull N)
    (hy : y ≫ pullback.snd c _ = 𝟙 _)
    (hyε : y ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)) ≫ εinf.1)
    (hyx₀ : (y ≫ inv e₀).base (IsLocalRing.closedPoint ℚ) = x₀.1)

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)

    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) g • Mη.pointEquivPlace x)
    (hcompat : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
          pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))))
        (x₀ : closedPoints M₀.C),
      y ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      (y ≫ inv e₀).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 →
      ((Mη.pointEquivPlace x).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
              (B := ↥(modularFunctionFieldFull N))).toRingHom) =
        (M₀.placeOfPoint x₀).toValuationSubring.toSubring))
    (ρ : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p → (↥(GaloisRep.ratLocalizedAt p) →+* ↥A))
    (hρ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
      A.subtype.comp (ρ A hA) = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
    (Ms : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
      CurveModel (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N))
    (es : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p), (Ms A hA).C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      ((residue ↥A).comp (ρ A hA)))))
    (hes_iso : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p), IsIso (es A hA))
    (hes : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
      es A hA ≫ pullback.snd c _ = (Ms A hA).toBase)

    (hsp : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [IsAlgClosed (ResidueField ↥A)],
      ∃ r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
          Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N),
        IsPlaceReductionModL A N r ∧
        ∀ (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA))) c)
          (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
          (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C //
            q ≫ (Ms A hA).toBase = 𝟙 _}),
          x.1 ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1 →
          y.1 ≫ es A hA ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xA.1 →
          (Ms A hA).pointEquivPlace y = r (Mη.pointEquivPlace x))

    (s : Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) (hs : IsClosed ({s} : Set (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))))
    (hspec : (e₀ ≫ pullback.fst c _).base x₀.1 ⤳ εinf.1.base s)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N))
    (hr : IsPlaceReductionModL A N r)
    (hrsp : ∀ (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA))) c)
          (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
          (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C //
            q ≫ (Ms A hA).toBase = 𝟙 _}),
          x.1 ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1 →
          y.1 ≫ es A hA ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xA.1 →
          (Ms A hA).pointEquivPlace y = r (Mη.pointEquivPlace x))
    (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA))) c)
    (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hx : x.1 ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1)
    (g : X.presheaf.stalk (xA.1.base (IsLocalRing.closedPoint ↥A)))
    (hg : (Scheme.stalkClosedPointTo xA.1).hom g ∈ IsLocalRing.maximalIdeal ↥A)
    (hgenP : (e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))).base (genericPoint M₀.C) ⤳ xA.1.base (IsLocalRing.closedPoint ↥A))
    (hgj : M₀.ffEquiv.symm ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) (genericPoint M₀.C)).hom
        ((X.presheaf.stalkSpecializes hgenP).hom g)) = ⟨jq, modularFunctionField_le_full N (jq_mem N)⟩) :
    0 < (r (Mη.pointEquivPlace x)).ord
        (⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) N⟩ : modularFunctionFieldFullC (ResidueField ↥A) N) :=
  ModularCurve.ZeroAtLift.core N p hpN c M₀ e₀ he₀ Mη eη heη hgal hcompat A hA r hr xA.1 x hx g hg hgenP hgj

end S_ModularCurve_ord_apply_pointEquivPlace_jqModC_pos_of_stalkClosedPointTo_mem_maximalIdeal_of_ffEquiv_symm_stalkMap_eq_jq_cuspSection_of_ratCurveModel_compat_of_neZero
end P2MW
export P2MW.S_ModularCurve_ord_apply_pointEquivPlace_jqModC_pos_of_stalkClosedPointTo_mem_maximalIdeal_of_ffEquiv_symm_stalkMap_eq_jq_cuspSection_of_ratCurveModel_compat_of_neZero (solution)
