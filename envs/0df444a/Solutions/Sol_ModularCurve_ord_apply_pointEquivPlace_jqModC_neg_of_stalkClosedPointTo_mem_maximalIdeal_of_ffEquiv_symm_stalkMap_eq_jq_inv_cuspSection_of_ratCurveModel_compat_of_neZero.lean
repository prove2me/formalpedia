-- Prove2me | solution 1 for ModularCurve.ord_apply_pointEquivPlace_jqModC_neg_of_stalkClosedPointTo_mem_maximalIdeal_of_ffEquiv_symm_stalkMap_eq_jq_inv_cuspSection_of_ratCurveModel_compat_of_neZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/43668ba4-aa50-5041-8edb-af7bbb3a62d8

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

import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo
import Theorems.Thm_ModularCurve_IsPlaceReductionModL_coordinate_clauses
import Theorems.Thm_ModularCurve_coe_ffEquiv_symm_stalkMap_eq_coeffEmb_ffEquiv_symm_of_galoisCompat_of_placeCompat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_apply_pointEquivPlace_jqModC_neg_of_stalkClosedPointTo_mem_maximalIdeal_of_ffEquiv_symm_stalkMap_eq_jq_inv_cuspSection_of_ratCurveModel_compat_of_neZero
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve AlgebraicCurve IsLocalRing CuspForm

namespace ZLAux

universe u

theorem hom_congr_apply {R S : CommRingCat.{u}} {f g : R ⟶ S} (h : f = g) (x : R) : f.hom x = g.hom x := by rw [h]

theorem stalkClosedPointTo_comp_stalkSpecializes {X : Scheme.{u}} {A S : CommRingCat.{u}} [IsLocalRing A] [IsLocalRing S]
    (φ : A ⟶ S) (σ : Spec A ⟶ X) (g : X.presheaf.stalk (σ.base (IsLocalRing.closedPoint A)))
    (h : (Spec.map φ ≫ σ).base (IsLocalRing.closedPoint S) ⤳ σ.base (IsLocalRing.closedPoint A)) :
    (Scheme.stalkClosedPointTo (Spec.map φ ≫ σ)).hom ((X.presheaf.stalkSpecializes h).hom g) =
      φ.hom ((Scheme.stalkClosedPointTo σ).hom g) := by

  have hq : (Spec.map φ).base (IsLocalRing.closedPoint S) ⤳ IsLocalRing.closedPoint A :=
    IsLocalRing.specializes_closedPoint _

  have s1 := hom_congr_apply (Scheme.stalkClosedPointTo_comp (Spec.map φ) σ) ((X.presheaf.stalkSpecializes h).hom g)
  rw [s1]
  erw [CommRingCat.hom_comp, RingHom.comp_apply]

  have s2 := hom_congr_apply (Scheme.Hom.stalkSpecializes_stalkMap σ _ _ hq) g
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at s2
  refine (congrArg (fun t => (Scheme.stalkClosedPointTo (Spec.map φ)).hom t) s2).trans ?_

  set u := (σ.stalkMap (IsLocalRing.closedPoint A)).hom g with hu
  set a : A := (stalkClosedPointIso A).hom.hom u with ha
  have hinv : (Scheme.ΓSpecIso A).hom.hom ((Scheme.ΓSpecIso A).inv.hom a) = a := by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Iso.inv_hom_id]; rfl
  have s3 := hom_congr_apply (germ_stalkClosedPointIso_hom A) ((Scheme.ΓSpecIso A).inv.hom a)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at s3
  rw [hinv] at s3
  have hu' : u = ((Spec A).presheaf.germ ⊤ (IsLocalRing.closedPoint A) trivial).hom ((Scheme.ΓSpecIso A).inv.hom a) := by
    apply (stalkClosedPointIso A).commRingCatIsoToRingEquiv.injective
    change (stalkClosedPointIso A).hom.hom u = (stalkClosedPointIso A).hom.hom _
    rw [s3]
  have hval : (Scheme.stalkClosedPointTo σ).hom g = a := rfl
  rw [hval, hu']

  have s4 := hom_congr_apply (TopCat.Presheaf.germ_stalkSpecializes (Spec A).presheaf (U := ⊤)
    (y := IsLocalRing.closedPoint A) trivial hq) ((Scheme.ΓSpecIso A).inv.hom a)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at s4
  refine (congrArg (fun t => (Scheme.stalkClosedPointTo (Spec.map φ)).hom t) s4).trans ?_
  have s5 := hom_congr_apply (Scheme.germ_stalkClosedPointTo_Spec φ) ((Scheme.ΓSpecIso A).inv.hom a)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at s5
  rw [hinv] at s5
  exact s5

end ZLAux

open ZLAux in
set_option maxHeartbeats 6400000 in
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
        ((X.presheaf.stalkSpecializes hgenP).hom g)) = ⟨jq, modularFunctionField_le_full N (jq_mem N)⟩⁻¹) :
    (r (Mη.pointEquivPlace x)).ord
        (⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) N⟩ : modularFunctionFieldFullC (ResidueField ↥A) N) < 0 := by
  classical

  have hSpec : Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hw : (eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))) ≫ c =
      (Mη.toBase ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, heη, Category.assoc, ← hSpec]
  let θ : Mη.C ⟶ M₀.C := pullback.lift (eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))) (Mη.toBase ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) hw ≫ inv e₀
  have hθ : θ ≫ e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))) = eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) := by
    simp only [θ, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]

  have hxθ : x.1 ≫ θ ≫ e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))) = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1 := by rw [hθ]; exact hx
  have hsp : (x.1 ≫ θ ≫ e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ⤳ xA.1.base (IsLocalRing.closedPoint ↥A) := by
    rw [hxθ]
    exact (IsLocalRing.specializes_closedPoint _).map xA.1.base.hom.continuous

  have hval : ∀ (τ : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ X) (hτ : τ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1)
      (h : τ.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ⤳ xA.1.base (IsLocalRing.closedPoint ↥A)),
      (Scheme.stalkClosedPointTo τ).hom ((X.presheaf.stalkSpecializes h).hom g) =
        ((Scheme.stalkClosedPointTo xA.1).hom g : (AlgebraicClosure ℚ)) := by
    rintro τ rfl h
    exact stalkClosedPointTo_comp_stalkSpecializes (CommRingCat.ofHom A.subtype) xA.1 g h
  set a : ↥A := (Scheme.stalkClosedPointTo xA.1).hom g with ha

  let gP : Mη.C.presheaf.stalk (x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) :=
    ((θ ≫ e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))).stalkMap (x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)))).hom ((X.presheaf.stalkSpecializes hsp).hom g)
  let s₀ : M₀.C.presheaf.stalk (θ.base (x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)))) :=
    ((e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))).stalkMap (θ.base (x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))))).hom ((X.presheaf.stalkSpecializes hsp).hom g)
  have hθs : (θ.stalkMap (x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)))).hom s₀ = gP := by
    have t := hom_congr_apply (Scheme.Hom.stalkMap_comp θ (e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) (x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))))
      ((X.presheaf.stalkSpecializes hsp).hom g)
    exact t.symm
  have hvalP : (Scheme.stalkClosedPointTo x.1).hom gP = (a : (AlgebraicClosure ℚ)) := by
    have t := hval _ hxθ hsp
    have t2 := hom_congr_apply (Scheme.stalkClosedPointTo_comp x.1 (θ ≫ e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))))) ((X.presheaf.stalkSpecializes hsp).hom g)
    exact t2.symm.trans t

  have hff := ModularCurve.coe_ffEquiv_symm_stalkMap_eq_coeffEmb_ffEquiv_symm_of_galoisCompat_of_placeCompat N p c M₀ e₀ he₀
    Mη eη heη hgal hcompat θ hθ (x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) s₀
  have hgenθ : genericPoint M₀.C ⤳ θ.base (x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) :=
    (genericPoint_spec M₀.C).specializes trivial
  have hM0 : M₀.ffEquiv.symm (algebraMap (M₀.C.presheaf.stalk (θ.base (x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))))) M₀.C.functionField s₀) =
      ⟨jq, modularFunctionField_le_full N (jq_mem N)⟩⁻¹ := by
    rw [← hgj]
    congr 1
    change (M₀.C.presheaf.stalkSpecializes hgenθ).hom s₀ = _
    have t1 := hom_congr_apply (Scheme.Hom.stalkSpecializes_stalkMap (e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) (genericPoint M₀.C) _ hgenθ)
      ((X.presheaf.stalkSpecializes hsp).hom g)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at t1
    refine t1.symm.trans ?_
    congr 1
    have t2 := hom_congr_apply (TopCat.Presheaf.stalkSpecializes_comp X.presheaf
      ((e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))).base.hom.map_specializes hgenθ) hsp) g
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at t2
    exact t2
  have hJ : Mη.ffEquiv.symm (algebraMap (Mη.C.presheaf.stalk (x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)))) Mη.C.functionField gP) = (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩ : ↥(modularFunctionFieldBar N))⁻¹ := by
    apply Subtype.ext
    rw [← hθs, hff, hM0]
    push_cast
    rw [map_inv₀]

  obtain ⟨hmem, hres, -⟩ := AlgebraicCurve.CurveModel.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo Mη x gP
  rw [hvalP] at hres
  set w := Mη.pointEquivPlace x with hw'
  have hmem' : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩ : ↥(modularFunctionFieldBar N))⁻¹ ∈ w.toValuationSubring := hJ ▸ hmem
  have hres' : IsLocalRing.residue ↥w.toValuationSubring ⟨_, hmem'⟩ = algebraMap (AlgebraicClosure ℚ) w.ResidueField (a : (AlgebraicClosure ℚ)) := by
    have e2 : (⟨_, hmem'⟩ : w.toValuationSubring) = ⟨_, hmem⟩ := Subtype.ext hJ.symm
    rw [e2, hres]

  have ordpos : ∀ (f : ↥(modularFunctionFieldBar N)) (hf : f ∈ w.toValuationSubring), f ≠ 0 →
      (⟨f, hf⟩ : w.toValuationSubring) ∈ IsLocalRing.maximalIdeal ↥w.toValuationSubring → 0 < w.ord f := by
    intro f hf hf0 hfmax
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥w.toValuationSubring
    have hb0 : (⟨f, hf⟩ : w.toValuationSubring) ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
    obtain ⟨n, u, hbu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
    have hn : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, mul_one] at hbu
      exact (IsLocalRing.mem_maximalIdeal _).mp hfmax (hbu ▸ u.isUnit)
    have hval' := congrArg Subtype.val hbu
    push_cast at hval'
    rw [show f = ((u : w.toValuationSubring) : ↥(modularFunctionFieldBar N)) * (((ϖ : w.toValuationSubring) : ↥(modularFunctionFieldBar N)) ^ (n : ℤ)) from by
        rw [zpow_natCast]; exact_mod_cast hval']
    rw [w.ord_unit_smul_zpow u hϖ]
    exact_mod_cast Nat.pos_of_ne_zero hn
  have memmax_of_ordpos : ∀ (f : ↥(modularFunctionFieldBar N)), 0 < w.ord f →
      ∃ hf : f ∈ w.toValuationSubring, (⟨f, hf⟩ : w.toValuationSubring) ∈ IsLocalRing.maximalIdeal ↥w.toValuationSubring := by
    intro f hf
    have hf0 : f ≠ 0 := by rintro rfl; simp at hf
    have hfmem : f ∈ w.toValuationSubring := by
      by_contra hnot
      have hinv : f⁻¹ ∈ w.toValuationSubring := (w.toValuationSubring.mem_or_inv_mem f).resolve_left hnot
      have hinvmax : (⟨f⁻¹, hinv⟩ : w.toValuationSubring) ∈ IsLocalRing.maximalIdeal ↥w.toValuationSubring := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        apply hnot
        have h1 : ((hu.unit⁻¹ : (↥w.toValuationSubring)ˣ) : w.toValuationSubring).val * f⁻¹ = 1 := by
          have hu1 : ((hu.unit⁻¹ : (↥w.toValuationSubring)ˣ) : w.toValuationSubring) * (hu.unit : w.toValuationSubring) = 1 :=
            Units.inv_mul _
          rw [IsUnit.unit_spec] at hu1
          have h1' := congrArg Subtype.val hu1
          push_cast at h1'
          exact h1'
        have hxf : ((hu.unit⁻¹ : (↥w.toValuationSubring)ˣ) : w.toValuationSubring).val = f := (mul_inv_eq_one₀ hf0).mp h1
        exact hxf ▸ ((hu.unit⁻¹ : (↥w.toValuationSubring)ˣ) : w.toValuationSubring).2
      have := ordpos f⁻¹ hinv (inv_ne_zero hf0) hinvmax
      rw [w.ord_inv] at this
      omega
    refine ⟨hfmem, ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := w.ord_coe_unit hu.unit
    simp only [IsUnit.unit_spec] at this
    omega

  have hle : ∀ a' : ↥A, w.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩ : ↥(modularFunctionFieldBar N)) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (a' : (AlgebraicClosure ℚ))) ≤ 0 := by
    intro a'
    by_contra hlt
    push Not at hlt
    obtain ⟨hfmem, hfmax⟩ := memmax_of_ordpos _ hlt

    have hJmem : ((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩ : ↥(modularFunctionFieldBar N)) : ↥(modularFunctionFieldBar N)) ∈ w.toValuationSubring := by
      have := add_mem hfmem (w.algebraMap_mem' (a' : (AlgebraicClosure ℚ)))
      simpa using this
    have hresJ : IsLocalRing.residue ↥w.toValuationSubring ⟨_, hJmem⟩ = algebraMap (AlgebraicClosure ℚ) w.ResidueField (a' : (AlgebraicClosure ℚ)) := by
      have hz : IsLocalRing.residue ↥w.toValuationSubring ⟨_, hfmem⟩ = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hfmax
      have e1 : (⟨_, hJmem⟩ : w.toValuationSubring) = ⟨_, hfmem⟩ + algebraMap (AlgebraicClosure ℚ) ↥w.toValuationSubring (a' : (AlgebraicClosure ℚ)) := by
        apply Subtype.ext
        simp [Place.coe_algebraMap]
      rw [e1, map_add, hz, zero_add]
      exact (IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ) ↥w.toValuationSubring w.ResidueField _).symm
    have hprod : IsLocalRing.residue ↥w.toValuationSubring (⟨_, hJmem⟩ * ⟨_, hmem'⟩) = 1 := by
      have : (⟨_, hJmem⟩ * ⟨_, hmem'⟩ : w.toValuationSubring) = 1 := by
        apply Subtype.ext
        have hJ0 : ((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩ : ↥(modularFunctionFieldBar N)) : ↥(modularFunctionFieldBar N)) ≠ 0 := by
          intro h0
          have := congrArg (fun f : ↥(modularFunctionFieldBar N) => (f : LaurentSeries (AlgebraicClosure ℚ)).coeff (-1)) h0
          simp only [ZeroMemClass.coe_zero, HahnSeries.coeff_zero] at this
          change (coeffEmb (AlgebraicClosure ℚ) jq).coeff (-1) = 0 at this
          rw [coeffEmb_coeff, coeff_jq_neg_one, map_one] at this
          exact one_ne_zero this
        simp [mul_inv_cancel₀ hJ0]
      rw [this, map_one]
    rw [map_mul, hresJ, hres', ← map_mul, ← map_one (algebraMap (AlgebraicClosure ℚ) w.ResidueField)] at hprod
    have hinj : Function.Injective (algebraMap (AlgebraicClosure ℚ) w.ResidueField) := (algebraMap (AlgebraicClosure ℚ) w.ResidueField).injective
    have h1 : (a' : (AlgebraicClosure ℚ)) * (a : (AlgebraicClosure ℚ)) = 1 := hinj hprod
    have h1A : a' * a = 1 := Subtype.ext (by exact_mod_cast h1)
    have hunit : IsUnit a := IsUnit.of_mul_eq_one a' (by rw [mul_comm]; exact h1A)
    exact (IsLocalRing.mem_maximalIdeal _).mp hg hunit
  obtain ⟨-, hcl2, -, -⟩ := ModularCurve.IsPlaceReductionModL.coordinate_clauses N p hpN A hA r hr
  exact hcl2 w hle

end S_ModularCurve_ord_apply_pointEquivPlace_jqModC_neg_of_stalkClosedPointTo_mem_maximalIdeal_of_ffEquiv_symm_stalkMap_eq_jq_inv_cuspSection_of_ratCurveModel_compat_of_neZero
end P2MW
export P2MW.S_ModularCurve_ord_apply_pointEquivPlace_jqModC_neg_of_stalkClosedPointTo_mem_maximalIdeal_of_ffEquiv_symm_stalkMap_eq_jq_inv_cuspSection_of_ratCurveModel_compat_of_neZero (solution)
