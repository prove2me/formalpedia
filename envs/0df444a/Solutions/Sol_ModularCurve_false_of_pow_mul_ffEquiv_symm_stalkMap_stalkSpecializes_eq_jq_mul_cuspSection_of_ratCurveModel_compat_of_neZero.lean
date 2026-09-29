-- Prove2me | solution 1 for ModularCurve.false_of_pow_mul_ffEquiv_symm_stalkMap_stalkSpecializes_eq_jq_mul_cuspSection_of_ratCurveModel_compat_of_neZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/ef5401b6-2d90-5545-a7c7-cc32be095c6f

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

import Theorems.Thm_AlgebraicGeometry_isPrime_span_germ_and_ne_zero_of_isIntegral_fibre_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_opens_fromSpecStalk_mem_and_forall_exists_unit_mul_eq_of_not_mem_prime
import Theorems.Thm_ModularCurve_infinite_setOf_base_closedPoint_mem_of_fromSpecStalk_span_germ_mem_cuspSection_of_ratCurveModel_compat_of_neZero
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_comp_eq_specMap_and_specMap_comp_eq_and_stalkClosedPointTo_mul_of_henselianLocalRing
import Theorems.Thm_ModularCurve_ord_apply_pointEquivPlace_jqModC_pos_of_stalkClosedPointTo_mem_maximalIdeal_of_ffEquiv_symm_stalkMap_eq_jq_cuspSection_of_ratCurveModel_compat_of_neZero
import Theorems.Thm_ModularCurve_false_of_infinite_setOf_ord_pointEquivPlace_jqModC_ne_zero_cuspSection_of_ratCurveModel_compat_of_neZero
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_ringHom_functionField_ffEquiv_symm_stalkMap_eq_of_isIso_pullback
import Theorems.Thm_ValuationSubring_charP_residueField_of_liesOverPrime
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_irreducible_natCast_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_false_of_pow_mul_ffEquiv_symm_stalkMap_stalkSpecializes_eq_jq_mul_cuspSection_of_ratCurveModel_compat_of_neZero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_frobeniusModL"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve AlgebraicCurve IsLocalRing CuspForm

universe u

namespace VertKit

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section OpenImm
variable {X X₁ : Scheme.{u}} [IsIntegral X] [IsIntegral X₁] (f : X₁ ⟶ X) [IsOpenImmersion f]

theorem app_genericPoint : f (genericPoint X₁) = genericPoint X := genericPoint_eq_of_isOpenImmersion f

theorem insep : Inseparable (genericPoint X) (f (genericPoint X₁)) := Inseparable.of_eq (app_genericPoint f).symm

noncomputable def θiso : X.functionField ≅ X₁.functionField :=
  X.presheaf.stalkCongr (insep f) ≪≫ asIso (f.stalkMap (genericPoint X₁))

theorem θiso_hom_apply (z : X.functionField) :
    (θiso f).hom z = f.stalkMap (genericPoint X₁) (X.presheaf.stalkSpecializes (insep f).ge z) := rfl

theorem θiso_algebraMap (x₁ : X₁) (z : X.presheaf.stalk (f x₁)) :
    algebraMap (X₁.presheaf.stalk x₁) X₁.functionField (f.stalkMap x₁ z) =
      (θiso f).hom (algebraMap (X.presheaf.stalk (f x₁)) X.functionField z) := by
  rw [θiso_hom_apply, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
    TopCat.Presheaf.stalkSpecializes_comp_apply]
  exact (Scheme.Hom.stalkSpecializes_stalkMap_apply f (genericPoint X₁) x₁
    ((genericPoint_spec X₁).specializes (Set.mem_univ x₁)) z).symm

end OpenImm

theorem isLocalization_away_ratLocalizedAt (p : ℕ) [Fact p.Prime] :
    IsLocalization.Away (((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))) ℚ := by
  haveI : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  have hirr : Irreducible (((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))) := GaloisRep.irreducible_natCast_ratLocalizedAt p Fact.out
  have hinj : Function.Injective (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ) := Subtype.val_injective
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [map_pow]
    exact IsUnit.pow _ (by
      rw [isUnit_iff_ne_zero, ne_eq, map_eq_zero_iff _ hinj]
      exact hirr.ne_zero)
  · intro q

    haveI := GaloisRep.isFractionRing_ratLocalizedAt p
    obtain ⟨⟨a, ⟨b, hb⟩⟩, hq⟩ := IsLocalization.surj (nonZeroDivisors ↥(GaloisRep.ratLocalizedAt p)) q
    have hb0 : (b : ↥(GaloisRep.ratLocalizedAt p)) ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hirr
    refine ⟨⟨a * ↑u⁻¹, ⟨_, n, rfl⟩⟩, ?_⟩
    change q * algebraMap _ ℚ (((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ^ n) = algebraMap _ ℚ (a * ↑u⁻¹)
    have hq' : q * algebraMap _ ℚ b = algebraMap _ ℚ a := hq
    rw [hu, map_mul] at hq'
    rw [map_mul, ← hq']
    have hu1 : algebraMap _ ℚ (↑u : ↥(GaloisRep.ratLocalizedAt p)) * algebraMap _ ℚ (↑u⁻¹ : ↥(GaloisRep.ratLocalizedAt p)) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    linear_combination (-(q * algebraMap _ ℚ (((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ^ n))) * hu1
  · intro a b hab
    exact ⟨1, by rw [hinj hab]⟩

end VertKit

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
    (m : ℕ) (hm : 0 < m) (a b : X.presheaf.stalk (εinf.1.base s))
    (ha : a ∉ Ideal.span {(X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))))})
    (hb : b ∉ Ideal.span {(X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))))})
    (hab : ((p : ℚ) : LaurentSeries ℚ) ^ m * ((M₀.ffEquiv.symm (algebraMap (M₀.C.presheaf.stalk x₀.1) M₀.C.functionField
          ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) x₀.1).hom ((X.presheaf.stalkSpecializes hspec).hom a))) :
          ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) =
      (jq : LaurentSeries ℚ) * ((M₀.ffEquiv.symm (algebraMap (M₀.C.presheaf.stalk x₀.1) M₀.C.functionField
          ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) x₀.1).hom ((X.presheaf.stalkSpecializes hspec).hom b))) :
          ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ)) :
    False := by
  classical
  haveI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  haveI : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  set f₀ := e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))) with hf₀def

  let ιP : ∀ P : X, ↥(GaloisRep.ratLocalizedAt p) →+* X.presheaf.stalk P := fun P =>
    (X.presheaf.germ ⊤ P trivial).hom.comp (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom)
  have hιP : ∀ (P : X) (r : ↥(GaloisRep.ratLocalizedAt p)), ιP P r = (X.presheaf.germ ⊤ P trivial).hom (c.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom r)) := fun _ _ => rfl
  set ϖ := (X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom
    ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))) with hϖdef

  obtain ⟨A, -, hA, -⟩ := ValuationSubring.exists_liesOverPrime_isFrobeniusAt_ratAlgClosure ⟨p, Fact.out⟩
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime p A hA
  haveI : HenselianLocalRing ↥A := ValuationSubring.henselianLocalRing_of_isAlgClosed A
  letI algRA : Algebra ↥(GaloisRep.ratLocalizedAt p) ↥A := (ρ A hA).toAlgebra
  have hρp : (ρ A hA) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ∈ IsLocalRing.maximalIdeal ↥A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    have : ((ρ A hA ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) : ↥A) : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) := by
      rw [map_natCast]
      exact map_natCast A.subtype p
    rw [this]
    exact hA

  let q : ↥(GaloisRep.ratLocalizedAt p) →+* ResidueField ↥A := (IsLocalRing.residue ↥A).comp (ρ A hA)
  have hsmax : s.asIdeal = IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt p) :=
    IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isClosed_singleton_iff_isMaximal s).mp hs)
  have hmaxp : (Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} : Ideal ↥(GaloisRep.ratLocalizedAt p)).IsMaximal := by
    rw [← GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p Fact.out]
    exact IsLocalRing.maximalIdeal.isMaximal _
  have hkerq : RingHom.ker q = Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))} := by
    apply (hmaxp.eq_of_le (RingHom.ker_ne_top q) ?_).symm
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    change IsLocalRing.residue ↥A (ρ A hA ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))) = 0
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hρp
  haveI : IsIso (es A hA) := hes_iso A hA
  haveI : Nonempty ((pullback c (Spec.map (CommRingCat.ofHom q)) : Scheme.{0})) :=
    Nonempty.map (fun t => (es A hA).base t) inferInstance
  haveI : IsIntegral (pullback c (Spec.map (CommRingCat.ofHom q))) :=
    isIntegral_of_isOpenImmersion (inv (es A hA))
  have hcs : c.base (εinf.1.base s) = s := by
    change (εinf.1 ≫ c).base s = s
    rw [εinf.2]; rfl
  have hsmem : εinf.1.base s ∈ Set.range (pullback.fst c (Spec.map (CommRingCat.ofHom q))).base := by
    rw [Scheme.Pullback.range_fst]
    refine ⟨⟨⊥, Ideal.bot_prime⟩, ?_⟩
    change (Spec.map (CommRingCat.ofHom q)).base _ = c.base (εinf.1.base s)
    rw [hcs]
    apply PrimeSpectrum.ext
    change Ideal.comap q ⊥ = s.asIdeal
    rw [← RingHom.ker_eq_comap_bot, hkerq, hsmax, GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p Fact.out]
  obtain ⟨hprime, hϖ0⟩ :=
    AlgebraicGeometry.isPrime_span_germ_and_ne_zero_of_isIntegral_fibre_of_smoothOfRelativeDimension_one
      ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) (by exact_mod_cast (Fact.out : p.Prime).ne_zero) hmaxp q hkerq c (εinf.1.base s) hsmem

  haveI := hprime
  obtain ⟨U, hU, hunit⟩ :=
    AlgebraicGeometry.Scheme.exists_opens_fromSpecStalk_mem_and_forall_exists_unit_mul_eq_of_not_mem_prime
      (εinf.1.base s) (Ideal.span {ϖ}) a b ha hb

  have hinfU := ModularCurve.infinite_setOf_base_closedPoint_mem_of_fromSpecStalk_span_germ_mem_cuspSection_of_ratCurveModel_compat_of_neZero
    N p hpN c M₀ e₀ he₀ εinf x₀ y hx₀ hy hyε hyx₀ Mη eη heη hgal hcompat ρ hρ Ms es hes_iso hes hsp s hs hspec A hA hprime U hU

  obtain ⟨r, hr, hrsp⟩ := hsp A hA

  obtain ⟨Θ, hΘ1, hΘ2, hΘ3, -⟩ :=
    AlgebraicCurve.CurveModel.exists_ringHom_functionField_ffEquiv_symm_stalkMap_eq_of_isIso_pullback
      (R := ↥(GaloisRep.ratLocalizedAt p)) (K := ℚ) Subtype.val_injective M₀ c e₀ he₀
  have hROUTE : ∀ z : X.presheaf.stalk (εinf.1.base s),
      M₀.ffEquiv.symm (algebraMap (M₀.C.presheaf.stalk x₀.1) M₀.C.functionField
        ((Scheme.Hom.stalkMap f₀ x₀.1).hom ((X.presheaf.stalkSpecializes hspec).hom z))) =
        Θ (algebraMap (X.presheaf.stalk (εinf.1.base s)) X.functionField z) := by
    intro z
    rw [hΘ2 x₀.1]
    congr 1
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, ← CategoryTheory.comp_apply,
      TopCat.Presheaf.stalkSpecializes_comp]
  have hC : ∀ (inst : Algebra ℚ ↥(modularFunctionFieldFull N)) (t : ℚ),
      ((@algebraMap ℚ ↥(modularFunctionFieldFull N) _ _ inst t : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) =
        HahnSeries.C t := by
    intro inst t
    exact RingHom.congr_fun (RingHom.ext_rat
      (((modularFunctionFieldFull N).val : ↥(modularFunctionFieldFull N) →+* LaurentSeries ℚ).comp
        (@algebraMap ℚ ↥(modularFunctionFieldFull N) _ _ inst)) HahnSeries.C) t
  have hΘp : ∀ P : X, Θ (algebraMap (X.presheaf.stalk P) X.functionField (ιP P ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))) =
      algebraMap ℚ ↥(modularFunctionFieldFull N) (p : ℚ) := by
    intro P
    rw [hιP, hΘ3 P, map_natCast]
  have hcoep : ((algebraMap ℚ ↥(modularFunctionFieldFull N) (p : ℚ) : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) =
      ((p : ℚ) : LaurentSeries ℚ) := by
    rw [hC]
    exact eq_ratCast (HahnSeries.C : ℚ →+* LaurentSeries ℚ) (p : ℚ)

  have habΘ : (algebraMap ℚ ↥(modularFunctionFieldFull N) (p : ℚ)) ^ m *
      Θ (algebraMap (X.presheaf.stalk (εinf.1.base s)) X.functionField a) =
      ⟨jq, modularFunctionField_le_full N (jq_mem N)⟩ * Θ (algebraMap (X.presheaf.stalk (εinf.1.base s)) X.functionField b) := by
    apply Subtype.val_injective
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul, SubmonoidClass.coe_pow, hcoep, ← hROUTE a, ← hROUTE b]
    exact hab
  have hΘinj : Function.Injective Θ := Θ.injective
  have halg_inj : Function.Injective (algebraMap (X.presheaf.stalk (εinf.1.base s)) X.functionField) :=
    IsFractionRing.injective _ _
  have hb0 : b ≠ 0 := fun h => hb (h ▸ Ideal.zero_mem _)
  have hΘb : Θ (algebraMap (X.presheaf.stalk (εinf.1.base s)) X.functionField b) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hΘinj, map_eq_zero_iff _ halg_inj]; exact hb0

  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))) := by
    haveI : IsLocalization.Away (((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))) ℚ := VertKit.isLocalization_away_ratLocalizedAt p
    exact IsOpenImmersion.of_isLocalization ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))
  haveI : IsOpenImmersion (pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  haveI : IsOpenImmersion f₀ := inferInstance
  have hgenη : f₀.base (genericPoint M₀.C) = genericPoint X := VertKit.app_genericPoint f₀
  have hzero : ∀ yk : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C // q ≫ (Ms A hA).toBase = 𝟙 _},
      (yk.1 ≫ es A hA ≫ pullback.fst c _).base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ U →
      ((Ms A hA).pointEquivPlace yk).ord
        (⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) N⟩ : modularFunctionFieldFullC (ResidueField ↥A) N) ≠ 0 := by
    intro yk hyk

    set xk : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ X := yk.1 ≫ es A hA ≫ pullback.fst c _ with hxk
    have hxkc : xk ≫ c = Spec.map (CommRingCat.ofHom ((algebraMap ↥A (IsLocalRing.ResidueField ↥A)).comp
        (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥A))) := by
      rw [hxk, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (es A hA), hes A hA,
        ← Category.assoc, yk.2, Category.id_comp]
      rfl
    obtain ⟨σ, hσc, hσk, hlin⟩ :=
      AlgebraicGeometry.Smooth.exists_comp_eq_specMap_and_specMap_comp_eq_and_stalkClosedPointTo_mul_of_henselianLocalRing
        c xk hxkc
    set y' : X := σ.base (IsLocalRing.closedPoint ↥A) with hy'
    have hy'xk : xk.base (IsLocalRing.closedPoint (ResidueField ↥A)) = y' := by
      rw [← hσk]
      change σ.base ((Spec.map (CommRingCat.ofHom (algebraMap ↥A (IsLocalRing.ResidueField ↥A)))).base
        (IsLocalRing.closedPoint (ResidueField ↥A))) = σ.base (IsLocalRing.closedPoint ↥A)
      congr 1
      exact IsLocalRing.comap_closedPoint (IsLocalRing.residue ↥A)
    have hy'U : y' ∈ U := hy'xk ▸ hyk

    obtain ⟨u, hu⟩ := hunit y' hy'U
    set g : X.presheaf.stalk y' := ιP y' (((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ^ m) * (u : X.presheaf.stalk y') with hg
    have hgm : (Scheme.stalkClosedPointTo σ).hom g ∈ IsLocalRing.maximalIdeal ↥A := by
      rw [hg, hιP, hlin]
      change (ρ A hA) (((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) ^ m) * _ ∈ _
      rw [map_pow]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hρp _ hm)
    have hgenP : f₀.base (genericPoint M₀.C) ⤳ y' := by
      rw [hgenη]; exact (genericPoint_spec X).specializes (Set.mem_univ _)
    have hgj : M₀.ffEquiv.symm ((Scheme.Hom.stalkMap f₀ (genericPoint M₀.C)).hom
        ((X.presheaf.stalkSpecializes hgenP).hom g)) = ⟨jq, modularFunctionField_le_full N (jq_mem N)⟩ := by
      rw [hΘ1 y' hgenP g, hg, map_mul, map_mul, map_pow, map_pow, map_pow, hΘp y']
      have huΘ := congrArg Θ hu
      rw [map_mul] at huΘ
      apply mul_right_cancel₀ hΘb
      rw [mul_assoc, huΘ, habΘ]

    let xA : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA))) c := ⟨σ, hσc⟩
    have hliftc : (Spec.map (CommRingCat.ofHom A.subtype) ≫ σ) ≫ c =
        𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))) := by
      rw [Category.assoc, hσc, Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      change Spec.map (CommRingCat.ofHom (A.subtype.comp (ρ A hA))) = _
      rw [hρ A hA]
    let xpt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C :=
      pullback.lift (Spec.map (CommRingCat.ofHom A.subtype) ≫ σ) (𝟙 _) hliftc ≫ inv eη
    have hxpt : xpt ≫ Mη.toBase = 𝟙 _ := by
      rw [← heη, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_snd]
    have hx : xpt ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1 := by
      change (pullback.lift _ _ hliftc ≫ inv eη) ≫ eη ≫ _ = _
      rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]
    have hpos := ModularCurve.ord_apply_pointEquivPlace_jqModC_pos_of_stalkClosedPointTo_mem_maximalIdeal_of_ffEquiv_symm_stalkMap_eq_jq_cuspSection_of_ratCurveModel_compat_of_neZero
      N p hpN c M₀ e₀ he₀ εinf x₀ y hx₀ hy hyε hyx₀ Mη eη heη hgal hcompat ρ hρ Ms es hes_iso hes hsp s hs hspec
      A hA r hr hrsp xA ⟨xpt, hxpt⟩ hx g hgm hgenP hgj

    have hred : (Ms A hA).pointEquivPlace yk = r (Mη.pointEquivPlace ⟨xpt, hxpt⟩) := by
      refine hrsp xA ⟨xpt, hxpt⟩ yk hx ?_
      change yk.1 ≫ es A hA ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (algebraMap ↥A (IsLocalRing.ResidueField ↥A))) ≫ σ
      rw [hσk]
    rw [hred]
    exact hpos.ne'

  exact ModularCurve.false_of_infinite_setOf_ord_pointEquivPlace_jqModC_ne_zero_cuspSection_of_ratCurveModel_compat_of_neZero
    N p hpN c M₀ e₀ he₀ εinf x₀ y hx₀ hy hyε hyx₀ Mη eη heη hgal hcompat ρ hρ Ms es hes_iso hes hsp s hs hspec A hA
    (hinfU.mono fun yk hyk => hzero yk hyk)

end S_ModularCurve_false_of_pow_mul_ffEquiv_symm_stalkMap_stalkSpecializes_eq_jq_mul_cuspSection_of_ratCurveModel_compat_of_neZero
end P2MW
export P2MW.S_ModularCurve_false_of_pow_mul_ffEquiv_symm_stalkMap_stalkSpecializes_eq_jq_mul_cuspSection_of_ratCurveModel_compat_of_neZero (solution)
