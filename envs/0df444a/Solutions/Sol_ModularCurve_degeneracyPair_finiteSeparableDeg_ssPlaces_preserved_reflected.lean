-- Prove2me | solution 1 for ModularCurve.degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/7bb4acdb-63b0-5354-950b-d1e78a54c189

import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Theorems.Thm_ModularCurve_degeneracyPair_finite_separable_identity_ssPlaces
import Theorems.Thm_ModularCurve_degeneracyPair_finrankAlong_and_place_transports
import Theorems.Thm_ModularCurve_mem_ssJSet_of_mem_roots_fibrePoly
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected
p2m_attr_erase "instance" "ModularCurve.SpecializationWitnessData.addCommGroup ModularCurve.CommutingHeckeFamily.commRing_adjoin AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "ModularCurve.coe_heckeBetaC AlgebraicCurve.Divisor.coe_degZeroEnd ModularCurve.coe_heckeAlphaC ModularCurve.CommutingHeckeFamily.mk.injEq ModularCurve.SpecializationWitnessData.mk.sizeOf_spec ModularCurve.SpecializationWitnessData.mk.injEq ModularCurve.CommutingHeckeFamily.mk.sizeOf_spec ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero"
p2m_attr_erase "simp" "compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.ProjectiveLine.map_mk"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

p2m_open "AlgebraicCurve ModularCurve~coeffMap_injective Polynomial"

namespace CuspsLegsE4

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) : Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  apply hf
  rw [← coeffMap_coeff, ← coeffMap_coeff, h]

theorem map_eval₂_aeval_toRingHom {A B : Type*} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B]
    (g : A →+* B) (Φ : Polynomial (Polynomial ℤ)) (a b : A) :
    g (Φ.eval₂ (aeval (R := ℤ) a).toRingHom b) = Φ.eval₂ (aeval (R := ℤ) (g a)).toRingHom (g b) := by
  rw [hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp

theorem eval₂_aeval_jqModC_jqNModC_eq_zero (K : Type*) [Field K] (ℓ : ℕ) [NeZero ℓ]
    (data : ModularPolynomialData ℓ) :
    data.Φ.eval₂ (aeval (R := ℤ) (jqModC K)).toRingHom (jqNModC K ℓ) = 0 := by
  have h0 : data.Φ.eval₂ (aeval (R := ℤ) (jqModC ℚ)).toRingHom (jqNModC ℚ ℓ) = 0 := by
    rw [jqNModC_rat, jqModC_rat]
    exact data.eval_eq_zero
  have hZ : data.Φ.eval₂ (aeval (R := ℤ) (jqModC ℤ)).toRingHom (jqNModC ℤ ℓ) = 0 := by
    apply coeffMap_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
    rw [map_eval₂_aeval_toRingHom, coeffMap_jqNModC, coeffMap_jqModC, h0, map_zero]
  have := congrArg (coeffMap (Int.castRingHom K)) hZ
  rwa [map_eval₂_aeval_toRingHom, coeffMap_jqNModC, coeffMap_jqModC, map_zero] at this

theorem eval₂_aeval_jqNModC_jqModC_eq_zero (K : Type*) [Field K] (ℓ : ℕ) [NeZero ℓ]
    (data : ModularPolynomialData ℓ) (hsym : EvalSymm data.Φ) :
    data.Φ.eval₂ (aeval (R := ℤ) (jqNModC K ℓ)).toRingHom (jqModC K) = 0 := by
  have h0 : data.Φ.eval₂ (aeval (R := ℤ) (jqNModC ℚ ℓ)).toRingHom (jqModC ℚ) = 0 := by
    rw [jqNModC_rat, jqModC_rat, hsym (jqN ℓ) jq]
    exact data.eval_eq_zero
  have hZ : data.Φ.eval₂ (aeval (R := ℤ) (jqNModC ℤ ℓ)).toRingHom (jqModC ℤ) = 0 := by
    apply coeffMap_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
    rw [map_eval₂_aeval_toRingHom, coeffMap_jqNModC, coeffMap_jqModC, h0, map_zero]
  have := congrArg (coeffMap (Int.castRingHom K)) hZ
  rwa [map_eval₂_aeval_toRingHom, coeffMap_jqNModC, coeffMap_jqModC, map_zero] at this

theorem isIntegral_adjoin_of_eval₂_eq_zero (K : Type*) [Field K] (F : IntermediateField K (LaurentSeries K))
    (Φ : Polynomial (Polynomial ℤ)) (hΦ : Φ.Monic) (a b : ↥F)
    (h : Φ.eval₂ (aeval (R := ℤ) (a : LaurentSeries K)).toRingHom (b : LaurentSeries K) = 0) :
    IsIntegral (Algebra.adjoin K ({a} : Set ↥F)) b := by
  refine ⟨Φ.map (Polynomial.eval₂RingHom (Int.castRingHom _) ⟨a, Algebra.self_mem_adjoin_singleton K _⟩),
    hΦ.map _, ?_⟩
  apply (algebraMap ↥F (LaurentSeries K)).injective
  have hcomp : (algebraMap ↥F (LaurentSeries K)).comp
      ((algebraMap _ ↥F).comp
        (Polynomial.eval₂RingHom (Int.castRingHom _)
          (⟨a, Algebra.self_mem_adjoin_singleton K _⟩ : ↥(Algebra.adjoin K ({a} : Set ↥F))))) =
      (aeval (R := ℤ) (a : LaurentSeries K)).toRingHom := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, eval₂_X, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, aeval_X]
    rfl
  rw [eval₂_map, hom_eval₂, hcomp, map_zero]
  exact h

end CuspsLegsE4

namespace FltWs24
namespace DegPair

variable {k : Type*} [Field k] [IsAlgClosed k]

theorem isRational_C (N : ℕ) [NeZero N] (x : Place k ↥(modularFunctionFieldC k N)) : x.IsRational := by
  haveI := isCurveOver_modularFunctionFieldC_of_perfectField k N
  exact (Place.isRational_iff_deg_eq_one x).2 (IsCurveOver.deg_eq_one_of_isAlgClosed x)

theorem mem_iff_mem_restrictAlong {F F' : Type*} [Field F] [Field F'] [Algebra k F] [Algebra k F']
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral) (P : Place k F') (g : F) (hg : g ≠ 0)
    (he : 0 < Place.ramificationIndexAlong φ P) :
    φ g ∈ P.toValuationSubring ↔ g ∈ (P.restrictAlong φ hφ).toValuationSubring := by
  have hφg : φ g ≠ 0 := (map_ne_zero φ).mpr hg
  rw [Place.mem_iff_ord_nonneg _ hφg, Place.mem_iff_ord_nonneg _ hg, Place.ord_restrictAlong φ hφ P g]
  constructor
  · intro h
    by_contra hneg
    push Not at hneg
    have : (Place.ramificationIndexAlong φ P : ℤ) * (P.restrictAlong φ hφ).ord g < 0 :=
      mul_neg_of_pos_of_neg (by exact_mod_cast he) hneg
    omega
  · intro h
    exact mul_nonneg (by positivity) h

theorem evalAt_along (N : ℕ) [NeZero N] {F' : Type*} [Field F'] [Algebra k F']
    (φ : ↥(modularFunctionFieldC k N) →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral)
    (P : Place k F') (g : ↥(modularFunctionFieldC k N))
    (he : 0 < Place.ramificationIndexAlong φ P) :
    P.evalAt (φ g) = (P.restrictAlong φ hφ).evalAt g := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [map_zero, show (0 : F') = algebraMap k _ 0 from (map_zero _).symm,
      show (0 : ↥(modularFunctionFieldC k N)) = algebraMap k _ 0 from (map_zero _).symm,
      Place.evalAt_algebraMap, Place.evalAt_algebraMap]
  by_cases hmem : g ∈ (P.restrictAlong φ hφ).toValuationSubring
  · letI := AlgebraicCurve.algebraAlong φ
    haveI := AlgebraicCurve.isScalarTower_along φ
    haveI := AlgebraicCurve.isIntegral_along φ hφ
    exact Place.evalAt_algebraMap_eq_evalAt_restrict P (isRational_C N _) hmem
  · have hmem' : φ g ∉ P.toValuationSubring := fun h => hmem ((mem_iff_mem_restrictAlong φ hφ P g hg he).mp h)
    unfold Place.evalAt
    rw [dif_neg hmem', dif_neg hmem]

theorem rIA_pos {F F' : Type*} [Field F] [Field F'] [Algebra k F] [Algebra k F']
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral) (P : Place k F') :
    0 < Place.ramificationIndexAlong φ P := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI := AlgebraicCurve.isScalarTower_along φ
  haveI := AlgebraicCurve.isIntegral_along φ hφ
  exact P.ramificationIndex_pos (F := F)

omit [IsAlgClosed k] in
theorem isRoot_fibrePoly_evalAt (F : IntermediateField k (LaurentSeries k))
    (Φ : Polynomial (Polynomial ℤ)) (a b : ↥F)
    (h : Φ.eval₂ (aeval (R := ℤ) (a : LaurentSeries k)).toRingHom (b : LaurentSeries k) = 0)
    (v : Place k ↥F) (hv : v.IsRational) (ha : a ∈ v.toValuationSubring) (hb : b ∈ v.toValuationSubring) :
    (fibrePoly Φ (v.evalAt a)).IsRoot (v.evalAt b) := by
  have hF : Φ.eval₂ (aeval (R := ℤ) a).toRingHom b = 0 := by
    apply (algebraMap ↥F (LaurentSeries k)).injective
    rw [CuspsLegsE4.map_eval₂_aeval_toRingHom, map_zero]
    exact h
  have hO : Φ.eval₂ (aeval (R := ℤ) (⟨a, ha⟩ : ↥v.toValuationSubring)).toRingHom ⟨b, hb⟩ = 0 := by
    apply Subtype.val_injective
    have := CuspsLegsE4.map_eval₂_aeval_toRingHom (v.toValuationSubring.subtype) Φ ⟨a, ha⟩ ⟨b, hb⟩
    rw [ZeroMemClass.coe_zero]
    exact this.trans hF
  have hres := congrArg (IsLocalRing.residue ↥v.toValuationSubring) hO
  rw [CuspsLegsE4.map_eval₂_aeval_toRingHom, map_zero,
    ← v.algebraMap_evalAt hv ha, ← v.algebraMap_evalAt hv hb,
    ← CuspsLegsE4.map_eval₂_aeval_toRingHom, map_eq_zero] at hres
  unfold fibrePoly
  rw [IsRoot, eval_map]
  have hhom : Polynomial.eval₂RingHom (Int.castRingHom k) (v.evalAt a) = (aeval (R := ℤ) (v.evalAt a)).toRingHom := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp
  rw [hhom]
  exact hres

end FltWs24.DegPair

open FltWs24.DegPair in
theorem solution
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k] :
    haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
    ∀ (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k)
        = qExpand k s x),
    (∀ i, FiniteAlong k (φ i)) ∧
    (∀ i, SeparableAlong k (φ i)) ∧
    (∀ i, finrankAlong k (φ i) = s + 1) ∧
    (∀ (i : Fin 2) (p : Place k ↥(modularFunctionFieldC k (M * s))),
      p ∈ ssPlaces q' (M * s) k →
        Place.restrictAlong (φ i) (hφ i) p ∈ ssPlaces q' M k) ∧
    (∀ (i : Fin 2) (v : Place k ↥(modularFunctionFieldC k M)),
      v ∈ ssPlaces q' M k →
        ∀ p : Place k ↥(modularFunctionFieldC k (M * s)),
          Place.restrictAlong (φ i) (hφ i) p = v → p ∈ ssPlaces q' (M * s) k) := by
  haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
  haveI : Fact s.Prime := ⟨hs⟩
  intro φ hφ hφα hφβ
  obtain ⟨hfin, hsep, hpres0, hrefl0⟩ :=
    ModularCurve.degeneracyPair_finite_separable_identity_ssPlaces M s q' hs hsq' hq'M hsM (k := k) φ hφ hφα hφβ
  obtain ⟨hrank, hrat, haff, hj0, hj1⟩ :=
    ModularCurve.degeneracyPair_finrankAlong_and_place_transports M s q' hs hsq' hq'M hsM (k := k) φ hφ hφα hφβ
  obtain ⟨data, hsym⟩ := ModularCurve.exists_modularPolynomialData_evalSymm s
  have hmon : ∀ c : k, fibrePoly data.Φ c ≠ 0 := fun c => (data.monic.map _).ne_zero
  have hb_coe : ((jGeomGen k (M * s) : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = jqModC k := rfl
  have ha_coe : ((φ 1 (jGeomGen k M) : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = jqNModC k s := by rw [hφβ]; rfl
  have ha0 : φ 1 (jGeomGen k M) ≠ 0 := by
    intro h0
    have h1 : ((φ 1 (jGeomGen k M) : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = 0 := by rw [h0]; rfl
    rw [ha_coe] at h1
    exact transcendental_jqNModC k s (h1 ▸ isAlgebraic_zero)
  refine ⟨hfin, hsep, hrank, ?_, ?_⟩
  · intro i p hp
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · exact hpres0 p hp
    · obtain ⟨hprat, hpaff, hpj⟩ := hp
      refine ⟨(hrat 1 p).2 hprat, (haff 1 p).2 hpaff, ?_⟩
      have hroot := hj1 p hpaff data
      exact ModularCurve.mem_ssJSet_of_mem_roots_fibrePoly q' (ℓ := s) hsq' data hpj
        ((Polynomial.mem_roots (hmon _)).2 hroot)
  · intro i v hv p hpv
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · exact hrefl0 v hv p hpv
    · subst hpv
      obtain ⟨hvrat, hvaff, hvj⟩ := hv
      have hprat : p.IsRational := (hrat 1 p).1 hvrat
      have hpaff : IsAffineGeomPlace k (M * s) p := (haff 1 p).1 hvaff
      refine ⟨hprat, hpaff, ?_⟩
      have he := rIA_pos (φ 1) (hφ 1) p
      have ha : φ 1 (jGeomGen k M) ∈ p.toValuationSubring :=
        (mem_iff_mem_restrictAlong (φ 1) (hφ 1) p _ (fun h0 => ha0 (by rw [h0, map_zero])) he).2 hvaff.1
      have hroot := isRoot_fibrePoly_evalAt (modularFunctionFieldC k (M * s)) data.Φ (φ 1 (jGeomGen k M)) (jGeomGen k (M * s))
        (by rw [ha_coe, hb_coe]; exact CuspsLegsE4.eval₂_aeval_jqNModC_jqModC_eq_zero k s data hsym) p hprat ha hpaff.1
      rw [evalAt_along M (φ 1) (hφ 1) p (jGeomGen k M) he] at hroot
      exact ModularCurve.mem_ssJSet_of_mem_roots_fibrePoly q' (ℓ := s) hsq' data hvj
        ((Polynomial.mem_roots (hmon _)).2 hroot)

end S_ModularCurve_degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected
end P2MW
export P2MW.S_ModularCurve_degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected (solution)
