-- Prove2me | solution 1 for ModularCurve.CharPModel.finiteDimensional_adjoin_jLine
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/d065d740-9155-5b67-87a7-080fd5d574f8

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_PhiGen
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_finiteDimensional_adjoin_jLine
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq jqN evalAtJ ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange EvalSymm transcendental_coeffEmb_jq transcendental_jqModC"
p2m_open "ModularCurve~laurentMap_injective"
namespace CharPModel

section LaurentMap

variable {R S : Type*} [CommRing R] [CommRing S]

private def laurentMapRingHom (f : R →+* S) : LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map f
  map_one' := by
    ext g
    rw [HahnSeries.map_coeff, HahnSeries.coeff_one, HahnSeries.coeff_one, apply_ite f,
      map_one, map_zero]
  map_mul' x y := HahnSeries.map_mul f.toNonUnitalRingHom
  map_zero' := by
    ext g
    rw [HahnSeries.map_coeff, HahnSeries.coeff_zero, HahnSeries.coeff_zero, map_zero]
  map_add' x y := HahnSeries.map_add f.toAddMonoidHom

@[scoped simp]
private theorem laurentMapRingHom_apply (f : R →+* S) (x : LaurentSeries R) :
    laurentMapRingHom f x = x.map f := rfl

private theorem laurentMap_injective {f : R →+* S} (hf : Function.Injective f) {x y : LaurentSeries R}
    (h : x.map f = y.map f) : x = y := by
  ext g
  have hg := congrArg (fun z : LaurentSeries S => z.coeff g) h
  simpa only [HahnSeries.map_coeff] using hf hg

private theorem map_eval₂Bivar (Φ : Polynomial (Polynomial ℤ)) (f : R →+* S) (u v : LaurentSeries R) :
    (Φ.eval₂ (Polynomial.aeval (R := ℤ) u).toRingHom v).map f
      = Φ.eval₂ (Polynomial.aeval (R := ℤ) (u.map f)).toRingHom (v.map f) := by
  have hcomp : (laurentMapRingHom f).comp (Polynomial.aeval (R := ℤ) u).toRingHom
      = (Polynomial.aeval (R := ℤ) (u.map f)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [eq_intCast, map_intCast]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, Polynomial.aeval_X, laurentMapRingHom_apply]
  have h := Polynomial.hom_eval₂ Φ (Polynomial.aeval (R := ℤ) u).toRingHom
    (laurentMapRingHom f) v
  rw [← laurentMapRingHom_apply, h, hcomp, laurentMapRingHom_apply]

end LaurentMap

section FibreEval

variable {R S : Type*} [CommRing R] [CommRing S]

private theorem qExpand_map (N : ℕ) [NeZero N] (f : R →+* S) (x : LaurentSeries R) :
    (qExpand R N x).map f = qExpand S N (x.map f) := by
  ext k
  rw [HahnSeries.map_coeff]
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qExpand_coeff_mul, HahnSeries.map_coeff]
  · have h1 := qExpand_coeff_of_not_dvd (R := R) (N := N) x hk
    have h2 := qExpand_coeff_of_not_dvd (R := S) (N := N) (x.map f) hk
    rw [h1, h2, map_zero]

private theorem map_jqNModC (N : ℕ) [NeZero N] {K K' : Type*} [CommRing K] [CommRing K']
    (f : K →+* K') : (jqNModC K N).map f = jqNModC K' N := by
  show (qExpand K N (jqModC K)).map f = qExpand K' N (jqModC K')
  rw [qExpand_map, map_jqModC]

variable (N : ℕ) [NeZero N] (data : ModularPolynomialData N)

private theorem intEval_eq_zero :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqModC ℤ)).toRingHom (jqNModC ℤ N) = 0 := by
  refine laurentMap_injective (f := Int.castRingHom ℚ) (Int.castRingHom ℚ).injective_int ?_
  rw [map_eval₂Bivar, map_jqModC, map_jqNModC,
    show (0 : LaurentSeries ℤ).map (Int.castRingHom ℚ) = 0 from
      map_zero (laurentMapRingHom (Int.castRingHom ℚ))]
  exact data.eval_eq_zero

private theorem fibreEval_eq_zero (k : Type*) [CommRing k] :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqModC k)).toRingHom (jqNModC k N) = 0 := by
  have h := congrArg (fun x : LaurentSeries ℤ => x.map (Int.castRingHom k))
    (intEval_eq_zero N data)
  simpa only [map_eval₂Bivar, map_jqModC, map_jqNModC,
    show (0 : LaurentSeries ℤ).map (Int.castRingHom k) = 0 from
      map_zero (laurentMapRingHom (Int.castRingHom k))] using h

private theorem intEvalSwap_eq_zero (hsym : EvalSymm data.Φ) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqNModC ℤ N)).toRingHom (jqModC ℤ) = 0 := by
  refine laurentMap_injective (f := Int.castRingHom ℚ) (Int.castRingHom ℚ).injective_int ?_
  rw [map_eval₂Bivar, map_jqModC, map_jqNModC,
    show (0 : LaurentSeries ℤ).map (Int.castRingHom ℚ) = 0 from
      map_zero (laurentMapRingHom (Int.castRingHom ℚ))]
  rw [show jqModC ℚ = jq from rfl, show jqNModC ℚ N = jqN N from rfl]
  rw [hsym (jqN N) jq]
  exact data.eval_eq_zero

private theorem fibreEvalSwap_eq_zero (hsym : EvalSymm data.Φ) (k : Type*) [CommRing k] :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqNModC k N)).toRingHom (jqModC k) = 0 := by
  have h := congrArg (fun x : LaurentSeries ℤ => x.map (Int.castRingHom k))
    (intEvalSwap_eq_zero N data hsym)
  simpa only [map_eval₂Bivar, map_jqModC, map_jqNModC,
    show (0 : LaurentSeries ℤ).map (Int.castRingHom k) = 0 from
      map_zero (laurentMapRingHom (Int.castRingHom k))] using h

end FibreEval

end CharPModel
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_finiteDimensional_adjoin_jLine.ModularCurve.CharPModel"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_finiteDimensional_adjoin_jLine.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_finiteDimensional_adjoin_jLine.ModularCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq jqN evalAtJ ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange EvalSymm transcendental_coeffEmb_jq transcendental_jqModC"
p2m_open "ModularCurve~laurentMap_injective"
namespace CharPModel

section LineTier

private theorem transcendental_subtype {K L : Type*} [Field K] [Field L] [Algebra K L]
    (S : IntermediateField K L) {x : L} (hx : x ∈ S) (h : Transcendental K x) :
    Transcendental K (⟨x, hx⟩ : S) := by
  intro halg
  apply h
  obtain ⟨p, hp0, hp⟩ := halg
  refine ⟨p, hp0, ?_⟩
  have h2 := congrArg S.val hp
  rw [map_zero, ← Polynomial.aeval_algHom_apply] at h2
  simpa using h2

private def jBar (N : ℕ) [NeZero N] :
    laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionField_le_full N (jq_mem N))⟩

private def jNBar (N : ℕ) [NeZero N] :
    laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩

private theorem transcendental_jBar (N : ℕ) [NeZero N] :
    Transcendental (AlgebraicClosure ℚ) (jBar N) :=
  ModularCurve.transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N

private theorem transcendental_jC (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    Transcendental k (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) :=
  transcendental_subtype _ (jqModC_mem k N) (ModularCurve.transcendental_jqModC k)

private theorem fibreEval_subtype (k : Type*) [Field k] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ)
        (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)).toRingHom
      (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) = 0 := by
  have hcomp : ((modularFunctionFieldC k N).val.toRingHom).comp
      (Polynomial.aeval (R := ℤ)
        (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)).toRingHom
      = (Polynomial.aeval (R := ℤ) (jqModC k)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [eq_intCast, map_intCast]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, Polynomial.aeval_X]
      rfl
  have h := Polynomial.hom_eval₂ data.Φ
    (Polynomial.aeval (R := ℤ)
      (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)).toRingHom
    ((modularFunctionFieldC k N).val.toRingHom)
    (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N)
  apply Subtype.val_injective
  have h0 : (modularFunctionFieldC k N).val.toRingHom
      (data.Φ.eval₂ (Polynomial.aeval (R := ℤ)
          (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)).toRingHom
        (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N)) = 0 := by
    rw [h, hcomp]
    exact fibreEval_eq_zero N data k
  simpa using h0

private theorem adjoin_pair_subtype_eq_top {K L : Type*} [Field K] [Field L] [Algebra K L]
    (x y : L) :
    IntermediateField.adjoin K
        ({⟨x, IntermediateField.subset_adjoin K {x, y} (Set.mem_insert x {y})⟩,
          ⟨y, IntermediateField.subset_adjoin K {x, y} (Set.mem_insert_of_mem x rfl)⟩} :
          Set (IntermediateField.adjoin K ({x, y} : Set L))) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨z, hz⟩ -
  induction hz using IntermediateField.adjoin_induction with
  | mem z hzm =>
    rcases hzm with rfl | hzm
    · exact IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
    · rcases hzm with rfl
      exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)
  | algebraMap a => exact IntermediateField.algebraMap_mem _ a
  | add a b ha hb hia hib => exact add_mem hia hib
  | mul a b ha hb hia hib => exact mul_mem hia hib
  | inv a ha hia => exact inv_mem hia

private theorem isIntegral_adjoin_of_bivar_monic {K L : Type*} [Field K] [Field L] [Algebra K L]
    {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) {x y : L}
    (h : Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y = 0) :
    IsIntegral (IntermediateField.adjoin K ({x} : Set L)) y := by
  set g : Polynomial ℤ →+* IntermediateField.adjoin K ({x} : Set L) :=
    (Polynomial.aeval (R := ℤ)
      (⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ :
        IntermediateField.adjoin K ({x} : Set L))).toRingHom with hg
  have hcomp : (algebraMap (IntermediateField.adjoin K ({x} : Set L)) L).comp g
      = (Polynomial.aeval (R := ℤ) x).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [eq_intCast, map_intCast]
    · simp only [hg, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, Polynomial.aeval_X]
      rfl
  refine ⟨Φ.map g, hΦ.map g, ?_⟩
  rw [Polynomial.eval₂_map, hcomp]
  exact h

private theorem barEval_laurent (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ)
        (coeffEmb (AlgebraicClosure ℚ) jq)).toRingHom
      (coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq)) = 0 := by
  have hcomp : ((coeffEmb (AlgebraicClosure ℚ)).comp
      (Polynomial.aeval (R := ℤ) jq).toRingHom)
      = (Polynomial.aeval (R := ℤ) (coeffEmb (AlgebraicClosure ℚ) jq)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [eq_intCast, map_intCast]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, Polynomial.aeval_X]
  have h := Polynomial.hom_eval₂ data.Φ (Polynomial.aeval (R := ℤ) jq).toRingHom
    (coeffEmb (AlgebraicClosure ℚ)) (qExpand ℚ N jq)
  have h0 := data.eval_eq_zero
  rw [show evalAtJ = (Polynomial.aeval (R := ℤ) jq).toRingHom from rfl,
    show jqN N = qExpand ℚ N jq from rfl] at h0
  rw [h0, map_zero, hcomp] at h
  exact h.symm

private theorem barEval_subtype (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jBar N)).toRingHom (jNBar N) = 0 := by
  have hcomp : (((laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionFieldFull N)).val.toRingHom).comp
      (Polynomial.aeval (R := ℤ) (jBar N)).toRingHom)
      = (Polynomial.aeval (R := ℤ)
          (coeffEmb (AlgebraicClosure ℚ) jq)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [eq_intCast, map_intCast]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, Polynomial.aeval_X]
      rfl
  have h := Polynomial.hom_eval₂ data.Φ
    (Polynomial.aeval (R := ℤ) (jBar N)).toRingHom
    ((laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).val.toRingHom)
    (jNBar N)
  apply Subtype.val_injective
  have h0 : (laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionFieldFull N)).val.toRingHom
      (data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jBar N)).toRingHom (jNBar N)) = 0 := by
    rw [h, hcomp]
    exact barEval_laurent N data
  simpa using h0

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 800000 in

private theorem finiteDimensional_adjoin_jC (k : Type*) [Field k] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) :
    FiniteDimensional
      (IntermediateField.adjoin k
        ({⟨jqModC k, jqModC_mem k N⟩} : Set (modularFunctionFieldC k N)))
      (modularFunctionFieldC k N) := by
  have hint : IsIntegral
      (IntermediateField.adjoin k
        ({⟨jqModC k, jqModC_mem k N⟩} : Set (modularFunctionFieldC k N)))
      (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) :=
    isIntegral_adjoin_of_bivar_monic data.monic (fibreEval_subtype k N data)
  have htop := adjoin_pair_subtype_eq_top (K := k) (jqModC k) (jqNModC k N)
  have htower := IntermediateField.adjoin_adjoin_left k
    ({⟨jqModC k, jqModC_mem k N⟩} : Set (modularFunctionFieldC k N))
    {⟨jqNModC k N, jqNModC_mem k N⟩}
  rw [Set.singleton_union] at htower
  have hpair : IntermediateField.adjoin k
      ({⟨jqModC k, jqModC_mem k N⟩, ⟨jqNModC k N, jqNModC_mem k N⟩} :
        Set (modularFunctionFieldC k N)) = ⊤ := htop
  rw [hpair] at htower
  have hFD : FiniteDimensional
      (IntermediateField.adjoin k
        ({⟨jqModC k, jqModC_mem k N⟩} : Set (modularFunctionFieldC k N)))
      (IntermediateField.adjoin
        (IntermediateField.adjoin k
          ({⟨jqModC k, jqModC_mem k N⟩} : Set (modularFunctionFieldC k N)))
        ({⟨jqNModC k N, jqNModC_mem k N⟩} : Set (modularFunctionFieldC k N))) :=
    IntermediateField.adjoin.finiteDimensional hint
  have h2 : IntermediateField.adjoin
      (IntermediateField.adjoin k
        ({⟨jqModC k, jqModC_mem k N⟩} : Set (modularFunctionFieldC k N)))
      ({⟨jqNModC k N, jqNModC_mem k N⟩} : Set (modularFunctionFieldC k N)) = ⊤ :=
    IntermediateField.restrictScalars_injective k
      (htower.trans IntermediateField.restrictScalars_top.symm)
  rw [h2] at hFD
  exact (IntermediateField.topEquiv (F := IntermediateField.adjoin k
    ({⟨jqModC k, jqModC_mem k N⟩} : Set (modularFunctionFieldC k N)))).toLinearEquiv.finiteDimensional

private theorem algebraMap_comp_aeval_adjoin_self {K L : Type*} [Field K] [Field L] [Algebra K L]
    (x : L) :
    (algebraMap (IntermediateField.adjoin K ({x} : Set L)) L).comp
      (Polynomial.aeval (R := ℤ)
        (IntermediateField.AdjoinSimple.gen K x)).toRingHom
      = (Polynomial.aeval (R := ℤ) x).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a
    simp only [eq_intCast, map_intCast]
  · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, Polynomial.aeval_X]
    rfl

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private def jLine (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    modularFunctionFieldC k N := ⟨jqModC k, jqModC_mem k N⟩

set_option synthInstance.maxHeartbeats 1600000 in
private def jNLine (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    modularFunctionFieldC k N := ⟨jqNModC k N, jqNModC_mem k N⟩

private theorem transcendental_jLine (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    Transcendental k (jLine k N) := transcendental_jC k N

set_option synthInstance.maxHeartbeats 1600000 in

private noncomputable def lineEquivC (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    RatFunc k ≃ₐ[k]
      (IntermediateField.adjoin k
        ({jLine k N} : Set (modularFunctionFieldC k N))) :=
  RatFunc.algEquivOfTranscendental _ (transcendental_jLine k N)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem lineEquivC_algebraMap (k : Type*) [Field k] (N : ℕ) [NeZero N]
    (g : Polynomial k) :
    lineEquivC k N (algebraMap (Polynomial k) (RatFunc k) g)
      = Polynomial.aeval
          (IntermediateField.AdjoinSimple.gen k (jLine k N)) g :=
  RatFunc.algEquivOfTranscendental_algebraMap _ (transcendental_jLine k N) g

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem lineX (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    lineEquivC k N (algebraMap (Polynomial k) (RatFunc k) Polynomial.X)
      = IntermediateField.AdjoinSimple.gen k (jLine k N) := by
  rw [lineEquivC_algebraMap, Polynomial.aeval_X]

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem lineConst (k : Type*) [Field k] (N : ℕ) [NeZero N] (a : ℤ) :
    Polynomial.aeval (R := ℤ)
      (IntermediateField.AdjoinSimple.gen k (jLine k N)) (Polynomial.C a)
      = lineEquivC k N (algebraMap (Polynomial k) (RatFunc k)
          ((Polynomial.C a).map (Int.castRingHom k))) := by
  rw [Polynomial.aeval_C, Polynomial.map_C,
    show Polynomial.C ((Int.castRingHom k) a)
        = algebraMap k (Polynomial k) ((Int.castRingHom k) a) from rfl,
    ← IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k),
    AlgEquiv.commutes]
  simp only [eq_intCast, map_intCast]

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem lineFun (k : Type*) [Field k] (N : ℕ) [NeZero N] (p : Polynomial ℤ) :
    Polynomial.aeval (R := ℤ)
      (IntermediateField.AdjoinSimple.gen k (jLine k N)) p
      = lineEquivC k N (algebraMap (Polynomial k) (RatFunc k)
          (p.map (Int.castRingHom k))) := by
  induction p using Polynomial.induction_on with
  | C a => exact lineConst k N a
  | add p q hp hq =>
    rw [Polynomial.map_add, map_add, map_add, map_add, hp, hq]
  | monomial n a _ =>
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, map_mul,
      map_pow, lineX, Polynomial.aeval_X]
    rw [lineConst k N a]

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem lineMapEq (k : Type*) [Field k] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) :
    data.Φ.map
      ((Polynomial.aeval (R := ℤ)
        (IntermediateField.AdjoinSimple.gen k (jLine k N))).toRingHom)
      = ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map
          (algebraMap (Polynomial k) (RatFunc k))).map
        (lineEquivC k N).toAlgHom.toRingHom := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_map, Polynomial.coeff_map, Polynomial.coeff_map,
    Polynomial.coeff_map]
  exact lineFun k N (data.Φ.coeff n)

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem linePsep (k : Type*) [Field k] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N)
    (hsep : ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable) :
    (data.Φ.map
      ((Polynomial.aeval (R := ℤ)
        (IntermediateField.AdjoinSimple.gen k (jLine k N))).toRingHom)).Separable := by
  rw [lineMapEq k N data]
  exact hsep.map

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem lineAevalZero (k : Type*) [Field k] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) :
    Polynomial.aeval
      (R := IntermediateField.adjoin k
        ({jLine k N} : Set (modularFunctionFieldC k N)))
      (jNLine k N)
      (data.Φ.map
        ((Polynomial.aeval (R := ℤ)
          (IntermediateField.AdjoinSimple.gen k (jLine k N))).toRingHom)) = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map,
    algebraMap_comp_aeval_adjoin_self (jLine k N)]
  exact fibreEval_subtype k N data

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem lineDvd (k : Type*) [Field k] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) :
    minpoly
      (IntermediateField.adjoin k
        ({jLine k N} : Set (modularFunctionFieldC k N)))
      (jNLine k N)
      ∣ data.Φ.map
        ((Polynomial.aeval (R := ℤ)
          (IntermediateField.AdjoinSimple.gen k (jLine k N))).toRingHom) :=
  minpoly.dvd
    (IntermediateField.adjoin k
      ({jLine k N} : Set (modularFunctionFieldC k N)))
    (jNLine k N)
    (lineAevalZero k N data)

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem isSeparable_jNC (k : Type*) [Field k] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N)
    (hsep : ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable) :
    IsSeparable
      (IntermediateField.adjoin k
        ({⟨jqModC k, jqModC_mem k N⟩} : Set (modularFunctionFieldC k N)))
      (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) :=
  (linePsep k N data hsep).of_dvd (lineDvd k N data)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem isSeparable_line_fibre (k : Type*) [Field k] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N)
    (hsep : ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable) :
    Algebra.IsSeparable
      (IntermediateField.adjoin k
        ({⟨jqModC k, jqModC_mem k N⟩} : Set (modularFunctionFieldC k N)))
      (modularFunctionFieldC k N) := by
  have hadj : Algebra.IsSeparable
      (IntermediateField.adjoin k
        ({⟨jqModC k, jqModC_mem k N⟩} : Set (modularFunctionFieldC k N)))
      (IntermediateField.adjoin
        (IntermediateField.adjoin k
          ({⟨jqModC k, jqModC_mem k N⟩} : Set (modularFunctionFieldC k N)))
        ({⟨jqNModC k N, jqNModC_mem k N⟩} : Set (modularFunctionFieldC k N))) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).mpr
      (isSeparable_jNC k N data hsep)
  have htower := IntermediateField.adjoin_adjoin_left k
    ({⟨jqModC k, jqModC_mem k N⟩} : Set (modularFunctionFieldC k N))
    {⟨jqNModC k N, jqNModC_mem k N⟩}
  rw [Set.singleton_union] at htower
  have hpair : IntermediateField.adjoin k
      ({⟨jqModC k, jqModC_mem k N⟩, ⟨jqNModC k N, jqNModC_mem k N⟩} :
        Set (modularFunctionFieldC k N)) = ⊤ :=
    adjoin_pair_subtype_eq_top (K := k) (jqModC k) (jqNModC k N)
  rw [hpair] at htower
  have h2 : IntermediateField.adjoin
      (IntermediateField.adjoin k
        ({⟨jqModC k, jqModC_mem k N⟩} : Set (modularFunctionFieldC k N)))
      ({⟨jqNModC k N, jqNModC_mem k N⟩} : Set (modularFunctionFieldC k N)) = ⊤ :=
    IntermediateField.restrictScalars_injective k
      (htower.trans IntermediateField.restrictScalars_top.symm)
  rw [h2] at hadj
  haveI := hadj
  exact AlgEquiv.Algebra.isSeparable IntermediateField.topEquiv

end LineTier
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_finiteDimensional_adjoin_jLine.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_finiteDimensional_adjoin_jLine.ModularCurve"

end CharPModel
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_finiteDimensional_adjoin_jLine.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_finiteDimensional_adjoin_jLine.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_finiteDimensional_adjoin_jLine.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_finiteDimensional_adjoin_jLine.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_finiteDimensional_adjoin_jLine.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_finiteDimensional_adjoin_jLine.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_finiteDimensional_adjoin_jLine.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_finiteDimensional_adjoin_jLine.ModularCurve"

p2m_open "ModularCurve~laurentMap_injective" in open _root_.P2MW.S_ModularCurve_CharPModel_finiteDimensional_adjoin_jLine.ModularCurve ModularCurve.CharPModel AlgebraicCurve in
set_option maxHeartbeats 3200000 in
theorem solution (k : Type*) [Field k]
    (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N) :
    FiniteDimensional
      (IntermediateField.adjoin k
        ({⟨jqModC k, jqModC_mem k N⟩} : Set (modularFunctionFieldC k N)))
      (modularFunctionFieldC k N) :=
  ModularCurve.CharPModel.finiteDimensional_adjoin_jC k N data

end S_ModularCurve_CharPModel_finiteDimensional_adjoin_jLine
end P2MW
export P2MW.S_ModularCurve_CharPModel_finiteDimensional_adjoin_jLine (solution)
