-- Prove2me | solution 1 for ModularCurve.CharPModel.chart_dichotomy_jBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/e73d1db1-965b-5b46-9445-43023196a7dd

import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_AlgebraicCurve_Place_finite_residueField_of_finiteDimensional
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

p2m_open "ModularCurve~laurentMap_injective P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve.CharPModel"
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.AlgebraicCurve"
open Polynomial
open IsLocalRing
open IsDedekindDomain

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "CharPModel.jBar jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq jqN evalAtJ ModularPolynomialData divisorExpansions mem_divisorExpansions modularFunctionFieldFull jqd_mem_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange EvalSymm transcendental_coeffEmb_jq transcendental_jqModC"
p2m_open "ModularCurve~laurentMap_injective"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar jNBar"
p2m_open "ModularCurve.CharPModel"

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
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve.CharPModel"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "CharPModel.jBar jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq jqN evalAtJ ModularPolynomialData divisorExpansions mem_divisorExpansions modularFunctionFieldFull jqd_mem_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange EvalSymm transcendental_coeffEmb_jq transcendental_jqModC"
p2m_open "ModularCurve~laurentMap_injective"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar jNBar"
p2m_open "ModularCurve.CharPModel"

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

end LineTier
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve"
end CharPModel
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "CharPModel.jBar jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq jqN evalAtJ ModularPolynomialData divisorExpansions mem_divisorExpansions modularFunctionFieldFull jqd_mem_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange EvalSymm transcendental_coeffEmb_jq transcendental_jqModC"
p2m_open "ModularCurve~laurentMap_injective"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar jNBar"
p2m_open "ModularCurve.CharPModel"

section BarFinDim

private def jdBar (N : ℕ) [NeZero N] (d : ℕ) [NeZero d] (hd : d ∣ N) :
    laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N hd)⟩

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem barEvalD_subtype (N : ℕ) [NeZero N] (d : ℕ) [NeZero d] (hd : d ∣ N)
    (data : ModularPolynomialData d) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jBar N)).toRingHom (jdBar N d hd) = 0 := by
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
    (jdBar N d hd)
  apply Subtype.val_injective
  have h0 : (laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionFieldFull N)).val.toRingHom
      (data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jBar N)).toRingHom (jdBar N d hd)) = 0 := by
    rw [h, hcomp]
    exact barEval_laurent d data
  simpa using h0

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem lbc_eq_adjoin_divisors (N : ℕ) [NeZero N] :
    laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)
      = IntermediateField.adjoin (AlgebraicClosure ℚ)
          (⇑(coeffEmb (AlgebraicClosure ℚ)) '' divisorExpansions N) := by
  refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_)
    (IntermediateField.adjoin_le_iff.mpr ?_)
  · rintro x ⟨y, hy, rfl⟩
    have hy' : y ∈ IntermediateField.adjoin ℚ (divisorExpansions N) := hy
    induction hy' using IntermediateField.adjoin_induction with
    | mem z hz =>
      exact IntermediateField.subset_adjoin _ _ ⟨z, hz, rfl⟩
    | algebraMap a =>
      rw [eq_ratCast, map_ratCast]
      simp
    | add a b ha hb hia hib =>
      rw [map_add]; exact add_mem (hia ha) (hib hb)
    | mul a b ha hb hia hib =>
      rw [map_mul]; exact mul_mem (hia ha) (hib hb)
    | inv a ha hia =>
      rw [map_inv₀]; exact inv_mem (hia ha)
  · rintro x ⟨y, hy, rfl⟩
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (IntermediateField.subset_adjoin ℚ _ hy)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem adjoin_val_preimage_eq_top {K L : Type*} [Field K] [Field L] [Algebra K L]
    {F : IntermediateField K L} {S : Set L} (hF : F = IntermediateField.adjoin K S) :
    IntermediateField.adjoin K (Subtype.val ⁻¹' S : Set F) = ⊤ := by
  subst hF
  rw [eq_top_iff]
  rintro ⟨z, hz⟩ -
  induction hz using IntermediateField.adjoin_induction with
  | mem w hw => exact IntermediateField.subset_adjoin _ _ hw
  | algebraMap a => exact IntermediateField.algebraMap_mem _ a
  | add a b ha hb hia hib => exact add_mem hia hib
  | mul a b ha hb hia hib => exact mul_mem hia hib
  | inv a ha hia => exact inv_mem hia

private def barGenSet (N : ℕ) [NeZero N] :
    Set (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :=
  Subtype.val ⁻¹' (⇑(coeffEmb (AlgebraicClosure ℚ)) '' divisorExpansions N)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem adjoin_barGenSet_eq_top (N : ℕ) [NeZero N] :
    IntermediateField.adjoin (AlgebraicClosure ℚ) (barGenSet N) = ⊤ :=
  adjoin_val_preimage_eq_top (lbc_eq_adjoin_divisors N)

private theorem barGenSet_finite (N : ℕ) [NeZero N] : (barGenSet N).Finite := by
  apply Set.Finite.preimage Subtype.val_injective.injOn
  apply Set.Finite.image
  have hsub : divisorExpansions N ⊆
      (fun d : {d // d ∈ N.divisors} =>
        @qExpand ℚ _ d.1 ⟨(Nat.pos_of_mem_divisors d.2).ne'⟩ jq) '' Set.univ := by
    rintro x ⟨d, hne, hd, hx⟩
    haveI := hne
    exact ⟨⟨d, Nat.mem_divisors.mpr ⟨hd, NeZero.ne N⟩⟩, Set.mem_univ _, hx.symm⟩
  exact ((Set.finite_univ (α := {d // d ∈ N.divisors})).image _).subset hsub

private theorem jBar_mem_barGenSet (N : ℕ) [NeZero N] : jBar N ∈ barGenSet N :=
  ⟨qExpand ℚ 1 jq, mem_divisorExpansions N (one_dvd N), by rw [qExpand_one_apply]; rfl⟩

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem barGenSet_integral (N : ℕ) [NeZero N]
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d) :
    ∀ x ∈ barGenSet N,
      IsIntegral (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jBar N} : Set (laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionFieldFull N)))) x := by
  rintro ⟨xv, hxF⟩ hx
  obtain ⟨y, hy, hxy⟩ := hx
  obtain ⟨d, hdne, hd, rfl⟩ := hy
  haveI := hdne
  have hxel : (⟨xv, hxF⟩ : laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionFieldFull N)) = jdBar N d hd := Subtype.ext hxy.symm
  rw [hxel]
  exact isIntegral_adjoin_of_bivar_monic (dataAll d hd).monic
    (barEvalD_subtype N d hd (dataAll d hd))

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem finiteDimensional_lineBar_of_dataAll (N : ℕ) [NeZero N]
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d) :
    FiniteDimensional
      (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jBar N} : Set (laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionFieldFull N))))
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) := by
  haveI : Finite ↥(barGenSet N) := (barGenSet_finite N).to_subtype
  have hint := barGenSet_integral N dataAll
  have htower := IntermediateField.adjoin_adjoin_left (AlgebraicClosure ℚ)
    ({jBar N} : Set (laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionFieldFull N))) (barGenSet N)
  rw [Set.singleton_union, Set.insert_eq_self.mpr (jBar_mem_barGenSet N),
    adjoin_barGenSet_eq_top N] at htower
  have h2 : IntermediateField.adjoin
      (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jBar N} : Set (laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionFieldFull N))))
      (barGenSet N) = ⊤ :=
    IntermediateField.restrictScalars_injective (AlgebraicClosure ℚ)
      (htower.trans IntermediateField.restrictScalars_top.symm)
  have hFD : FiniteDimensional
      (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jBar N} : Set (laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionFieldFull N))))
      (IntermediateField.adjoin
        (IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({jBar N} : Set (laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionFieldFull N))))
        (barGenSet N)) :=
    IntermediateField.finiteDimensional_adjoin hint
  rw [h2] at hFD
  exact (IntermediateField.topEquiv (F := IntermediateField.adjoin (AlgebraicClosure ℚ)
    ({jBar N} : Set (laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionFieldFull N))))).toLinearEquiv.finiteDimensional

end BarFinDim
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve"

end CharPModel
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve"

noncomputable section

open IsLocalRing

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_inv Place.finite_residueField_of_finiteDimensional"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg FiniteResidue ord ord_inv exists_unit_mul_zpow ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mem_maximalIdeal_iff_ord_pos restrict finite_residueField_of_finiteDimensional mem_of_ord_nonneg"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

private theorem _root_.AlgebraicCurve.Place.algebraMap_mem (a : K) : algebraMap K F a ∈ w.toValuationSubring := w.algebraMap_mem' a

p2m_export "AlgebraicCurve.Place" "algebraMap_mem"

private theorem _root_.AlgebraicCurve.Place.algebraMap_mem_nonunits_iff (a : K) :
    algebraMap K F a ∈ w.toValuationSubring.nonunits ↔ a = 0 := by
  constructor
  · intro h
    rcases (ValuationSubring.mem_nonunits_iff_or _).mp h with h0 | hinv
    · exact (map_eq_zero _).mp h0
    · exact absurd (by simpa using w.algebraMap_mem a⁻¹) hinv
  · rintro rfl
    simp [ZeroMemClass.zero_mem]

p2m_export "AlgebraicCurve.Place" "algebraMap_mem_nonunits_iff"

private theorem _root_.AlgebraicCurve.Place.mul_mem_nonunits {x y : F} (hx : x ∈ w.toValuationSubring.nonunits)
    (hy : y ∈ w.toValuationSubring) : x * y ∈ w.toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hx ⊢
  rw [← ValuationSubring.valuation_le_one_iff] at hy
  calc w.toValuationSubring.valuation (x * y)
      = w.toValuationSubring.valuation x * w.toValuationSubring.valuation y := map_mul _ _ _
    _ ≤ w.toValuationSubring.valuation x * 1 := by gcongr
    _ = w.toValuationSubring.valuation x := mul_one _
    _ < 1 := hx

p2m_export "AlgebraicCurve.Place" "mul_mem_nonunits"

private theorem _root_.AlgebraicCurve.Place.mem_of_ord_pos {f : F} (h : 0 < w.ord f) : f ∈ w.toValuationSubring := by
  have hf : f ≠ 0 := by rintro rfl; simp at h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf hπ
  rw [hu, show w.ord f = (((w.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h.le).symm,
    zpow_natCast]
  exact mul_mem (u : w.toValuationSubring).2 (pow_mem (π : w.toValuationSubring).2 _)

p2m_export "AlgebraicCurve.Place" "mem_of_ord_pos"

private theorem _root_.AlgebraicCurve.Place.mem_nonunits_iff_ord_pos {f : F} (hf : f ≠ 0) :
    f ∈ w.toValuationSubring.nonunits ↔ 0 < w.ord f := by
  constructor
  · intro h
    have hmem : f ∈ w.toValuationSubring := w.toValuationSubring.nonunits_subset h
    have h' : ((⟨f, hmem⟩ : w.toValuationSubring) : F) ∈ w.toValuationSubring.nonunits := h
    rw [ValuationSubring.coe_mem_nonunits_iff] at h'
    exact (w.mem_maximalIdeal_iff_ord_pos hf hmem).mp h'
  · intro h
    have hmem : f ∈ w.toValuationSubring := w.mem_of_ord_pos h
    have h' := (w.mem_maximalIdeal_iff_ord_pos hf hmem).mpr h
    rw [← ValuationSubring.coe_mem_nonunits_iff] at h'
    exact h'

p2m_export "AlgebraicCurve.Place" "mem_nonunits_iff_ord_pos"

private def _root_.AlgebraicCurve.Place.HasValueAt (f : F) (a : K) : Prop :=
  f - algebraMap K F a ∈ w.toValuationSubring.nonunits

p2m_export "AlgebraicCurve.Place" "HasValueAt"
private theorem hasValueAt_iff (f : F) (a : K) :
    w.HasValueAt f a ↔ f - algebraMap K F a ∈ w.toValuationSubring.nonunits := Iff.rfl

private theorem _root_.AlgebraicCurve.Place.hasValueAt_iff_ord_pos {f : F} {a : K} (h : f ≠ algebraMap K F a) :
    w.HasValueAt f a ↔ 0 < w.ord (f - algebraMap K F a) :=
  w.mem_nonunits_iff_ord_pos (sub_ne_zero.mpr h)

p2m_export "AlgebraicCurve.Place" "hasValueAt_iff_ord_pos"
private theorem hasValueAt_of_ord_pos {f : F} {a : K} (h : 0 < w.ord (f - algebraMap K F a)) :
    w.HasValueAt f a := by
  have hne : f ≠ algebraMap K F a := by
    intro hfa; rw [hfa, sub_self] at h; simp at h
  exact (w.hasValueAt_iff_ord_pos hne).mpr h

private theorem _root_.AlgebraicCurve.Place.hasValueAt_algebraMap (a : K) : w.HasValueAt (algebraMap K F a) a := by
  simp [HasValueAt, ZeroMemClass.zero_mem]

p2m_export "AlgebraicCurve.Place" "hasValueAt_algebraMap"

private theorem _root_.AlgebraicCurve.Place.hasValueAt_zero_iff (f : F) : w.HasValueAt f 0 ↔ f ∈ w.toValuationSubring.nonunits := by
  simp [HasValueAt]

p2m_export "AlgebraicCurve.Place" "hasValueAt_zero_iff"

private theorem _root_.AlgebraicCurve.Place.mem_of_hasValueAt {f : F} {a : K} (h : w.HasValueAt f a) : f ∈ w.toValuationSubring := by
  have h1 : f - algebraMap K F a ∈ w.toValuationSubring := w.toValuationSubring.nonunits_subset h
  simpa using add_mem h1 (w.algebraMap_mem a)

p2m_export "AlgebraicCurve.Place" "mem_of_hasValueAt"
namespace HasValueAt
variable {w} in

private theorem _root_.AlgebraicCurve.Place.HasValueAt.unique {f : F} {a b : K} (ha : w.HasValueAt f a) (hb : w.HasValueAt f b) :
    a = b := by
  have h : algebraMap K F (a - b) ∈ w.toValuationSubring.nonunits := by
    have := sub_mem hb ha
    rwa [sub_sub_sub_cancel_left, ← map_sub] at this
  exact sub_eq_zero.mp ((w.algebraMap_mem_nonunits_iff _).mp h)

end HasValueAt
p2m_export "AlgebraicCurve.Place" "HasValueAt.unique"
namespace HasValueAt
variable {w} in
private theorem _root_.AlgebraicCurve.Place.HasValueAt.add {f g : F} {a b : K} (hf : w.HasValueAt f a) (hg : w.HasValueAt g b) :
    w.HasValueAt (f + g) (a + b) := by
  have := add_mem hf hg
  rw [HasValueAt, map_add]
  convert this using 1
  ring

end HasValueAt
p2m_export "AlgebraicCurve.Place" "HasValueAt.add"
namespace HasValueAt
variable {w} in
private theorem _root_.AlgebraicCurve.Place.HasValueAt.neg {f : F} {a : K} (hf : w.HasValueAt f a) : w.HasValueAt (-f) (-a) := by
  have := neg_mem hf
  rw [HasValueAt, map_neg]
  convert this using 1
  ring

end HasValueAt
p2m_export "AlgebraicCurve.Place" "HasValueAt.neg"
namespace HasValueAt
variable {w} in
private theorem _root_.AlgebraicCurve.Place.HasValueAt.mul {f g : F} {a b : K} (hf : w.HasValueAt f a) (hg : w.HasValueAt g b) :
    w.HasValueAt (f * g) (a * b) := by
  have h1 : (f - algebraMap K F a) * g ∈ w.toValuationSubring.nonunits :=
    w.mul_mem_nonunits hf (w.mem_of_hasValueAt hg)
  have h2 : (g - algebraMap K F b) * algebraMap K F a ∈ w.toValuationSubring.nonunits :=
    w.mul_mem_nonunits hg (w.algebraMap_mem a)
  have := add_mem h1 h2
  rw [HasValueAt, map_mul]
  convert this using 1
  ring

end HasValueAt
p2m_export "AlgebraicCurve.Place" "HasValueAt.mul"
namespace HasValueAt
variable {w} in

private theorem _root_.AlgebraicCurve.Place.HasValueAt.inv {f : F} {a : K} (hf : w.HasValueAt f a) (ha : a ≠ 0) :
    w.HasValueAt f⁻¹ a⁻¹ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    have : w.HasValueAt (0 : F) 0 := by simpa using w.hasValueAt_algebraMap 0
    exact ha (hf.unique this)
  have hfu : f ∉ w.toValuationSubring.nonunits := fun hfn =>
    ha (hf.unique ((w.hasValueAt_zero_iff f).mpr hfn))
  have hfinv : f⁻¹ ∈ w.toValuationSubring := by
    by_contra hne
    exact hfu ((ValuationSubring.mem_nonunits_iff_or _).mpr (Or.inr (by simpa using hne)))
  have hprod : (f - algebraMap K F a) * (f⁻¹ * algebraMap K F a⁻¹)
      ∈ w.toValuationSubring.nonunits :=
    w.mul_mem_nonunits hf (mul_mem hfinv (w.algebraMap_mem _))
  have := neg_mem hprod
  change f⁻¹ - algebraMap K F a⁻¹ ∈ w.toValuationSubring.nonunits
  convert this using 1
  have haF : algebraMap K F a ≠ 0 := by simpa using ha
  rw [map_inv₀]
  field_simp
  ring

end HasValueAt
p2m_export "AlgebraicCurve.Place" "HasValueAt.inv"
namespace HasValueAt
variable {w} in

private theorem _root_.AlgebraicCurve.Place.HasValueAt.div {f g : F} {a b : K} (hf : w.HasValueAt f a) (hg : w.HasValueAt g b)
    (hb : b ≠ 0) : w.HasValueAt (f / g) (a / b) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact hf.mul (hg.inv hb)

end HasValueAt
p2m_export "AlgebraicCurve.Place" "HasValueAt.div"

private theorem _root_.AlgebraicCurve.Place.hasValueAt_iff_residue {f : F} (hf : f ∈ w.toValuationSubring) (a : K) :
    w.HasValueAt f a ↔
      residue w.toValuationSubring ⟨f, hf⟩ = algebraMap K w.ResidueField a := by
  have e : algebraMap K w.ResidueField a =
      residue w.toValuationSubring (algebraMap K w.toValuationSubring a) := rfl
  rw [e, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

p2m_export "AlgebraicCurve.Place" "hasValueAt_iff_residue"

private theorem exists_hasValueAt (hw : Function.Surjective (algebraMap K w.ResidueField)) {f : F}
    (hf : f ∈ w.toValuationSubring) : ∃ a : K, w.HasValueAt f a := by
  obtain ⟨a, ha⟩ := hw (residue w.toValuationSubring ⟨f, hf⟩)
  exact ⟨a, (w.hasValueAt_iff_residue hf a).mpr ha.symm⟩

private theorem _root_.AlgebraicCurve.Place.surjective_algebraMap_residueField_of_isAlgClosed [IsAlgClosed K]
    [Module.Finite K w.ResidueField] : Function.Surjective (algebraMap K w.ResidueField) :=
  haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K w.ResidueField
  (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := w.ResidueField)).2

p2m_export "AlgebraicCurve.Place" "surjective_algebraMap_residueField_of_isAlgClosed"

private theorem surjective_algebraMap_residueField_of_deg_eq_one [IsAlgClosed K] (h : w.deg = 1) :
    Function.Surjective (algebraMap K w.ResidueField) :=
  haveI : Module.Finite K w.ResidueField := Module.finite_of_finrank_eq_succ (n := 0) h
  w.surjective_algebraMap_residueField_of_isAlgClosed

end Place
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve"
end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve"
end
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve"

namespace ValuationSubring
p2m_export "ValuationSubring" "comap subtype valuation_eq_iff coe_mem_nonunits_iff mem_comap neg_mem toSubring algebraMap_apply ext mem_nonunits_iff_or zero_mem nonunits mem_nonunits_iff mem_top eq_of_le_of_ne_top mul_mem mem_or_inv_mem nonunits_subset add_mem eq_top_iff valuation_le_one_iff algebra valuation"
p2m_open "ValuationSubring"

variable {F : Type*} [Field F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable (O : ValuationSubring F)

private def _root_.ValuationSubring.centreOver (hO : ∀ r : R, algebraMap R F r ∈ O) : Ideal R :=
  (IsLocalRing.maximalIdeal O).comap ((algebraMap R F).codRestrict O.toSubring hO)

p2m_export "ValuationSubring" "centreOver"
private scoped instance centreOver_isPrime (hO : ∀ r : R, algebraMap R F r ∈ O) : (O.centreOver hO).IsPrime :=
  Ideal.comap_isPrime _ _

omit [IsDedekindDomain R] [IsFractionRing R F] in
private theorem _root_.ValuationSubring.mem_centreOver_iff (hO : ∀ r : R, algebraMap R F r ∈ O) {r : R} :
    r ∈ O.centreOver hO ↔ algebraMap R F r ∈ O.nonunits := by
  rw [centreOver, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

p2m_export "ValuationSubring" "mem_centreOver_iff"
omit [IsDedekindDomain R] [IsFractionRing R F] in
private theorem _root_.ValuationSubring.inv_algebraMap_mem (hO : ∀ r : R, algebraMap R F r ∈ O) {s : R}
    (hs : s ∉ O.centreOver hO) : (algebraMap R F s)⁻¹ ∈ O := by
  rw [mem_centreOver_iff, ValuationSubring.mem_nonunits_iff, not_lt] at hs
  have hy : O.valuation (algebraMap R F s) ≤ 1 := (O.valuation_le_one_iff _).mpr (hO s)
  have h1 : O.valuation (algebraMap R F s) = 1 := le_antisymm hy hs
  apply (O.valuation_le_one_iff _).mp
  rw [map_inv₀, h1, inv_one]

p2m_export "ValuationSubring" "inv_algebraMap_mem"

private theorem _root_.ValuationSubring.centreOver_ne_bot (hO : ∀ r : R, algebraMap R F r ∈ O) (hne : O ≠ ⊤) :
    O.centreOver hO ≠ ⊥ := by
  intro hbot
  apply hne
  refine SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  rw [div_eq_mul_inv]
  refine O.mul_mem _ _ (hO a) (O.inv_algebraMap_mem hO fun hmem => ?_)
  rw [hbot, Ideal.mem_bot] at hmem
  exact nonZeroDivisors.ne_zero hb hmem

p2m_export "ValuationSubring" "centreOver_ne_bot"

private def _root_.ValuationSubring.centreHeightOneSpectrum (hO : ∀ r : R, algebraMap R F r ∈ O) (hne : O ≠ ⊤) :
    HeightOneSpectrum R :=
  ⟨O.centreOver hO, inferInstance, O.centreOver_ne_bot hO hne⟩

p2m_export "ValuationSubring" "centreHeightOneSpectrum"

private theorem _root_.ValuationSubring.valuationSubringAtPrime_centre_le (hO : ∀ r : R, algebraMap R F r ∈ O) (hne : O ≠ ⊤) :
    HeightOneSpectrum.valuationSubringAtPrime F (O.centreHeightOneSpectrum hO hne) ≤ O := by
  rintro x ⟨a, s, hs, rfl⟩
  exact O.mul_mem _ _ (hO a) (O.inv_algebraMap_mem hO hs)

p2m_export "ValuationSubring" "valuationSubringAtPrime_centre_le"

private theorem _root_.ValuationSubring.eq_valuationSubringAtPrime_centre (hO : ∀ r : R, algebraMap R F r ∈ O) (hne : O ≠ ⊤) :
    O = HeightOneSpectrum.valuationSubringAtPrime F (O.centreHeightOneSpectrum hO hne) :=
  (ValuationSubring.eq_of_le_of_ne_top _ (O.valuationSubringAtPrime_centre_le hO hne) hne).symm

p2m_export "ValuationSubring" "eq_valuationSubringAtPrime_centre"

private theorem _root_.ValuationSubring.isPrincipalIdealRing_of_dedekind_le (hO : ∀ r : R, algebraMap R F r ∈ O) (hne : O ≠ ⊤) :
    IsPrincipalIdealRing O := by
  rw [O.eq_valuationSubringAtPrime_centre hO hne]
  infer_instance

p2m_export "ValuationSubring" "isPrincipalIdealRing_of_dedekind_le"
end ValuationSubring
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ValuationSubring"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_inv Place.finite_residueField_of_finiteDimensional"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg FiniteResidue ord ord_inv exists_unit_mul_zpow ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mem_maximalIdeal_iff_ord_pos restrict finite_residueField_of_finiteDimensional mem_of_ord_nonneg"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]

private def ofValuationSubringOver (O : ValuationSubring F) (hO : ∀ r : R, algebraMap R F r ∈ O)
    (hne : O ≠ ⊤) (hK : ∀ c : K, algebraMap K F c ∈ O) : Place K F where
  toValuationSubring := O
  algebraMap_mem' := hK
  ne_top' := hne
  isPrincipalIdealRing' := O.isPrincipalIdealRing_of_dedekind_le hO hne

@[scoped simp]
private theorem ofValuationSubringOver_toValuationSubring (O : ValuationSubring F)
    (hO : ∀ r : R, algebraMap R F r ∈ O) (hne : O ≠ ⊤) (hK : ∀ c : K, algebraMap K F c ∈ O) :
    (ofValuationSubringOver O hO hne hK).toValuationSubring = O := rfl

private theorem mem_nonunits_ofValuationSubringOver_iff (O : ValuationSubring F)
    (hO : ∀ r : R, algebraMap R F r ∈ O) (hne : O ≠ ⊤) (hK : ∀ c : K, algebraMap K F c ∈ O)
    {B : Subring F} {𝔭 : Ideal B} (hdom : ∀ b : B, (b : F) ∈ O.nonunits ↔ b ∈ 𝔭) (b : B) :
    (b : F) ∈ (ofValuationSubringOver O hO hne hK).toValuationSubring.nonunits ↔ b ∈ 𝔭 :=
  hdom b

end Place
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ValuationSubring P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.AlgebraicCurve.Place"

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ValuationSubring P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.AlgebraicCurve"

set_option autoImplicit false

open IsLocalRing Polynomial

namespace Valuation
p2m_export "Valuation" "map_add' ext map_sub map Integers ne_zero_iff map_neg integer restrict comap map_sum_eq_of_lt"
p2m_open "Valuation"

variable {R Γ₀ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]

private theorem _root_.Valuation.exists_ne_map_eq_of_sum_eq_zero {ι : Type*} [DecidableEq ι] (v : Valuation R Γ₀)
    {s : Finset ι} {f : ι → R} (hs : ∑ i ∈ s, f i = 0) {j : ι} (hj : j ∈ s)
    (hj0 : v (f j) ≠ 0) (hmax : ∀ i ∈ s, v (f i) ≤ v (f j)) :
    ∃ i ∈ s, i ≠ j ∧ v (f i) = v (f j) := by
  by_contra h
  push Not at h
  have hlt : ∀ i ∈ s \ {j}, v (f i) < v (f j) := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    exact lt_of_le_of_ne (hmax i hi.1) (h i hi.1 hi.2)
  have := v.map_sum_eq_of_lt hj hlt
  rw [hs, map_zero] at this
  exact hj0 this.symm

p2m_export "Valuation" "exists_ne_map_eq_of_sum_eq_zero"
end Valuation
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ValuationSubring P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.AlgebraicCurve"

namespace ValuationSubring
p2m_export "ValuationSubring" "comap subtype valuation_eq_iff coe_mem_nonunits_iff mem_comap neg_mem toSubring algebraMap_apply ext mem_nonunits_iff_or zero_mem nonunits mem_nonunits_iff mem_top eq_of_le_of_ne_top mul_mem mem_or_inv_mem nonunits_subset add_mem eq_top_iff valuation_le_one_iff algebra valuation"
p2m_open "ValuationSubring"

variable {K : Type*} [Field K] (A : ValuationSubring K)
variable {k : Type*} [Field k]

private theorem _root_.ValuationSubring.natCast_mem_ker (ℓ : ℕ) [CharP k ℓ] (red : A →+* k) :
    ((ℓ : ℕ) : A) ∈ RingHom.ker red := by
  rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]

p2m_export "ValuationSubring" "natCast_mem_ker"

private theorem _root_.ValuationSubring.natCast_mem_maximalIdeal (ℓ : ℕ) [CharP k ℓ] (red : A →+* k) :
    ((ℓ : ℕ) : A) ∈ maximalIdeal A :=
  IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top red) (A.natCast_mem_ker ℓ red)

p2m_export "ValuationSubring" "natCast_mem_maximalIdeal"

private theorem _root_.ValuationSubring.isUnit_intCast_of_not_dvd (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (red : A →+* k)
    {m : ℤ} (hm : ¬ (ℓ : ℤ) ∣ m) : IsUnit ((m : ℤ) : A) := by
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hprime.irreducible).mpr hm
  have hA : (a : A) * ((ℓ : ℕ) : A) + (b : A) * (m : A) = 1 := by
    have := congrArg (Int.cast : ℤ → A) hab
    push_cast at this
    exact this
  have hℓm : (a : A) * ((ℓ : ℕ) : A) ∈ maximalIdeal A :=
    Ideal.mul_mem_left _ _ (A.natCast_mem_maximalIdeal ℓ red)
  have hu : IsUnit ((b : A) * (m : A)) := by
    by_contra hnu
    have hmem : (b : A) * (m : A) ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h1 : (1 : A) ∈ maximalIdeal A := hA ▸ Ideal.add_mem _ hℓm hmem
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  exact isUnit_of_mul_isUnit_right hu

p2m_export "ValuationSubring" "isUnit_intCast_of_not_dvd"

private theorem _root_.ValuationSubring.map_intCast_eq_zero_of_not_isUnit (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (red : A →+* k)
    {m : ℤ} (hm : ¬ IsUnit ((m : ℤ) : A)) : red (m : A) = 0 := by
  have hdvd : (ℓ : ℤ) ∣ m := by
    by_contra h
    exact hm (A.isUnit_intCast_of_not_dvd ℓ red h)
  obtain ⟨c, rfl⟩ := hdvd
  rw [map_intCast]
  push_cast
  rw [CharP.cast_eq_zero k ℓ, zero_mul]

p2m_export "ValuationSubring" "map_intCast_eq_zero_of_not_isUnit"

private theorem _root_.ValuationSubring.map_eq_zero_of_rat_mem_maximalIdeal (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (red : A →+* k) (φ : ℚ →+* K) (r : ℚ) (hrA : φ r ∈ A)
    (hr : (⟨φ r, hrA⟩ : A) ∈ maximalIdeal A) : red ⟨φ r, hrA⟩ = 0 := by

  have hnum : (⟨φ r, hrA⟩ : A) * ((r.den : ℕ) : A) = ((r.num : ℤ) : A) := by
    apply Subtype.ext
    change φ r * (((r.den : ℕ) : A) : K) = (((r.num : ℤ) : A) : K)
    push_cast
    rw [← map_natCast φ, ← map_intCast φ, ← map_mul, Rat.mul_den_eq_num]

  have hnum_mem : ((r.num : ℤ) : A) ∈ maximalIdeal A := hnum ▸ Ideal.mul_mem_right _ _ hr
  have hnum0 : red ((r.num : ℤ) : A) = 0 :=
    A.map_intCast_eq_zero_of_not_isUnit ℓ red ((IsLocalRing.mem_maximalIdeal _).mp hnum_mem)

  have hden : ¬ (ℓ : ℤ) ∣ (r.den : ℤ) := by
    intro h
    have hℓnum : (ℓ : ℤ) ∣ r.num := by
      by_contra h'
      have hu : IsUnit ((r.num : ℤ) : A) := A.isUnit_intCast_of_not_dvd ℓ red h'
      exact (IsLocalRing.mem_maximalIdeal _).mp hnum_mem hu
    have h1 : (ℓ : ℤ) ∣ (Int.gcd r.num (r.den : ℤ) : ℤ) := Int.dvd_coe_gcd hℓnum h
    have hg : Int.gcd r.num (r.den : ℤ) = 1 := by
      simpa [Int.gcd, Int.natAbs_natCast] using r.reduced
    rw [hg] at h1
    have := Int.eq_one_of_dvd_one (by positivity) h1
    have hℓ1 : ℓ = 1 := by exact_mod_cast this
    exact (Fact.out : ℓ.Prime).one_lt.ne' hℓ1
  have hden0 : red ((r.den : ℕ) : A) ≠ 0 := by
    rw [map_natCast]
    intro h0
    rw [CharP.cast_eq_zero_iff k ℓ] at h0
    exact hden (by exact_mod_cast h0)

  have := congrArg red hnum
  rw [map_mul, hnum0] at this
  exact (mul_eq_zero.mp this).resolve_right hden0

p2m_export "ValuationSubring" "map_eq_zero_of_rat_mem_maximalIdeal"

private theorem _root_.ValuationSubring.exists_pow_valuation_eq_of_isRoot (φ : ℚ →+* K) {x : K} (hx0 : x ≠ 0)
    {p : ℚ[X]} (hp0 : p ≠ 0) (hpx : p.eval₂ φ x = 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ r : ℚ, r ≠ 0 ∧ A.valuation (x ^ n) = A.valuation (φ r) := by
  classical
  set v := A.valuation with hv
  let f : ℕ → K := fun i => φ (p.coeff i) * x ^ i
  have hsum : ∑ i ∈ p.support, f i = 0 := by
    rw [eval₂_eq_sum, Polynomial.sum_def] at hpx
    exact hpx
  have hvx : v x ≠ 0 := (v.ne_zero_iff).mpr hx0
  have hf0 : ∀ i ∈ p.support, v (f i) ≠ 0 := by
    intro i hi
    refine (v.ne_zero_iff).mpr (mul_ne_zero ?_ (pow_ne_zero _ hx0))
    exact (map_ne_zero φ).mpr (mem_support_iff.mp hi)
  obtain ⟨j, hj, hjmax⟩ :=
    Finset.exists_max_image p.support (fun i => v (f i)) (support_nonempty.mpr hp0)
  obtain ⟨i, hi, hij, heq⟩ := v.exists_ne_map_eq_of_sum_eq_zero hsum hj (hf0 j hj) hjmax

  obtain ⟨a, b, hab, ha, hb, heq'⟩ :
      ∃ a b : ℕ, a < b ∧ a ∈ p.support ∧ b ∈ p.support ∧ v (f a) = v (f b) := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h, hi, hj, heq⟩
    · exact ⟨j, i, h, hj, hi, heq.symm⟩
  have hca0 : v (φ (p.coeff a)) ≠ 0 := (v.ne_zero_iff).mpr ((map_ne_zero φ).mpr (mem_support_iff.mp ha))
  have hcb0 : v (φ (p.coeff b)) ≠ 0 := (v.ne_zero_iff).mpr ((map_ne_zero φ).mpr (mem_support_iff.mp hb))

  have h1 : v (φ (p.coeff a)) * v x ^ a = (v (φ (p.coeff b)) * v x ^ (b - a)) * v x ^ a := by
    have e : v x ^ b = v x ^ (b - a) * v x ^ a := by rw [← pow_add, Nat.sub_add_cancel hab.le]
    have := heq'
    simp only [f, map_mul, map_pow] at this
    rw [this, e, ← mul_assoc]
  have h2 : v (φ (p.coeff a)) = v (φ (p.coeff b)) * v x ^ (b - a) :=
    mul_right_cancel₀ (pow_ne_zero _ hvx) h1
  refine ⟨b - a, Nat.sub_pos_of_lt hab, p.coeff a / p.coeff b,
    div_ne_zero (mem_support_iff.mp ha) (mem_support_iff.mp hb), ?_⟩
  rw [map_div₀, map_div₀, map_pow, h2, mul_div_cancel_left₀ _ hcb0]

p2m_export "ValuationSubring" "exists_pow_valuation_eq_of_isRoot"

private theorem _root_.ValuationSubring.ker_eq_maximalIdeal_of_isAlgebraic [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (red : A →+* k) :
    RingHom.ker red = maximalIdeal A := by
  refine le_antisymm (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top red)) ?_
  intro x hx
  rw [RingHom.mem_ker]
  rcases eq_or_ne x 0 with rfl | hx0
  · exact map_zero red
  have hxK : (x : K) ≠ 0 := by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hx0
  obtain ⟨p, hp0, hpx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (x : K)
  obtain ⟨n, hn, r, hr0, hval⟩ :=
    A.exists_pow_valuation_eq_of_isRoot (algebraMap ℚ K) hxK hp0 (by rwa [← aeval_def])

  obtain ⟨u, hu⟩ := (A.valuation_eq_iff _ _).mp hval
  have hcoe : ((((u⁻¹ : Aˣ) : A) * x ^ n : A) : K) = algebraMap ℚ K r := by
    push_cast
    rw [← hu, ← mul_assoc, ← MulMemClass.coe_mul, Units.inv_mul, OneMemClass.coe_one, one_mul]
  have hrA : algebraMap ℚ K r ∈ A := hcoe ▸ SetLike.coe_mem _
  have hxn : x ^ n = (u : A) * ⟨algebraMap ℚ K r, hrA⟩ := by
    apply Subtype.ext
    push_cast
    exact hu.symm
  have hrm : (⟨algebraMap ℚ K r, hrA⟩ : A) ∈ maximalIdeal A := by
    have hxnm : x ^ n ∈ maximalIdeal A := Ideal.pow_mem_of_mem _ hx n hn
    rw [hxn] at hxnm
    exact ((IsLocalRing.maximalIdeal.isMaximal A).isPrime.mem_or_mem hxnm).resolve_left
      (fun h => (IsLocalRing.mem_maximalIdeal _).mp h u.isUnit)
  have hr0' : red ⟨algebraMap ℚ K r, hrA⟩ = 0 :=
    A.map_eq_zero_of_rat_mem_maximalIdeal ℓ red (algebraMap ℚ K) r hrA hrm
  have : red (x ^ n) = 0 := by rw [hxn, map_mul, hr0', mul_zero]
  rw [map_pow] at this
  exact pow_eq_zero_iff hn.ne' |>.mp this

p2m_export "ValuationSubring" "ker_eq_maximalIdeal_of_isAlgebraic"

private theorem exists_mul_eq_one_of_map_ne_zero [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (red : A →+* k) {a : A} (ha : red a ≠ 0) :
    ∃ b : A, red a * red b = 1 := by
  have hunit : IsUnit a := by
    by_contra h
    have : a ∈ RingHom.ker red := by
      rw [A.ker_eq_maximalIdeal_of_isAlgebraic ℓ red]
      exact (IsLocalRing.mem_maximalIdeal _).mpr h
    exact ha this
  obtain ⟨u, rfl⟩ := hunit
  exact ⟨((u⁻¹ : Aˣ) : A), by rw [← map_mul, Units.mul_inv, map_one]⟩

private theorem ker_eq_maximalIdeal_apply [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (red : A →+* k) (a : A) :
    red a = 0 ↔ a ∈ maximalIdeal A := by
  rw [← RingHom.mem_ker, A.ker_eq_maximalIdeal_of_isAlgebraic ℓ red]

end ValuationSubring
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ValuationSubring P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.AlgebraicCurve"

set_option autoImplicit false

noncomputable section

open scoped IntermediateField.algebraAdjoinAdjoin
open IntermediateField Polynomial

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_inv Place.finite_residueField_of_finiteDimensional"
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {j : F}

private theorem isPrincipalIdealRing_adjoin_singleton (hj : Transcendental K j) :
    IsPrincipalIdealRing (Algebra.adjoin K ({j} : Set F)) :=
  IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental K j hj).toRingHom
    (Polynomial.algEquivOfTranscendental K j hj).surjective

private theorem isDedekindDomain_adjoin_singleton (hj : Transcendental K j) :
    IsDedekindDomain (Algebra.adjoin K ({j} : Set F)) :=
  haveI := isPrincipalIdealRing_adjoin_singleton hj
  inferInstance

private theorem isDedekindDomain_integralClosure_adjoin (hj : Transcendental K j)
    [FiniteDimensional K⟮j⟯ F] [Algebra.IsSeparable K⟮j⟯ F] :
    IsDedekindDomain (integralClosure (Algebra.adjoin K ({j} : Set F)) F) :=
  haveI := isDedekindDomain_adjoin_singleton hj
  integralClosure.isDedekindDomain (Algebra.adjoin K ({j} : Set F)) K⟮j⟯ F

private theorem isFractionRing_integralClosure_adjoin (hj : Transcendental K j)
    [FiniteDimensional K⟮j⟯ F] :
    IsFractionRing (integralClosure (Algebra.adjoin K ({j} : Set F)) F) F :=
  haveI := isDedekindDomain_adjoin_singleton hj
  integralClosure.isFractionRing_of_finite_extension (A := Algebra.adjoin K ({j} : Set F)) K⟮j⟯ F

private theorem integralClosure_adjoin_le_valuationSubring (O : ValuationSubring F)
    (hK : ∀ c : K, algebraMap K F c ∈ O) (hjO : j ∈ O)
    (r : integralClosure (Algebra.adjoin K ({j} : Set F)) F) : (r : F) ∈ O := by

  let O' : Subalgebra K F :=
    { O.toSubring with
      algebraMap_mem' := hK }
  have hle : Algebra.adjoin K ({j} : Set F) ≤ O' :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hjO)
  let φ : Algebra.adjoin K ({j} : Set F) →+* O :=
    (Subalgebra.val _).toRingHom.codRestrict O.toSubring (fun y => hle y.2)

  obtain ⟨p, hp, hpr⟩ : IsIntegral (Algebra.adjoin K ({j} : Set F)) (r : F) := r.2
  have hint : IsIntegral O (r : F) := by
    refine ⟨p.map φ, hp.map φ, ?_⟩
    rw [eval₂_map]
    exact hpr
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

private theorem algebraMap_mem_integralClosure_adjoin (c : K) :
    algebraMap K F c ∈ integralClosure (Algebra.adjoin K ({j} : Set F)) F := by
  rw [mem_integralClosure_iff, IsScalarTower.algebraMap_apply K (Algebra.adjoin K ({j} : Set F)) F]
  exact isIntegral_algebraMap

private theorem self_mem_integralClosure_adjoin :
    j ∈ integralClosure (Algebra.adjoin K ({j} : Set F)) F := by
  rw [mem_integralClosure_iff]
  have : j = algebraMap (Algebra.adjoin K ({j} : Set F)) F ⟨j, Algebra.self_mem_adjoin_singleton K j⟩ :=
    rfl
  rw [this]
  exact isIntegral_algebraMap

private theorem le_integralClosure_adjoin_of_isIntegral {S B : Subring F}
    (hS : S ≤ (Algebra.adjoin K ({j} : Set F)).toSubring)
    (hint : ∀ b : B, IsIntegral S (b : F)) (b : B) :
    (b : F) ∈ integralClosure (Algebra.adjoin K ({j} : Set F)) F := by
  rw [mem_integralClosure_iff]
  obtain ⟨p, hp, hpb⟩ := hint b
  let φ : S →+* Algebra.adjoin K ({j} : Set F) :=
    S.subtype.codRestrict (Algebra.adjoin K ({j} : Set F)).toSubring (fun y => hS y.2)
  refine ⟨p.map φ, hp.map φ, ?_⟩
  rw [eval₂_map]
  exact hpb

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ValuationSubring P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.AlgebraicCurve"

set_option autoImplicit false

open Polynomial

namespace ValuationSubring
p2m_export "ValuationSubring" "comap subtype valuation_eq_iff coe_mem_nonunits_iff mem_comap neg_mem toSubring algebraMap_apply ext mem_nonunits_iff_or zero_mem nonunits mem_nonunits_iff mem_top eq_of_le_of_ne_top mul_mem mem_or_inv_mem nonunits_subset add_mem eq_top_iff valuation_le_one_iff algebra valuation"
p2m_open "ValuationSubring"

variable {K : Type*} [Field K] (A : ValuationSubring K) {k : Type*} [Field k]

private theorem isAlgClosed_of_surjective [IsAlgClosed K] (red : A →+* k)
    (hred : Function.Surjective red) : IsAlgClosed k := by
  refine IsAlgClosed.of_exists_root k fun p hp hirr => ?_

  have hlifts : p ∈ Polynomial.lifts red := (lifts_iff_coeff_lifts p).mpr fun n => hred _
  obtain ⟨P, hPp, hPdeg, hP⟩ := lifts_and_degree_eq_and_monic hlifts hp

  have hdegK : (P.map (algebraMap A K)).degree ≠ 0 := by
    rw [hP.degree_map, hPdeg]
    exact (degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (P.map (algebraMap A K)) hdegK

  have hint : IsIntegral A x := ⟨P, hP, by rwa [IsRoot.def, eval_map] at hx⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint

  have hy : P.eval y = 0 := by
    apply IsFractionRing.injective A K
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← eval_map]
    exact hx
  refine ⟨red y, ?_⟩
  rw [← hPp, eval_map, Polynomial.eval₂_at_apply, hy, map_zero]

end ValuationSubring
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ValuationSubring P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.AlgebraicCurve"

set_option autoImplicit false

namespace RingHom
p2m_export "RingHom" "IsIntegral.of_finite restrict coe_comp inverse IsIntegral surjective Finite ker_ne_top ext comp_apply rangeRestrict toAddMonoidHom codRestrict injective_int coe_mul ker_rangeRestrict ker range comp rangeRestrict_surjective toNonUnitalRingHom mem_ker mem_range_self coe_one"
p2m_open "RingHom"

variable {B C : Type*} [CommRing B] [CommRing C] (π : B →+* C)

private def _root_.RingHom.imagePrime (𝔮 : Ideal B) : Ideal π.range := 𝔮.map π.rangeRestrict

p2m_export "RingHom" "imagePrime"
variable {π} in

private theorem rangeRestrict_mem_imagePrime_iff {𝔮 : Ideal B} (hker : ker π ≤ 𝔮) (b : B) :
    π.rangeRestrict b ∈ π.imagePrime 𝔮 ↔ b ∈ 𝔮 := by
  rw [imagePrime, ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ π.rangeRestrict_surjective,
    ← RingHom.ker, ker_rangeRestrict, sup_eq_left.mpr hker]

variable {π} in

private theorem mk_mem_imagePrime_iff {𝔮 : Ideal B} (hker : ker π ≤ 𝔮) (b : B)
    (hb : π b ∈ π.range := π.mem_range_self b) :
    (⟨π b, hb⟩ : π.range) ∈ π.imagePrime 𝔮 ↔ b ∈ 𝔮 :=
  rangeRestrict_mem_imagePrime_iff hker b

variable {π} in

private theorem mem_imagePrime_iff {𝔮 : Ideal B} (y : π.range) :
    y ∈ π.imagePrime 𝔮 ↔ ∃ b ∈ 𝔮, π.rangeRestrict b = y := by
  rw [imagePrime, Ideal.mem_map_iff_of_surjective _ π.rangeRestrict_surjective]

variable {π} in

private theorem imagePrime_ne_top {𝔮 : Ideal B} (hker : ker π ≤ 𝔮) (h𝔮 : 𝔮 ≠ ⊤) :
    π.imagePrime 𝔮 ≠ ⊤ := by
  intro htop
  apply h𝔮
  rw [Ideal.eq_top_iff_one, ← rangeRestrict_mem_imagePrime_iff hker, map_one, htop]
  exact Submodule.mem_top

variable {π} in

private theorem imagePrime_isPrime {𝔮 : Ideal B} [𝔮.IsPrime] (hker : ker π ≤ 𝔮) :
    (π.imagePrime 𝔮).IsPrime :=
  Ideal.map_isPrime_of_surjective π.rangeRestrict_surjective (by rwa [ker_rangeRestrict])

variable {π} in

private theorem imagePrime_isMaximal {𝔮 : Ideal B} [h : 𝔮.IsMaximal] (hker : ker π ≤ 𝔮) :
    (π.imagePrime 𝔮).IsMaximal :=
  (Ideal.map_eq_top_or_isMaximal_of_surjective _ π.rangeRestrict_surjective h).resolve_left
    (imagePrime_ne_top hker h.ne_top)

variable {π} in

private theorem eq_zero_of_const_mem_imagePrime {A k : Type*} [CommRing A] [CommRing k]
    (σ : A →+* B) (red : A →+* k) (ι : k →+* C) (hcompat : ∀ a : A, π (σ a) = ι (red a))
    (hred : Function.Surjective red) {𝔮 : Ideal B} (hker : ker π ≤ 𝔮)
    (h𝔮 : ∀ a : A, σ a ∈ 𝔮 → red a = 0) (c : k) (hc : ι c ∈ π.range)
    (hmem : (⟨ι c, hc⟩ : π.range) ∈ π.imagePrime 𝔮) : c = 0 := by
  obtain ⟨a, rfl⟩ := hred c
  refine h𝔮 a ((rangeRestrict_mem_imagePrime_iff hker (σ a)).mp ?_)
  convert hmem using 1
  exact Subtype.ext (hcompat a)

variable {π} in

private theorem const_mem_range {A k : Type*} [CommRing A] [CommRing k]
    (σ : A →+* B) (red : A →+* k) (ι : k →+* C) (hcompat : ∀ a : A, π (σ a) = ι (red a))
    (hred : Function.Surjective red) (c : k) : ι c ∈ π.range := by
  obtain ⟨a, rfl⟩ := hred c
  exact ⟨σ a, hcompat a⟩

end RingHom
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ValuationSubring P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_inv Place.finite_residueField_of_finiteDimensional"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg FiniteResidue ord ord_inv exists_unit_mul_zpow ne_top' algebraMap_mem' toValuationSubring isPrincipalIdealRing' mem_maximalIdeal_iff_ord_pos restrict finite_residueField_of_finiteDimensional mem_of_ord_nonneg"
p2m_open "AlgebraicCurve.Place"

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

private theorem finite_residueField_of_adjoin_simple_eq_top_of_mem {x : E} (hx : Transcendental K x)
    (htop : IntermediateField.adjoin K ({x} : Set E) = ⊤) (v : Place K E)
    (hxv : x ∈ v.toValuationSubring) : Module.Finite K v.ResidueField := by
  classical

  haveI : IsDedekindDomain (Algebra.adjoin K ({x} : Set E)) := isDedekindDomain_adjoin_singleton hx
  haveI : FaithfulSMul (Algebra.adjoin K ({x} : Set E)) E :=
    (faithfulSMul_iff_algebraMap_injective _ E).mpr Subtype.val_injective
  haveI : IsFractionRing (Algebra.adjoin K ({x} : Set E)) E := by
    refine IsFractionRing.of_field (Algebra.adjoin K ({x} : Set E)) E (fun z => ?_)
    have hz : z ∈ IntermediateField.adjoin K ({x} : Set E) := by
      rw [htop]
      exact IntermediateField.mem_top
    obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
    exact ⟨⟨r, hr⟩, ⟨s, hs⟩, rfl⟩
  set O := v.toValuationSubring with hOdef

  have hO : ∀ r : Algebra.adjoin K ({x} : Set E), algebraMap _ E r ∈ O := by
    intro r
    have hle : Algebra.adjoin K ({x} : Set E) ≤
        { O.toSubring with algebraMap_mem' := v.algebraMap_mem' } :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr hxv)
    exact hle r.2
  have hne : O ≠ ⊤ := v.ne_top'

  let xO : O := ⟨x, hxv⟩
  let xbar : v.ResidueField := IsLocalRing.residue O xO
  have hcomp : (IsLocalRing.residue O).comp (algebraMap K O) = algebraMap K v.ResidueField :=
    RingHom.ext fun _ => rfl
  have hres_aeval : ∀ p : K[X], IsLocalRing.residue O (Polynomial.aeval xO p) =
      Polynomial.aeval xbar p := fun p => by
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, hcomp]
  have hcoe_aeval : ∀ p : K[X], ((Polynomial.aeval xO p : O) : E) = Polynomial.aeval x p :=
    fun p => by
    have := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom K O E) xO p

    exact this.symm
  let e := Polynomial.algEquivOfTranscendental K x hx
  have hcoe_e : ∀ p : K[X], ((e p : Algebra.adjoin K ({x} : Set E)) : E) = Polynomial.aeval x p :=
    fun p => by
    rw [Polynomial.algEquivOfTranscendental_apply, Polynomial.aeval_subalgebra_coe]

  have hOe : ∀ p : K[X], (⟨((e p : Algebra.adjoin K ({x} : Set E)) : E), hO (e p)⟩ : O) =
      Polynomial.aeval xO p := fun p => Subtype.ext (by rw [hcoe_aeval, hcoe_e])

  obtain ⟨f, hf𝔭, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (O.centreOver_ne_bot hO hne)
  obtain ⟨g, rfl⟩ := e.surjective f
  have hg0 : g ≠ 0 := fun h => hf0 (by rw [h, map_zero])
  have hgbar : Polynomial.aeval xbar g = 0 := by
    rw [← hres_aeval, IsLocalRing.residue_eq_zero_iff, ← hOe,
      ← ValuationSubring.coe_mem_nonunits_iff]
    exact (O.mem_centreOver_iff hO).mp hf𝔭
  have halg : IsAlgebraic K xbar := ⟨g, hg0, hgbar⟩
  have hint : IsIntegral K xbar := halg.isIntegral
  haveI : FiniteDimensional K K⟮xbar⟯ := IntermediateField.adjoin.finiteDimensional hint

  have htop' : K⟮xbar⟯ = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
    have hz : (z : E) ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E
        (O.centreHeightOneSpectrum hO hne) := by
      rw [← O.eq_valuationSubringAtPrime_centre hO hne]
      exact z.2
    obtain ⟨a, s, hs, hz'⟩ := hz
    obtain ⟨ga, rfl⟩ := e.surjective a
    obtain ⟨gs, rfl⟩ := e.surjective s

    have hsn : ((e gs : Algebra.adjoin K ({x} : Set E)) : E) ∉ O.nonunits := fun h =>
      hs ((O.mem_centreOver_iff hO).mpr h)
    have hres_s : IsLocalRing.residue O (Polynomial.aeval xO gs) ≠ 0 := by
      rw [Ne, IsLocalRing.residue_eq_zero_iff, ← hOe, ← ValuationSubring.coe_mem_nonunits_iff]
      exact hsn
    have hs0 : ((e gs : Algebra.adjoin K ({x} : Set E)) : E) ≠ 0 := fun h =>
      hsn (h ▸ (zero_mem O.nonunits))

    have hmul : z * Polynomial.aeval xO gs = Polynomial.aeval xO ga := by
      rw [← hOe, ← hOe]
      apply Subtype.ext
      change (z : E) * _ = _
      push_cast
      rw [hz']
      exact inv_mul_cancel_right₀ hs0 _
    have hzq : IsLocalRing.residue O z =
        Polynomial.aeval xbar ga / Polynomial.aeval xbar gs := by
      rw [eq_div_iff (by rwa [← hres_aeval]), ← hres_aeval, ← hres_aeval, ← map_mul, hmul]
    rw [hzq]
    refine div_mem ?_ ?_ <;>
      exact IntermediateField.algebra_adjoin_le_adjoin K _ (Polynomial.aeval_mem_adjoin_singleton K _)

  have : FiniteDimensional K (⊤ : IntermediateField K v.ResidueField) := by
    rw [← htop']
    infer_instance
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

private theorem _root_.IntermediateField.adjoin_simple_inv_eq (x : E) :
    IntermediateField.adjoin K ({x⁻¹} : Set E) = IntermediateField.adjoin K ({x} : Set E) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self K x)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have h := inv_mem (IntermediateField.mem_adjoin_simple_self K x⁻¹)
    rwa [inv_inv] at h

p2m_alias "P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.IntermediateField.adjoin_simple_inv_eq" "IntermediateField.adjoin_simple_inv_eq"

private theorem finite_residueField_of_adjoin_simple_eq_top {x : E} (hx : Transcendental K x)
    (htop : IntermediateField.adjoin K ({x} : Set E) = ⊤) (v : Place K E) :
    Module.Finite K v.ResidueField := by
  by_cases hxv : x ∈ v.toValuationSubring
  · exact finite_residueField_of_adjoin_simple_eq_top_of_mem hx htop v hxv
  ·
    have hxinv : x⁻¹ ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem x).resolve_left hxv
    have hx' : Transcendental K x⁻¹ := fun h => hx (by simpa using h.inv)
    have htop' : IntermediateField.adjoin K ({x⁻¹} : Set E) = ⊤ := by
      rw [IntermediateField.adjoin_simple_inv_eq x, htop]
    exact finite_residueField_of_adjoin_simple_eq_top_of_mem hx' htop' v hxinv

private theorem finiteResidue_of_adjoin_simple_eq_top {x : E} (hx : Transcendental K x)
    (htop : IntermediateField.adjoin K ({x} : Set E) = ⊤) (v : Place K E) : v.FiniteResidue :=
  ⟨finite_residueField_of_adjoin_simple_eq_top hx htop v⟩

end Place
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ValuationSubring P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ModularCurve P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.ValuationSubring P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.AlgebraicCurve"

open _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar.AlgebraicCurve in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (N : ℕ) [NeZero N]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (w : Place (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) :
    (∃ a : A, (jBar N - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        (a : AlgebraicClosure ℚ)) ∈ w.toValuationSubring.nonunits) ∨
      (∃ a : A, ((jBar N)⁻¹ - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        (a : AlgebraicClosure ℚ)) ∈ w.toValuationSubring.nonunits) := by
  classical
  haveI hFD : FiniteDimensional
      (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jBar N} : Set (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))))
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :=
    ModularCurve.CharPModel.finiteDimensional_lineBar_of_dataAll N dataAll
  haveI h2 : Module.Finite (AlgebraicClosure ℚ)
      ((w.restrict (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jBar N} : Set (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))))).ResidueField) := by
    have h := ModularCurve.CharPModel.adjoin_val_preimage_eq_top
      (K := AlgebraicClosure ℚ) (L := laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      (F := IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jBar N} : Set (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))))
      (S := ({jBar N} : Set (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))) rfl
    have hset : (Subtype.val ⁻¹' ({jBar N} : Set (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) :
        Set (IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({jBar N} : Set (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))))
        = {⟨jBar N, IntermediateField.mem_adjoin_simple_self _ (jBar N)⟩} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hz => Subtype.ext hz, fun hz => by rw [hz]⟩
    rw [hset] at h
    exact AlgebraicCurve.Place.finite_residueField_of_adjoin_simple_eq_top
      (ModularCurve.CharPModel.transcendental_subtype _
        (IntermediateField.mem_adjoin_simple_self _ (jBar N))
        (ModularCurve.CharPModel.transcendental_jBar N)) h _
  haveI h2f : Module.Finite
      ((w.restrict (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jBar N} : Set (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))))).ResidueField)
      w.ResidueField :=
    AlgebraicCurve.Place.finite_residueField_of_finiteDimensional w
  haveI h3 : Module.Finite (AlgebraicClosure ℚ) w.ResidueField :=
    Module.Finite.trans
      ((w.restrict (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jBar N} : Set (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))))).ResidueField)
      w.ResidueField
  have hsurj : Function.Surjective
      (algebraMap (AlgebraicClosure ℚ) w.ResidueField) :=
    AlgebraicCurve.Place.surjective_algebraMap_residueField_of_isAlgClosed w
  have hjne : (jBar N : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ≠ 0 := by
    intro h0
    apply ModularCurve.transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N
    have halg : IsAlgebraic (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar N) := by
      rw [h0]
      exact isAlgebraic_zero
    exact halg
  by_cases hmem : (jBar N : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ∈ w.toValuationSubring
  · obtain ⟨c, hc⟩ := AlgebraicCurve.Place.exists_hasValueAt w hsurj hmem
    rcases eq_or_ne c 0 with rfl | hc0
    · exact Or.inl ⟨⟨0, A.zero_mem⟩, hc⟩
    · rcases A.mem_or_inv_mem c with hcA | hcA
      · exact Or.inl ⟨⟨c, hcA⟩, hc⟩
      · exact Or.inr ⟨⟨c⁻¹, hcA⟩, hc.inv hc0⟩
  · refine Or.inr ⟨0, ?_⟩
    have hlt : w.ord (jBar N : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) < 0 := by
      by_contra hge
      exact hmem (w.mem_of_ord_nonneg hjne (not_lt.mp hge))
    have hinvne : ((jBar N)⁻¹ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ≠ 0 := inv_ne_zero hjne
    have hpos : 0 < w.ord ((jBar N)⁻¹ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) := by
      rw [AlgebraicCurve.Place.ord_inv]
      exact neg_pos.mpr hlt
    have hnu := (w.mem_nonunits_iff_ord_pos hinvne).mpr hpos
    simpa using hnu

end
end
end S_ModularCurve_CharPModel_chart_dichotomy_jBar
end P2MW
export P2MW.S_ModularCurve_CharPModel_chart_dichotomy_jBar (solution)
