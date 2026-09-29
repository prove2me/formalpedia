-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.spPlace_d7_dictZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/0aed47f5-3eb5-57eb-8669-52d090a1ea0d

import Definitions.Def_ModularCurve_SpecializationMap
import Theorems.Thm_ModularCurve_CharPModel_chart_dichotomy_jBar
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero_of_t_small
import Theorems.Thm_AlgebraicCurve_Place_finite_residueField_of_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.qExpandAlgHomC_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

p2m_open "ModularCurve~jBar P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel"
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve"
open Polynomial
open IsLocalRing

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq jqN evalAtJ ModularPolynomialData jq_mem divisorExpansions mem_divisorExpansions modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange EvalSymm CharPModel.jBar CharPModel.jNBar CharPModel.FibreModel modularFunctionFieldBar HeckeAlphaBarIntegral HeckeBetaBarIntegral laurentMap_injective KroneckerCongruence CharPModel.chart_dichotomy_jBar transcendental_coeffEmb_jq transcendental_jqModC CharPModel.FibreModel.spPlace_d7_dictZero_of_t_small"
p2m_open "ModularCurve~jBar"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar jNBar constantsHom affineBaseFin affineBaseInf FibreModel chart_dichotomy_jBar FibreModel.spPlace_d7_dictZero_of_t_small"
p2m_open "ModularCurve.CharPModel"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place"

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
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq jqN evalAtJ ModularPolynomialData jq_mem divisorExpansions mem_divisorExpansions modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange EvalSymm CharPModel.jBar CharPModel.jNBar CharPModel.FibreModel modularFunctionFieldBar HeckeAlphaBarIntegral HeckeBetaBarIntegral laurentMap_injective KroneckerCongruence CharPModel.chart_dichotomy_jBar transcendental_coeffEmb_jq transcendental_jqModC CharPModel.FibreModel.spPlace_d7_dictZero_of_t_small"
p2m_open "ModularCurve~jBar"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar jNBar constantsHom affineBaseFin affineBaseInf FibreModel chart_dichotomy_jBar FibreModel.spPlace_d7_dictZero_of_t_small"
p2m_open "ModularCurve.CharPModel"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place"

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
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve"

end CharPModel
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve"

noncomputable section

open IsLocalRing

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_inv IsCurveOver Place.finite_residueField_of_finiteDimensional"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg FiniteResidue ord ord_mul ord_inv ord_zpow exists_unit_mul_zpow ne_top' algebraMap_mem' toValuationSubring mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos restrict ord_nonneg_of_mem mem_of_ord_nonneg finite_residueField_of_finiteDimensional"
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
private theorem _root_.AlgebraicCurve.Place.hasValueAt_of_ord_pos {f : F} {a : K} (h : 0 < w.ord (f - algebraMap K F a)) :
    w.HasValueAt f a := by
  have hne : f ≠ algebraMap K F a := by
    intro hfa; rw [hfa, sub_self] at h; simp at h
  exact (w.hasValueAt_iff_ord_pos hne).mpr h

p2m_export "AlgebraicCurve.Place" "hasValueAt_of_ord_pos"

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
p2m_open_scoped "AlgebraicCurve.Place.HasValueAt" in
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
p2m_open_scoped "AlgebraicCurve.Place.HasValueAt" in
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
p2m_open_scoped "AlgebraicCurve.Place.HasValueAt" in
variable {w} in
private theorem _root_.AlgebraicCurve.Place.HasValueAt.neg {f : F} {a : K} (hf : w.HasValueAt f a) : w.HasValueAt (-f) (-a) := by
  have := neg_mem hf
  rw [HasValueAt, map_neg]
  convert this using 1
  ring

end HasValueAt
p2m_export "AlgebraicCurve.Place" "HasValueAt.neg"
namespace HasValueAt
p2m_open_scoped "AlgebraicCurve.Place.HasValueAt" in
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
p2m_open_scoped "AlgebraicCurve.Place.HasValueAt" in
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
p2m_open_scoped "AlgebraicCurve.Place.HasValueAt" in
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

private theorem _root_.AlgebraicCurve.Place.exists_hasValueAt (hw : Function.Surjective (algebraMap K w.ResidueField)) {f : F}
    (hf : f ∈ w.toValuationSubring) : ∃ a : K, w.HasValueAt f a := by
  obtain ⟨a, ha⟩ := hw (residue w.toValuationSubring ⟨f, hf⟩)
  exact ⟨a, (w.hasValueAt_iff_residue hf a).mpr ha.symm⟩

p2m_export "AlgebraicCurve.Place" "exists_hasValueAt"

private theorem mul_inv_pow_succ_mul {F : Type*} [Field F] {x y : F}
    (hx : x ≠ 0) (hy : y ≠ 0) (m : ℕ) :
    (y * x⁻¹ ^ (m + 1)) * (x * y⁻¹ ^ (m + 1)) = ((x * y)⁻¹) ^ m := by
  have key : ∀ z : F, z ≠ 0 → z * z⁻¹ ^ (m + 1) = z⁻¹ ^ m := by
    intro z hz
    rw [pow_succ, mul_comm (z⁻¹ ^ m) z⁻¹, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]
  calc (y * x⁻¹ ^ (m + 1)) * (x * y⁻¹ ^ (m + 1))
      = (x * x⁻¹ ^ (m + 1)) * (y * y⁻¹ ^ (m + 1)) := by ring
    _ = x⁻¹ ^ m * y⁻¹ ^ m := by rw [key x hx, key y hy]
    _ = ((x * y)⁻¹) ^ m := by rw [mul_inv, mul_pow]

private theorem div_pow_succ_mul_div_pow_succ {F : Type*} [Field F] {x y : F}
    (hx : x ≠ 0) (hy : y ≠ 0) (m : ℕ) :
    (y / x ^ (m + 1)) * (x / y ^ (m + 1)) = ((x * y)⁻¹) ^ m := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← inv_pow, ← inv_pow]
  exact mul_inv_pow_succ_mul hx hy m

private theorem div_pow_succ_eq_inv_pow_mul_inv {F : Type*} [Field F] {x y : F}
    (hx : x ≠ 0) (hy : y ≠ 0) (m : ℕ) :
    x / y ^ (m + 1) = ((x * y)⁻¹) ^ m * (y / x ^ (m + 1))⁻¹ := by
  have h2 := div_pow_succ_mul_div_pow_succ hx hy m
  have hne : y / x ^ (m + 1) ≠ 0 := div_ne_zero hy (pow_ne_zero _ hx)
  rw [← h2, mul_comm (y / x ^ (m + 1)) (x / y ^ (m + 1)), mul_inv_cancel_right₀ hne]

private theorem _root_.AlgebraicCurve.Place.surjective_algebraMap_residueField_of_isAlgClosed [IsAlgClosed K]
    [Module.Finite K w.ResidueField] : Function.Surjective (algebraMap K w.ResidueField) :=
  haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K w.ResidueField
  (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := w.ResidueField)).2

p2m_export "AlgebraicCurve.Place" "surjective_algebraMap_residueField_of_isAlgClosed"

private theorem surjective_algebraMap_residueField_of_deg_eq_one [IsAlgClosed K] (h : w.deg = 1) :
    Function.Surjective (algebraMap K w.ResidueField) :=
  haveI : Module.Finite K w.ResidueField := Module.finite_of_finrank_eq_succ (n := 0) h
  w.surjective_algebraMap_residueField_of_isAlgClosed

variable (A : ValuationSubring K)

private def _root_.AlgebraicCurve.Place.compSubring : Subring F where
  carrier := {f | ∃ a : A, w.HasValueAt f a}
  mul_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, by simpa using ha.mul hb⟩
  one_mem' := ⟨1, by simpa using w.hasValueAt_algebraMap 1⟩
  add_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by simpa using ha.add hb⟩
  zero_mem' := ⟨0, by simpa using w.hasValueAt_algebraMap 0⟩
  neg_mem' := by
    rintro f ⟨a, ha⟩
    exact ⟨-a, by simpa using ha.neg⟩

p2m_export "AlgebraicCurve.Place" "compSubring"
variable {A} in
private theorem mem_compSubring_iff {f : F} : f ∈ w.compSubring A ↔ ∃ a : A, w.HasValueAt f a :=
  Iff.rfl

variable {A} in
private theorem _root_.AlgebraicCurve.Place.mem_compSubring_of_hasValueAt {f : F} {a : K} (ha : a ∈ A) (h : w.HasValueAt f a) :
    f ∈ w.compSubring A :=
  ⟨⟨a, ha⟩, h⟩

p2m_export "AlgebraicCurve.Place" "mem_compSubring_of_hasValueAt"

private theorem _root_.AlgebraicCurve.Place.compSubring_le : w.compSubring A ≤ w.toValuationSubring.toSubring := by
  rintro f ⟨a, ha⟩
  exact w.mem_of_hasValueAt ha

p2m_export "AlgebraicCurve.Place" "compSubring_le"

private theorem _root_.AlgebraicCurve.Place.mem_compSubring_of_mem_nonunits {f : F} (hf : f ∈ w.toValuationSubring.nonunits) :
    f ∈ w.compSubring A :=
  ⟨0, by simpa [w.hasValueAt_zero_iff] using hf⟩

p2m_export "AlgebraicCurve.Place" "mem_compSubring_of_mem_nonunits"

private theorem _root_.AlgebraicCurve.Place.algebraMap_mem_compSubring_iff (a : K) : algebraMap K F a ∈ w.compSubring A ↔ a ∈ A := by
  constructor
  · rintro ⟨b, hb⟩
    rw [(w.hasValueAt_algebraMap a).unique hb]
    exact b.2
  · intro ha
    exact ⟨⟨a, ha⟩, w.hasValueAt_algebraMap a⟩

p2m_export "AlgebraicCurve.Place" "algebraMap_mem_compSubring_iff"

private def _root_.AlgebraicCurve.Place.value : w.compSubring A →+* A where
  toFun f := Classical.choose f.2
  map_one' := Subtype.ext <|
    (Classical.choose_spec (w.compSubring A).one_mem).unique (by
      simpa using w.hasValueAt_algebraMap 1)
  map_mul' f g := Subtype.ext <|
    (Classical.choose_spec (mul_mem f.2 g.2)).unique (by
      simpa using (Classical.choose_spec f.2).mul (Classical.choose_spec g.2))
  map_zero' := Subtype.ext <|
    (Classical.choose_spec (w.compSubring A).zero_mem).unique (by
      simpa using w.hasValueAt_algebraMap 0)
  map_add' f g := Subtype.ext <|
    (Classical.choose_spec (add_mem f.2 g.2)).unique (by
      simpa using (Classical.choose_spec f.2).add (Classical.choose_spec g.2))

p2m_export "AlgebraicCurve.Place" "value"

private theorem _root_.AlgebraicCurve.Place.hasValueAt_value (f : w.compSubring A) : w.HasValueAt (f : F) (w.value A f : K) :=
  Classical.choose_spec f.2

p2m_export "AlgebraicCurve.Place" "hasValueAt_value"
variable {A} in
private theorem _root_.AlgebraicCurve.Place.value_eq_of_hasValueAt {f : w.compSubring A} {a : A} (h : w.HasValueAt (f : F) a) :
    w.value A f = a :=
  Subtype.ext ((w.hasValueAt_value A f).unique h)

p2m_export "AlgebraicCurve.Place" "value_eq_of_hasValueAt"
variable {A} in

private theorem _root_.AlgebraicCurve.Place.ord_sub_value_pos {f : w.compSubring A} (hf : (f : F) ≠ algebraMap K F (w.value A f)) :
    0 < w.ord ((f : F) - algebraMap K F (w.value A f)) :=
  (w.hasValueAt_iff_ord_pos hf).mp (w.hasValueAt_value A f)

p2m_export "AlgebraicCurve.Place" "ord_sub_value_pos"
variable {A} in
private theorem value_eq_of_ord_pos {f : w.compSubring A} {a : A}
    (h : 0 < w.ord ((f : F) - algebraMap K F a)) : w.value A f = a :=
  w.value_eq_of_hasValueAt (w.hasValueAt_of_ord_pos h)

private theorem _root_.AlgebraicCurve.Place.value_algebraMap (a : A) :
    w.value A ⟨algebraMap K F a, (w.algebraMap_mem_compSubring_iff A a).mpr a.2⟩ = a :=
  w.value_eq_of_hasValueAt (w.hasValueAt_algebraMap (a : K))

p2m_export "AlgebraicCurve.Place" "value_algebraMap"
private theorem _root_.AlgebraicCurve.Place.value_surjective : Function.Surjective (w.value A) :=
  fun a => ⟨_, w.value_algebraMap A a⟩

p2m_export "AlgebraicCurve.Place" "value_surjective"
variable {A} in

private theorem _root_.AlgebraicCurve.Place.value_eq_zero_of_mem_nonunits {f : w.compSubring A}
    (hf : (f : F) ∈ w.toValuationSubring.nonunits) : w.value A f = 0 :=
  w.value_eq_of_hasValueAt (by simpa [w.hasValueAt_zero_iff] using hf)

p2m_export "AlgebraicCurve.Place" "value_eq_zero_of_mem_nonunits"

private def _root_.AlgebraicCurve.Place.centre : Ideal (w.compSubring A) := (maximalIdeal A).comap (w.value A)

p2m_export "AlgebraicCurve.Place" "centre"
private scoped instance centre_isPrime : (w.centre A).IsPrime := Ideal.comap_isPrime _ _

private scoped instance centre_isMaximal : (w.centre A).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective _ (w.value_surjective A)

variable {A} in
private theorem mem_centre_iff (f : w.compSubring A) : f ∈ w.centre A ↔ w.value A f ∈ maximalIdeal A :=
  Iff.rfl

variable {A} in
private theorem _root_.AlgebraicCurve.Place.mem_centre_iff_of_hasValueAt {f : w.compSubring A} {a : A} (h : w.HasValueAt (f : F) a) :
    f ∈ w.centre A ↔ a ∈ maximalIdeal A := by
  rw [mem_centre_iff, w.value_eq_of_hasValueAt h]

p2m_export "AlgebraicCurve.Place" "mem_centre_iff_of_hasValueAt"
variable {A} in

private theorem mem_centre_iff_of_ord_pos {f : w.compSubring A} {a : A}
    (h : 0 < w.ord ((f : F) - algebraMap K F a)) : f ∈ w.centre A ↔ a ∈ maximalIdeal A :=
  w.mem_centre_iff_of_hasValueAt (w.hasValueAt_of_ord_pos h)

variable {A} in

private theorem _root_.AlgebraicCurve.Place.mem_centre_of_mem_nonunits {f : w.compSubring A}
    (hf : (f : F) ∈ w.toValuationSubring.nonunits) : f ∈ w.centre A := by
  rw [mem_centre_iff, w.value_eq_zero_of_mem_nonunits hf]
  exact Ideal.zero_mem _

p2m_export "AlgebraicCurve.Place" "mem_centre_of_mem_nonunits"
variable {A} in
private theorem mem_centre_of_ord_pos {f : w.compSubring A} (hf : 0 < w.ord (f : F)) : f ∈ w.centre A :=
  w.mem_centre_of_mem_nonunits ((w.mem_nonunits_iff_ord_pos (by rintro h; simp [h] at hf)).mpr hf)

private theorem _root_.AlgebraicCurve.Place.algebraMap_mem_centre_iff (a : A) :
    (⟨algebraMap K F a, (w.algebraMap_mem_compSubring_iff A a).mpr a.2⟩ : w.compSubring A)
        ∈ w.centre A ↔ a ∈ maximalIdeal A := by
  rw [mem_centre_iff, value_algebraMap]

p2m_export "AlgebraicCurve.Place" "algebraMap_mem_centre_iff"

private theorem _root_.AlgebraicCurve.Place.mem_compSubring_or_inv_mem (hw : Function.Surjective (algebraMap K w.ResidueField))
    (f : F) : f ∈ w.compSubring A ∨ f⁻¹ ∈ w.compSubring A := by
  by_cases hf : f ∈ w.toValuationSubring
  · obtain ⟨c, hc⟩ := w.exists_hasValueAt hw hf
    by_cases hcA : c ∈ A
    · exact Or.inl ⟨⟨c, hcA⟩, hc⟩
    · right

      have hcA' : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
      have hc0 : c ≠ 0 := fun h => hcA (h ▸ A.zero_mem)
      have hf0 : f ≠ 0 := by
        rintro rfl
        have : w.HasValueAt (0 : F) 0 := by simpa using w.hasValueAt_algebraMap 0
        exact hc0 (hc.unique this)
      have hfu : f ∉ w.toValuationSubring.nonunits := by
        intro hfn
        exact hc0 (hc.unique ((w.hasValueAt_zero_iff f).mpr hfn))
      have hfinv : f⁻¹ ∈ w.toValuationSubring := by
        by_contra hne
        exact hfu ((ValuationSubring.mem_nonunits_iff_or _).mpr (Or.inr (by simpa using hne)))
      refine ⟨⟨c⁻¹, hcA'⟩, ?_⟩

      have hprod : (f - algebraMap K F c) * (f⁻¹ * algebraMap K F c⁻¹)
          ∈ w.toValuationSubring.nonunits :=
        w.mul_mem_nonunits hc (mul_mem hfinv (w.algebraMap_mem _))
      have := neg_mem hprod
      show f⁻¹ - algebraMap K F (c⁻¹ : K) ∈ w.toValuationSubring.nonunits
      convert this using 1
      have hcF : algebraMap K F c ≠ 0 := by simpa using hc0
      rw [map_inv₀]
      field_simp
      ring
  ·
    right
    refine w.mem_compSubring_of_mem_nonunits A ?_
    exact (ValuationSubring.inv_mem_nonunits_iff _).mpr (Or.inr hf)

p2m_export "AlgebraicCurve.Place" "mem_compSubring_or_inv_mem"

private def _root_.AlgebraicCurve.Place.compValuationSubring (hw : Function.Surjective (algebraMap K w.ResidueField)) :
    ValuationSubring F :=
  ValuationSubring.ofSubring (w.compSubring A) (w.mem_compSubring_or_inv_mem A hw)

p2m_export "AlgebraicCurve.Place" "compValuationSubring"
@[scoped simp]
private theorem compValuationSubring_toSubring (hw : Function.Surjective (algebraMap K w.ResidueField)) :
    (w.compValuationSubring A hw).toSubring = w.compSubring A := rfl

private theorem mem_compValuationSubring_iff (hw : Function.Surjective (algebraMap K w.ResidueField))
    (f : F) : f ∈ w.compValuationSubring A hw ↔ f ∈ w.compSubring A := Iff.rfl

private theorem mem_compSubring_of_isIntegral (hw : Function.Surjective (algebraMap K w.ResidueField))
    {S : Subring F} (hS : S ≤ w.compSubring A) {f : F} (hf : IsIntegral S f) :
    f ∈ w.compSubring A := by
  obtain ⟨p, hp, hpf⟩ := hf
  let V := w.compValuationSubring A hw
  let i : S →+* V := Subring.inclusion hS
  have hint : IsIntegral V f := by
    refine ⟨p.map i, hp.map i, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hpf
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

private theorem _root_.AlgebraicCurve.Place.mem_compSubring_of_isIntegral' [IsAlgClosed K] {S : Subring F} (hS : S ≤ w.compSubring A)
    {f : F} (hf : IsIntegral S f) : f ∈ w.compSubring A := by
  obtain ⟨p, hp, hpf⟩ := hf
  have hSO : ∀ s : S, (s : F) ∈ w.toValuationSubring := fun s => w.compSubring_le A (hS s.2)

  have hfO : f ∈ w.toValuationSubring := by
    refine w.mem_of_eval_monic_eq_zero (P := p.map S.subtype) (hp.map _) (fun i => ?_) ?_
    · rw [Polynomial.coeff_map]
      exact hSO _
    · rw [Polynomial.eval_map]
      exact hpf

  let vS : S →+* A := (w.value A).comp (Subring.inclusion hS)
  let ιS : S →+* w.toValuationSubring := S.subtype.codRestrict _ hSO
  have hres : (residue w.toValuationSubring).comp ιS =
      ((algebraMap K w.ResidueField).comp (algebraMap A K)).comp vS := by
    ext s
    change residue w.toValuationSubring ⟨s, hSO s⟩ =
      algebraMap K w.ResidueField ((w.value A ⟨s, hS s.2⟩ : A) : K)
    exact (w.hasValueAt_iff_residue (hSO s) _).mp (w.hasValueAt_value A ⟨s, hS s.2⟩)
  set r : w.ResidueField := residue w.toValuationSubring ⟨f, hfO⟩ with hr
  let Q : Polynomial A := p.map vS
  have hQ : Q.Monic := hp.map _
  have hzero : Polynomial.eval₂ ιS ⟨f, hfO⟩ p = 0 := by
    apply Subtype.val_injective
    change w.toValuationSubring.subtype (Polynomial.eval₂ ιS ⟨f, hfO⟩ p) = ((0 : w.toValuationSubring) : F)
    rw [Polynomial.hom_eval₂]
    exact hpf
  have hrootκ : Polynomial.eval₂ (algebraMap K w.ResidueField) r (Q.map (algebraMap A K)) = 0 := by
    rw [Polynomial.eval₂_map, Polynomial.eval₂_map, ← hres, hr, ← Polynomial.hom_eval₂, hzero,
      map_zero]

  have hint : IsIntegral K r := ⟨Q.map (algebraMap A K), hQ.map _, hrootκ⟩
  obtain ⟨c, hc⟩ : r ∈ (algebraMap K w.ResidueField).range :=
    minpoly.mem_range_of_degree_eq_one K r
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint))

  have hcroot : Polynomial.eval₂ (algebraMap A K) c Q = 0 := by
    apply (algebraMap K w.ResidueField).injective
    rw [Polynomial.hom_eval₂, ← Polynomial.eval₂_map, hc, hrootκ, map_zero]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (⟨Q, hQ, hcroot⟩ : IsIntegral A c)

  refine ⟨y, (w.hasValueAt_iff_residue hfO _).mpr ?_⟩
  rw [← hr, ← hc, ← hy]
  rfl

p2m_export "AlgebraicCurve.Place" "mem_compSubring_of_isIntegral'"

private theorem exists_unique_valueHom [IsAlgClosed K] (g : F) (B₀ : Subring F)
    (hint : ∀ b : B₀,
      ∃ p : Polynomial (Subring.closure (algebraMap K F '' (A : Set K) ∪ {g})),
        p.Monic ∧
          Polynomial.eval₂ (Subring.closure (algebraMap K F '' (A : Set K) ∪ {g})).subtype
            (b : F) p = 0)
    (hw : ∃ a : A, g - algebraMap K F (a : K) ∈ w.toValuationSubring.nonunits) :
    ∃! φ : B₀ →+* A, ∀ b : B₀,
      (b : F) - algebraMap K F ((φ b : A) : K) ∈ w.toValuationSubring.nonunits := by

  obtain ⟨a₀, ha₀⟩ := hw
  have hg : g ∈ w.compSubring A := w.mem_compSubring_of_hasValueAt a₀.2 ha₀
  have hS : Subring.closure (algebraMap K F '' (A : Set K) ∪ {g}) ≤ w.compSubring A := by
    rw [Subring.closure_le]
    rintro y (⟨c, hc, rfl⟩ | rfl)
    · exact (w.algebraMap_mem_compSubring_iff A c).mpr hc
    · exact hg
  have hB₀ : B₀ ≤ w.compSubring A := fun b hb => w.mem_compSubring_of_isIntegral' A hS (hint ⟨b, hb⟩)

  refine ⟨(w.value A).comp (Subring.inclusion hB₀), fun b => w.hasValueAt_value A ⟨b, hB₀ b.2⟩, ?_⟩

  intro ψ hψ
  refine RingHom.ext fun b => ?_
  have h1 : w.HasValueAt (b : F) ((ψ b : A) : K) := hψ b
  have h2 : ψ b = w.value A ⟨b, hB₀ b.2⟩ := Subtype.ext (h1.unique (w.hasValueAt_value A ⟨b, hB₀ b.2⟩))
  exact h2

variable {A} in

private theorem _root_.AlgebraicCurve.Place.residue_comp_value_surjective {B : Subring F} (hB : B ≤ w.compSubring A)
    (hconst : ∀ a : A, algebraMap K F a ∈ B) :
    Function.Surjective
      (((IsLocalRing.residue A).comp (w.value A)).comp (Subring.inclusion hB)) := by
  intro x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  refine ⟨⟨algebraMap K F a, hconst a⟩, ?_⟩
  change IsLocalRing.residue A (w.value A ⟨algebraMap K F a, hB (hconst a)⟩) = _
  rw [w.value_eq_of_hasValueAt (w.hasValueAt_algebraMap (a : K))]

p2m_export "AlgebraicCurve.Place" "residue_comp_value_surjective"
variable {A} in

private theorem _root_.AlgebraicCurve.Place.ker_residue_comp_value {B : Subring F} (hB : B ≤ w.compSubring A) :
    RingHom.ker (((IsLocalRing.residue A).comp (w.value A)).comp (Subring.inclusion hB)) =
      (w.centre A).comap (Subring.inclusion hB) := by
  ext b
  rw [RingHom.mem_ker, Ideal.mem_comap, mem_centre_iff, RingHom.comp_apply, RingHom.comp_apply,
    IsLocalRing.residue_eq_zero_iff]

p2m_export "AlgebraicCurve.Place" "ker_residue_comp_value"
variable {A} in
private theorem centre_comap_isMaximal {B : Subring F} (hB : B ≤ w.compSubring A)
    (hconst : ∀ a : A, algebraMap K F a ∈ B) :
    ((w.centre A).comap (Subring.inclusion hB)).IsMaximal := by
  rw [← w.ker_residue_comp_value hB]
  exact RingHom.ker_isMaximal_of_surjective _ (w.residue_comp_value_surjective hB hconst)

variable {A} in

private theorem sub_value_mem_centre_comap {B : Subring F} (hB : B ≤ w.compSubring A)
    (hconst : ∀ a : A, algebraMap K F a ∈ B) (b : B) :
    b - ⟨algebraMap K F (w.value A ⟨b, hB b.2⟩ : K), hconst _⟩ ∈
      (w.centre A).comap (Subring.inclusion hB) := by
  rw [Ideal.mem_comap, mem_centre_iff]
  simp only [map_sub]
  have h1 : w.value A (Subring.inclusion hB ⟨algebraMap K F (w.value A ⟨b, hB b.2⟩ : K), hconst _⟩)
      = w.value A ⟨b, hB b.2⟩ :=
    w.value_eq_of_hasValueAt (w.hasValueAt_algebraMap _)
  have h2 : w.value A (Subring.inclusion hB b) = w.value A ⟨b, hB b.2⟩ := rfl
  rw [h1, h2, sub_self]
  exact Ideal.zero_mem _

variable {A} in

private theorem algebraMap_mem_centre_comap_iff {B : Subring F} (hB : B ≤ w.compSubring A)
    (hconst : ∀ a : A, algebraMap K F a ∈ B) (a : A) :
    (⟨algebraMap K F a, hconst a⟩ : B) ∈ (w.centre A).comap (Subring.inclusion hB) ↔
      a ∈ maximalIdeal A := by
  rw [Ideal.mem_comap]
  exact w.algebraMap_mem_centre_iff A a

end Place
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place"

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve"

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq jqN evalAtJ ModularPolynomialData jq_mem divisorExpansions mem_divisorExpansions modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange EvalSymm CharPModel.jBar CharPModel.jNBar CharPModel.FibreModel modularFunctionFieldBar HeckeAlphaBarIntegral HeckeBetaBarIntegral laurentMap_injective KroneckerCongruence CharPModel.chart_dichotomy_jBar transcendental_coeffEmb_jq transcendental_jqModC CharPModel.FibreModel.spPlace_d7_dictZero_of_t_small"
p2m_open "ModularCurve~jBar"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar jNBar constantsHom affineBaseFin affineBaseInf FibreModel chart_dichotomy_jBar FibreModel.spPlace_d7_dictZero_of_t_small"
p2m_open "ModularCurve.CharPModel"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place"

section SolWork

variable {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {ℓ : ℕ} [Fact ℓ.Prime] {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}

namespace FibreModel p2m_export "ModularCurve.CharPModel.FibreModel" "spPlace piInf_mem_spPlace_nonunits_iff integralInf integralFin jNBar_mem jInvBar_mem piInf_const piInf_jInv BFin piInf BInf constInf_mem CuspChart spPlace_d7_dictZero_of_t_small" end FibreModel
namespace FibreModel
p2m_open_scoped "ModularCurve.CharPModel.FibreModel" in
private theorem _root_.ModularCurve.CharPModel.FibreModel.bfin_le_compSubring (fm : FibreModel N A ℓ k red)
    (w : Place (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
    (hwFin : (jBar N : laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionFieldFull N)) ∈ w.compSubring A) :
    fm.BFin ≤ (w.compSubring A : Subring (laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionFieldFull N))) := by
  have hS : affineBaseFin N A ≤ w.compSubring A := by
    refine Subring.closure_le.mpr ?_
    rintro x (⟨a, rfl⟩ | rfl)
    · exact (w.algebraMap_mem_compSubring_iff A _).mpr a.2
    · exact hwFin
  exact fun x hx => w.mem_compSubring_of_isIntegral' A hS (fm.integralFin ⟨x, hx⟩)

end FibreModel
p2m_export "ModularCurve.CharPModel" "FibreModel.bfin_le_compSubring"
end SolWork
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve"
end CharPModel
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve"

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq jqN evalAtJ ModularPolynomialData jq_mem divisorExpansions mem_divisorExpansions modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange EvalSymm CharPModel.jBar CharPModel.jNBar CharPModel.FibreModel modularFunctionFieldBar HeckeAlphaBarIntegral HeckeBetaBarIntegral laurentMap_injective KroneckerCongruence CharPModel.chart_dichotomy_jBar transcendental_coeffEmb_jq transcendental_jqModC CharPModel.FibreModel.spPlace_d7_dictZero_of_t_small"
p2m_open "ModularCurve~jBar"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar jNBar constantsHom affineBaseFin affineBaseInf FibreModel chart_dichotomy_jBar FibreModel.spPlace_d7_dictZero_of_t_small"
p2m_open "ModularCurve.CharPModel"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place"

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem fibreEvalSwap_subtype (k : Type*) [Field k] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) (hsym : EvalSymm data.Φ) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ)
        (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N)).toRingHom
      (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) = 0 := by
  have hcomp : ((modularFunctionFieldC k N).val.toRingHom).comp
      (Polynomial.aeval (R := ℤ)
        (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N)).toRingHom
      = (Polynomial.aeval (R := ℤ) (jqNModC k N)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [eq_intCast, map_intCast]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, Polynomial.aeval_X]
      rfl
  have h := Polynomial.hom_eval₂ data.Φ
    (Polynomial.aeval (R := ℤ)
      (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N)).toRingHom
    ((modularFunctionFieldC k N).val.toRingHom)
    (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
  apply Subtype.val_injective
  have h0 : (modularFunctionFieldC k N).val.toRingHom
      (data.Φ.eval₂ (Polynomial.aeval (R := ℤ)
        (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N)).toRingHom
        (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)) = 0 := by
    rw [h, hcomp]
    exact fibreEvalSwap_eq_zero N data hsym k
  simpa using h0

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem barEvalSwap_laurent (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (hsym : EvalSymm data.Φ) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ)
        (coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq))).toRingHom
      (coeffEmb (AlgebraicClosure ℚ) jq) = 0 := by
  have hswap0 : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (qExpand ℚ N jq)).toRingHom jq
      = 0 := by
    rw [show qExpand ℚ N jq = jqN N from rfl, hsym (jqN N) jq]
    have h0 := data.eval_eq_zero
    rw [show evalAtJ = (Polynomial.aeval (R := ℤ) jq).toRingHom from rfl] at h0
    exact h0
  have hcomp : ((coeffEmb (AlgebraicClosure ℚ)).comp
      (Polynomial.aeval (R := ℤ) (qExpand ℚ N jq)).toRingHom)
      = (Polynomial.aeval (R := ℤ)
          (coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq))).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [eq_intCast, map_intCast]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, Polynomial.aeval_X]
  have h := Polynomial.hom_eval₂ data.Φ
    (Polynomial.aeval (R := ℤ) (qExpand ℚ N jq)).toRingHom
    (coeffEmb (AlgebraicClosure ℚ)) jq
  rw [hswap0, map_zero, hcomp] at h
  exact h.symm

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem barEvalSwap_subtype (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (hsym : EvalSymm data.Φ) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jNBar N)).toRingHom (jBar N) = 0 := by
  have hcomp : (((laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionFieldFull N)).val.toRingHom).comp
      (Polynomial.aeval (R := ℤ) (jNBar N)).toRingHom)
      = (Polynomial.aeval (R := ℤ)
          (coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq))).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [eq_intCast, map_intCast]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, Polynomial.aeval_X]
      rfl
  have h := Polynomial.hom_eval₂ data.Φ
    (Polynomial.aeval (R := ℤ) (jNBar N)).toRingHom
    ((laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).val.toRingHom)
    (jBar N)
  apply Subtype.val_injective
  have h0 : (laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionFieldFull N)).val.toRingHom
      (data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jNBar N)).toRingHom (jBar N)) = 0 := by
    rw [h, hcomp]
    exact barEvalSwap_laurent N data hsym
  simpa using h0

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem transcendental_jNC (k : Type*) [Field k] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) (hsym : EvalSymm data.Φ) :
    Transcendental k (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) := by
  intro halg
  haveI hFD : FiniteDimensional k
      (IntermediateField.adjoin k
        ({⟨jqNModC k N, jqNModC_mem k N⟩} : Set (modularFunctionFieldC k N))) :=
    IntermediateField.adjoin.finiteDimensional halg.isIntegral
  have h2 : IsIntegral
      (IntermediateField.adjoin k
        ({⟨jqNModC k N, jqNModC_mem k N⟩} : Set (modularFunctionFieldC k N)))
      (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) :=
    isIntegral_adjoin_of_bivar_monic data.monic (fibreEvalSwap_subtype k N data hsym)
  have h3 : IsIntegral k (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) := by
    haveI : Algebra.IsIntegral k
        (IntermediateField.adjoin k
          ({⟨jqNModC k N, jqNModC_mem k N⟩} : Set (modularFunctionFieldC k N))) :=
      Algebra.IsIntegral.of_finite _ _
    exact isIntegral_trans _ h2
  exact (transcendental_jC k N) h3.isAlgebraic

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem transcendental_jNBar (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) (hsym : EvalSymm data.Φ) :
    Transcendental (AlgebraicClosure ℚ) (jNBar N) := by
  intro halg
  haveI hFD : FiniteDimensional (AlgebraicClosure ℚ)
      (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jNBar N} : Set (laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionFieldFull N)))) :=
    IntermediateField.adjoin.finiteDimensional halg.isIntegral
  have h2 : IsIntegral
      (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jNBar N} : Set (laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionFieldFull N))))
      (jBar N) :=
    isIntegral_adjoin_of_bivar_monic data.monic (barEvalSwap_subtype N data hsym)
  have h3 : IsIntegral (AlgebraicClosure ℚ) (jBar N) := by
    haveI : Algebra.IsIntegral (AlgebraicClosure ℚ)
        (IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({jNBar N} : Set (laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionFieldFull N)))) :=
      Algebra.IsIntegral.of_finite _ _
    exact isIntegral_trans _ h2
  exact (transcendental_jBar N) h3.isAlgebraic

private theorem jBar_ne_const (N : ℕ) [NeZero N] (c : AlgebraicClosure ℚ) :
    jBar N ≠ algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) c :=
  fun h => transcendental_jBar N (h ▸ isAlgebraic_algebraMap c)

private theorem jLine_ne_const (k : Type*) [Field k] (N : ℕ) [NeZero N] (c : k) :
    jLine k N ≠ algebraMap k (modularFunctionFieldC k N) c :=
  fun h => transcendental_jLine k N (h ▸ isAlgebraic_algebraMap c)

private theorem jLine_ne_zero (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    (jLine k N : modularFunctionFieldC k N) ≠ 0 :=
  fun h => transcendental_jLine k N (h ▸ isAlgebraic_zero)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem mem_of_ord_nonneg {k' F' : Type*} [Field k'] [Field F'] [Algebra k' F']
    (v : Place k' F') {x : F'} (hx : x ≠ 0) (h : 0 ≤ v.ord x) :
    x ∈ v.toValuationSubring := by
  by_contra hmem
  rcases v.toValuationSubring.mem_or_inv_mem x with hx' | hinv
  · exact hmem hx'
  have hinv_nu : x⁻¹ ∈ v.toValuationSubring.nonunits := by
    refine (ValuationSubring.mem_nonunits_iff_or _).mpr (Or.inr ?_)
    rwa [inv_inv]
  have hpos : 0 < v.ord x⁻¹ :=
    (v.mem_nonunits_iff_ord_pos (inv_ne_zero hx)).mp hinv_nu
  rw [v.ord_inv] at hpos
  exact absurd h (not_le.mpr (neg_pos.mp hpos))

private theorem ord_nonneg_of_mem' {k' F' : Type*} [Field k'] [Field F'] [Algebra k' F']
    (v : Place k' F') {x : F'} (hx : x ≠ 0) (h : x ∈ v.toValuationSubring) :
    0 ≤ v.ord x := by
  by_contra hneg
  have hpos : 0 < v.ord x⁻¹ := by
    rw [v.ord_inv]
    exact neg_pos.mpr (not_le.mp hneg)
  have hnu : x⁻¹ ∈ v.toValuationSubring.nonunits :=
    (v.mem_nonunits_iff_ord_pos (inv_ne_zero hx)).mpr hpos
  rcases (ValuationSubring.mem_nonunits_iff_or _).mp hnu with h0 | hninv
  · exact inv_ne_zero hx h0
  · rw [inv_inv] at hninv
    exact hninv h

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem jNBar_ne_const (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (hsym : EvalSymm data.Φ) (c : AlgebraicClosure ℚ) :
    jNBar N ≠ algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) c :=
  fun h => transcendental_jNBar N data hsym (h ▸ isAlgebraic_algebraMap c)

private theorem jNLine_ne_const (k : Type*) [Field k] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) (hsym : EvalSymm data.Φ) (c : k) :
    jNLine k N ≠ algebraMap k (modularFunctionFieldC k N) c := by
  intro h
  have htr : Transcendental k (jNLine k N) := transcendental_jNC k N data hsym
  exact htr (h ▸ isAlgebraic_algebraMap c)

private theorem jNLine_ne_zero (k : Type*) [Field k] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) (hsym : EvalSymm data.Φ) :
    (jNLine k N : modularFunctionFieldC k N) ≠ 0 := by
  intro h
  have htr : Transcendental k (jNLine k N) := transcendental_jNC k N data hsym
  exact htr (h ▸ isAlgebraic_zero)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem aeval_mem_subring {F' : Type*} [Field F'] (S : Subring F') {x : F'} (hx : x ∈ S)
    (p : Polynomial ℤ) : Polynomial.aeval (R := ℤ) x p ∈ S := by
  have hcomp : (S.subtype).comp
      (Polynomial.aeval (R := ℤ) (⟨x, hx⟩ : S)).toRingHom
      = (Polynomial.aeval (R := ℤ) x).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [eq_intCast, map_intCast]
    · rw [RingHom.comp_apply]
      rw [show (Polynomial.aeval (R := ℤ) (⟨x, hx⟩ : S)).toRingHom Polynomial.X
          = (⟨x, hx⟩ : S) from Polynomial.aeval_X _]
      rw [show (Polynomial.aeval (R := ℤ) x).toRingHom Polynomial.X = x
          from Polynomial.aeval_X _]
      rfl
  have h := congrArg (fun φ : Polynomial ℤ →+* F' => φ p) hcomp
  simp only [RingHom.coe_comp, Function.comp_apply] at h
  rw [show Polynomial.aeval (R := ℤ) x p
      = (Polynomial.aeval (R := ℤ) x).toRingHom p from rfl, ← h]
  exact SetLike.coe_mem _

private theorem jBar_sub_const_ne (N : ℕ) [NeZero N] (c : AlgebraicClosure ℚ) :
    (ModularCurve.CharPModel.jBar N : laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionFieldFull N))
      - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionFieldFull N)) c ≠ 0 := by
  intro h0
  apply ModularCurve.transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N
  have halg : IsAlgebraic (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar N) := by
    have : (ModularCurve.CharPModel.jBar N : laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionFieldFull N))
        = algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionFieldFull N)) c := by
      have := sub_eq_zero.mp h0
      exact this
    rw [this]
    exact isAlgebraic_algebraMap c
  exact halg

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem ord_jLine_neg_of_pole (N : ℕ) [NeZero N]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] (k : Type*)
    [Field k] [CharP k ℓ] (red : A →+* k)
    (fm : ModularCurve.CharPModel.FibreModel N A ℓ k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularCurve.ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable) :
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
    (∀ a : A,
      w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) ≤ 0) →
    ((fm.spPlace hred dataAll hsep) w).ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
        < 0 := by
  intro w hpole

  rcases ModularCurve.CharPModel.chart_dichotomy_jBar N A dataAll w with ⟨a, ha⟩ | ⟨a, ha⟩
  · exfalso
    have hne := jBar_sub_const_ne N (a : AlgebraicClosure ℚ)
    have hpos := (w.mem_nonunits_iff_ord_pos hne).mp ha
    exact absurd hpos (not_lt.mpr (hpole a))

  · have hjne : (ModularCurve.CharPModel.jBar N : laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionFieldFull N)) ≠ 0 := by
      have := jBar_sub_const_ne N 0
      simpa using this
    have ha𝔪 : (a : A) ∈ IsLocalRing.maximalIdeal A := by
      by_contra hunit
      have hu : IsUnit (a : A) := IsLocalRing.notMem_maximalIdeal.mp hunit
      obtain ⟨u, hu_eq⟩ := hu
      have hane : (a : AlgebraicClosure ℚ) ≠ 0 := by
        intro h0
        apply hunit
        have : (a : A) = 0 := Subtype.ext h0
        rw [this]
        exact (IsLocalRing.maximalIdeal A).zero_mem

      have hinv_mem : ((a : AlgebraicClosure ℚ))⁻¹ ∈ A := by
        have : ((u⁻¹ : Aˣ) : A) * (a : A) = 1 := by
          rw [← hu_eq]
          exact u.inv_mul
        have hcoe : (((u⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) * (a : AlgebraicClosure ℚ) = 1 := by
          exact_mod_cast congrArg (algebraMap A (AlgebraicClosure ℚ)) this
        have : (((u⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) = ((a : AlgebraicClosure ℚ))⁻¹ :=
          eq_inv_of_mul_eq_one_left hcoe
        rw [← this]
        exact ((u⁻¹ : Aˣ) : A).2

      have hval : w.HasValueAt
          (ModularCurve.CharPModel.jBar N : laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionFieldFull N)) ((a : AlgebraicClosure ℚ))⁻¹ := by
        have hv : w.HasValueAt
            ((ModularCurve.CharPModel.jBar N : laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionFieldFull N))⁻¹) (a : AlgebraicClosure ℚ) := ha
        have := hv.inv hane
        simpa [inv_inv] using this
      have hne := jBar_sub_const_ne N ((a : AlgebraicClosure ℚ))⁻¹
      have hpos := (w.mem_nonunits_iff_ord_pos hne).mp hval
      exact absurd hpos (not_lt.mpr (hpole ⟨_, hinv_mem⟩))

    have hdict := (fm.piInf_mem_spPlace_nonunits_iff hred dataAll hsep w hpole
        ⟨(ModularCurve.CharPModel.jBar N)⁻¹, fm.jInvBar_mem⟩).mpr ⟨a, ha𝔪, ha⟩
    rw [fm.piInf_jInv] at hdict

    have hlne := jLine_ne_zero k N
    have hpos := ((fm.spPlace hred dataAll hsep w).mem_nonunits_iff_ord_pos
      (inv_ne_zero hlne)).mp hdict
    have hoinv := AlgebraicCurve.Place.ord_inv
      (v := fm.spPlace hred dataAll hsep w)
      (ModularCurve.CharPModel.jLine k N)
    rw [hoinv] at hpos
    show (fm.spPlace hred dataAll hsep w).ord (ModularCurve.CharPModel.jLine k N) < 0
    linarith

end CharPModel
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem sol_d0_jN_pole (N : ℕ) [NeZero N]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] (k : Type*)
    [Field k] [CharP k ℓ] (red : A →+* k)
    (fm : ModularCurve.CharPModel.FibreModel N A ℓ k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularCurve.ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hsym : ModularCurve.EvalSymm (dataAll N (dvd_refl N)).Φ) :
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
    (∀ a : A,
      w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) ≤ 0) →
    ((fm.spPlace hred dataAll hsep) w).ord (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k
        N) < 0 := by
  intro w hpole
  by_cases h : (ModularCurve.CharPModel.jBar N : laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionFieldFull N)) ∈ w.compSubring A
  · exfalso
    have hvN : (ModularCurve.CharPModel.jNBar N : laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionFieldFull N)) ∈ w.compSubring A :=
      fm.bfin_le_compSubring w h fm.jNBar_mem
    have ha₀ := w.ord_sub_value_pos (f := ⟨ModularCurve.CharPModel.jNBar N, hvN⟩)
      (ModularCurve.CharPModel.jNBar_ne_const N (dataAll N (dvd_refl N)) hsym
        ((w.value A ⟨ModularCurve.CharPModel.jNBar N, hvN⟩ : A) : AlgebraicClosure ℚ))
    exact absurd ha₀ (not_lt.mpr (hpole (w.value A ⟨ModularCurve.CharPModel.jNBar N, hvN⟩)))
  · have hjpole : ∀ a : A, w.ord ((ModularCurve.CharPModel.jBar N : laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionFieldFull N)) - algebraMap (AlgebraicClosure ℚ)
          (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          (a : AlgebraicClosure ℚ)) ≤ 0 := by
      intro a
      by_contra hgt
      push Not at hgt
      exact h (w.mem_compSubring_of_hasValueAt (A := A) a.2 (w.hasValueAt_of_ord_pos hgt))
    have hjneg := ModularCurve.CharPModel.ord_jLine_neg_of_pole N A ℓ k red fm hred dataAll hsep w hjpole
    by_contra hge
    push Not at hge
    have hmemN : (ModularCurve.CharPModel.jNLine k N : modularFunctionFieldC k N) ∈
        (fm.spPlace hred dataAll hsep w).toValuationSubring :=
      ModularCurve.CharPModel.mem_of_ord_nonneg _
        (ModularCurve.CharPModel.jNLine_ne_zero k N (dataAll N (dvd_refl N)) hsym) hge
    have hmemJ : (ModularCurve.CharPModel.jLine k N : modularFunctionFieldC k N) ∈
        (fm.spPlace hred dataAll hsep w).toValuationSubring := by
      refine (fm.spPlace hred dataAll hsep w).mem_of_eval_monic_eq_zero
        (P := (dataAll N (dvd_refl N)).Φ.map
          ((Polynomial.aeval (R := ℤ) (ModularCurve.CharPModel.jNLine k N)).toRingHom))
        ((dataAll N (dvd_refl N)).monic.map _) (fun i => ?_) ?_
      · rw [Polynomial.coeff_map]
        exact ModularCurve.CharPModel.aeval_mem_subring
          (fm.spPlace hred dataAll hsep w).toValuationSubring.toSubring hmemN _
      · rw [Polynomial.eval_map]
        exact ModularCurve.CharPModel.fibreEvalSwap_subtype k N (dataAll N (dvd_refl N)) hsym
    exact absurd (ModularCurve.CharPModel.ord_nonneg_of_mem' _
      (ModularCurve.CharPModel.jLine_ne_zero k N) hmemJ) (not_le.mpr hjneg)

p2m_open "ModularCurve~jBar P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel"
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve"
open Polynomial
open IsLocalRing
open IsDedekindDomain

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq jqN evalAtJ ModularPolynomialData jq_mem divisorExpansions mem_divisorExpansions modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange EvalSymm CharPModel.jBar CharPModel.jNBar CharPModel.FibreModel modularFunctionFieldBar HeckeAlphaBarIntegral HeckeBetaBarIntegral laurentMap_injective KroneckerCongruence CharPModel.chart_dichotomy_jBar transcendental_coeffEmb_jq transcendental_jqModC CharPModel.FibreModel.spPlace_d7_dictZero_of_t_small"
p2m_open "ModularCurve~jBar"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar jNBar constantsHom affineBaseFin affineBaseInf FibreModel chart_dichotomy_jBar FibreModel.spPlace_d7_dictZero_of_t_small"
p2m_open "ModularCurve.CharPModel"

section LaurentMap

variable {R S : Type*} [CommRing R] [CommRing S]

end LaurentMap
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve"
section FibreEval
variable {R S : Type*} [CommRing R] [CommRing S]
variable (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
end FibreEval
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve"
end CharPModel
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve"
namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq jqN evalAtJ ModularPolynomialData jq_mem divisorExpansions mem_divisorExpansions modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange EvalSymm CharPModel.jBar CharPModel.jNBar CharPModel.FibreModel modularFunctionFieldBar HeckeAlphaBarIntegral HeckeBetaBarIntegral laurentMap_injective KroneckerCongruence CharPModel.chart_dichotomy_jBar transcendental_coeffEmb_jq transcendental_jqModC CharPModel.FibreModel.spPlace_d7_dictZero_of_t_small"
p2m_open "ModularCurve~jBar"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar jNBar constantsHom affineBaseFin affineBaseInf FibreModel chart_dichotomy_jBar FibreModel.spPlace_d7_dictZero_of_t_small"
p2m_open "ModularCurve.CharPModel"
section LineTier
end LineTier
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve"
end CharPModel
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve"
namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq jqN evalAtJ ModularPolynomialData jq_mem divisorExpansions mem_divisorExpansions modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange EvalSymm CharPModel.jBar CharPModel.jNBar CharPModel.FibreModel modularFunctionFieldBar HeckeAlphaBarIntegral HeckeBetaBarIntegral laurentMap_injective KroneckerCongruence CharPModel.chart_dichotomy_jBar transcendental_coeffEmb_jq transcendental_jqModC CharPModel.FibreModel.spPlace_d7_dictZero_of_t_small"
p2m_open "ModularCurve~jBar"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar jNBar constantsHom affineBaseFin affineBaseInf FibreModel chart_dichotomy_jBar FibreModel.spPlace_d7_dictZero_of_t_small"
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
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve"

end CharPModel
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve"

noncomputable section

open IsLocalRing

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_inv IsCurveOver Place.finite_residueField_of_finiteDimensional"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg FiniteResidue ord ord_mul ord_inv ord_zpow exists_unit_mul_zpow ne_top' algebraMap_mem' toValuationSubring mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos restrict ord_nonneg_of_mem mem_of_ord_nonneg finite_residueField_of_finiteDimensional"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

end Place
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve"
end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve"
end
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve"

namespace ValuationSubring
p2m_export "ValuationSubring" "comap subtype coe_mem_nonunits_iff mem_comap neg_mem toSubring algebraMap_apply ext mem_nonunits_iff_or zero_mem nonunits ofSubring mem_nonunits_iff inv_mem_nonunits_iff mem_top eq_of_le_of_ne_top mul_mem one_mem mem_or_inv_mem nonunits_subset add_mem eq_top_iff valuation_le_one_iff algebra valuation inclusion"
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
end ValuationSubring
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ValuationSubring"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_inv IsCurveOver Place.finite_residueField_of_finiteDimensional"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg FiniteResidue ord ord_mul ord_inv ord_zpow exists_unit_mul_zpow ne_top' algebraMap_mem' toValuationSubring mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos restrict ord_nonneg_of_mem mem_of_ord_nonneg finite_residueField_of_finiteDimensional"
p2m_open "AlgebraicCurve.Place"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
end Place
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ValuationSubring"
end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ValuationSubring"
set_option autoImplicit false
open IsLocalRing Polynomial

namespace Valuation
p2m_export "Valuation" "map_add' ext map_sub map Integers congr map_neg integer restrict comap"
p2m_open "Valuation"
variable {R Γ₀ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
end Valuation
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ValuationSubring"
namespace ValuationSubring
p2m_export "ValuationSubring" "comap subtype coe_mem_nonunits_iff mem_comap neg_mem toSubring algebraMap_apply ext mem_nonunits_iff_or zero_mem nonunits ofSubring mem_nonunits_iff inv_mem_nonunits_iff mem_top eq_of_le_of_ne_top mul_mem one_mem mem_or_inv_mem nonunits_subset add_mem eq_top_iff valuation_le_one_iff algebra valuation inclusion"
p2m_open "ValuationSubring"
variable {K : Type*} [Field K] (A : ValuationSubring K)
variable {k : Type*} [Field k]

end ValuationSubring
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ValuationSubring"
set_option autoImplicit false
open scoped IntermediateField.algebraAdjoinAdjoin
open IntermediateField Polynomial
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_inv IsCurveOver Place.finite_residueField_of_finiteDimensional"
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

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ValuationSubring"
set_option autoImplicit false
open Polynomial
namespace ValuationSubring
p2m_export "ValuationSubring" "comap subtype coe_mem_nonunits_iff mem_comap neg_mem toSubring algebraMap_apply ext mem_nonunits_iff_or zero_mem nonunits ofSubring mem_nonunits_iff inv_mem_nonunits_iff mem_top eq_of_le_of_ne_top mul_mem one_mem mem_or_inv_mem nonunits_subset add_mem eq_top_iff valuation_le_one_iff algebra valuation inclusion"
p2m_open "ValuationSubring"
variable {K : Type*} [Field K] (A : ValuationSubring K) {k : Type*} [Field k]
end ValuationSubring
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ValuationSubring"
set_option autoImplicit false
namespace RingHom
p2m_export "RingHom" "IsIntegral.of_finite restrict coe_comp ker_isMaximal_of_surjective inverse IsIntegral surjective Finite ext comp_apply toAddMonoidHom codRestrict injective_int coe_mul ker range comp toNonUnitalRingHom mem_ker coe_one"
p2m_open "RingHom"
variable {B C : Type*} [CommRing B] [CommRing C] (π : B →+* C)
end RingHom
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ValuationSubring"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_inv IsCurveOver Place.finite_residueField_of_finiteDimensional"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg FiniteResidue ord ord_mul ord_inv ord_zpow exists_unit_mul_zpow ne_top' algebraMap_mem' toValuationSubring mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos restrict ord_nonneg_of_mem mem_of_ord_nonneg finite_residueField_of_finiteDimensional"
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

p2m_alias "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.IntermediateField.adjoin_simple_inv_eq" "IntermediateField.adjoin_simple_inv_eq"

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
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ValuationSubring"

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ValuationSubring"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_inv IsCurveOver Place.finite_residueField_of_finiteDimensional"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg FiniteResidue ord ord_mul ord_inv ord_zpow exists_unit_mul_zpow ne_top' algebraMap_mem' toValuationSubring mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos restrict ord_nonneg_of_mem mem_of_ord_nonneg finite_residueField_of_finiteDimensional"
p2m_open "AlgebraicCurve.Place"

p2m_open "ModularCurve~jBar" in open _root_.P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve _root_.ModularCurve.CharPModel _root_.P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem surj_residue_bar (N : ℕ) [NeZero N]
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (w : Place (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) :
    Function.Surjective (algebraMap (AlgebraicClosure ℚ) w.ResidueField) := by
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

  exact hsurj

end Place
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ValuationSubring"
end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ValuationSubring"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_inv IsCurveOver Place.finite_residueField_of_finiteDimensional"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg FiniteResidue ord ord_mul ord_inv ord_zpow exists_unit_mul_zpow ne_top' algebraMap_mem' toValuationSubring mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos restrict ord_nonneg_of_mem mem_of_ord_nonneg finite_residueField_of_finiteDimensional"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

set_option maxHeartbeats 3200000 in

private theorem sub_value_mem_nonunits (w : Place K F) (A : ValuationSubring K)
    (f : w.compSubring A) :
    (f : F) - algebraMap K F (w.value A f : K) ∈ w.toValuationSubring.nonunits := by
  rcases eq_or_ne (f : F) (algebraMap K F (w.value A f : K)) with he | hne
  · rw [he, sub_self]
    exact zero_mem _
  · exact (w.mem_nonunits_iff_ord_pos (sub_ne_zero.mpr hne)).mpr (w.ord_sub_value_pos hne)

end Place
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ValuationSubring"
end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ValuationSubring"

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq jqN evalAtJ ModularPolynomialData jq_mem divisorExpansions mem_divisorExpansions modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange EvalSymm CharPModel.jBar CharPModel.jNBar CharPModel.FibreModel modularFunctionFieldBar HeckeAlphaBarIntegral HeckeBetaBarIntegral laurentMap_injective KroneckerCongruence CharPModel.chart_dichotomy_jBar transcendental_coeffEmb_jq transcendental_jqModC CharPModel.FibreModel.spPlace_d7_dictZero_of_t_small"
p2m_open "ModularCurve~jBar"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar jNBar constantsHom affineBaseFin affineBaseInf FibreModel chart_dichotomy_jBar FibreModel.spPlace_d7_dictZero_of_t_small"
p2m_open "ModularCurve.CharPModel"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve"

namespace FibreModel
p2m_open_scoped "ModularCurve.CharPModel.FibreModel" in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem _root_.ModularCurve.CharPModel.FibreModel.binf_le_compSubring {N : ℕ} [NeZero N]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ : ℕ} [Fact ℓ.Prime] {k : Type*}
    [Field k] [CharP k ℓ] {red : A →+* k} (fm : FibreModel N A ℓ k red)
    (w : Place (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
    (hwInf : ((jBar N)⁻¹ : laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionFieldFull N)) ∈ w.compSubring A) :
    fm.BInf ≤ (w.compSubring A : Subring (laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionFieldFull N))) := by
  have hS : affineBaseInf N A ≤ w.compSubring A := by
    refine Subring.closure_le.mpr ?_
    rintro x (⟨a, rfl⟩ | rfl)
    · exact (w.algebraMap_mem_compSubring_iff A _).mpr a.2
    · exact hwInf
  exact fun x hx => w.mem_compSubring_of_isIntegral' A hS (fm.integralInf ⟨x, hx⟩)

end FibreModel
p2m_export "ModularCurve.CharPModel" "FibreModel.binf_le_compSubring"
end CharPModel
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ValuationSubring"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ValuationSubring"

p2m_open "ModularCurve~jBar" in open _root_.P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve _root_.ModularCurve.CharPModel _root_.P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero.ModularCurve.CharPModel IsLocalRing in
set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 3200000 in

theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (_hsq : Squarefree N) (_hlN : ¬ ℓ ∣ N)
    (_data : ModularPolynomialData ℓ) (_hKr : KroneckerCongruence ℓ _data)
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (_halpha : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (_hbeta : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsym : EvalSymm (dataAll N (dvd_refl N)).Φ)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (fm : FibreModel N A ℓ k red) (cc : fm.CuspChart) :
    ∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (τ : A)
      (ht : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          / (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩ : modularFunctionFieldBar N) ^ N ∈
                  w.toValuationSubring),
    (∀ a : A,
      w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) ≤ 0) →
    IsLocalRing.residue w.toValuationSubring ⟨_, ht⟩
        = algebraMap (AlgebraicClosure ℚ) w.ResidueField (τ : AlgebraicClosure ℚ) →
      ⟨jqModC k, jqModC_mem k N⟩ / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^ N
          - algebraMap k (modularFunctionFieldC k N) (red τ) = 0 ∨
      0 < ((fm.spPlace hred dataAll hsep) w).ord
        (⟨jqModC k, jqModC_mem k N⟩ / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^
            N
          - algebraMap k (modularFunctionFieldC k N) (red τ)) := by
  intro w τ ht hpole hres
  classical
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)

  have hteq : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩ : modularFunctionFieldBar N)
      / (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N) ^ N
      = jNBar N * ((jBar N)⁻¹) ^ N := by
    rw [div_eq_mul_inv, inv_pow]; rfl
  have ht'eq : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
      / (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩ : modularFunctionFieldBar N) ^ N
      = jBar N * ((jNBar N)⁻¹) ^ N := by
    rw [div_eq_mul_inv, inv_pow]; rfl
  set T : modularFunctionFieldBar N := jNBar N * ((jBar N)⁻¹) ^ N with hT
  set T' : modularFunctionFieldBar N := jBar N * ((jNBar N)⁻¹) ^ N with hT'
  have ht2 : T' ∈ w.toValuationSubring := ht'eq ▸ ht
  have hres2 : IsLocalRing.residue w.toValuationSubring ⟨T', ht2⟩
      = algebraMap (AlgebraicClosure ℚ) w.ResidueField (τ : AlgebraicClosure ℚ) := by
    rw [← hres]
    congr 1
    exact Subtype.ext ht'eq.symm

  have hjne : (jBar N : modularFunctionFieldBar N) ≠ 0 := by
    have := jBar_sub_const_ne N 0
    simpa using this
  have hjNne : (jNBar N : modularFunctionFieldBar N) ≠ 0 := by
    have h1 := ModularCurve.CharPModel.jNBar_ne_const N (dataAll N (dvd_refl N)) hsym 0
    simpa using h1

  have hjnot : (jBar N : modularFunctionFieldBar N) ∉ w.compSubring A := by
    intro h
    have hvN : (jNBar N : modularFunctionFieldBar N) ∈ w.compSubring A :=
      fm.bfin_le_compSubring w h fm.jNBar_mem
    have ha₀ := w.ord_sub_value_pos (f := ⟨jNBar N, hvN⟩)
      (ModularCurve.CharPModel.jNBar_ne_const N (dataAll N (dvd_refl N)) hsym
        ((w.value A ⟨jNBar N, hvN⟩ : A) : AlgebraicClosure ℚ))
    exact absurd ha₀ (not_lt.mpr (hpole (w.value A ⟨jNBar N, hvN⟩)))

  have hjpole : ∀ a : A, w.ord ((jBar N : modularFunctionFieldBar N)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0 := by
    intro a
    by_contra hgt
    push Not at hgt
    exact hjnot (w.mem_compSubring_of_hasValueAt (A := A) a.2 (w.hasValueAt_of_ord_pos hgt))

  have hinvcomp : ((jBar N)⁻¹ : modularFunctionFieldBar N) ∈ w.compSubring A := by
    rcases ModularCurve.CharPModel.chart_dichotomy_jBar N A dataAll w with ⟨a, ha⟩ | ⟨a, ha⟩
    · exfalso
      have hne := jBar_sub_const_ne N (a : AlgebraicClosure ℚ)
      have hpos := (w.mem_nonunits_iff_ord_pos hne).mp ha
      exact absurd hpos (not_lt.mpr (hjpole a))
    · exact ⟨a, ha⟩

  have hbinf : (fm.BInf : Subring (modularFunctionFieldBar N)) ≤ (w.compSubring A : Subring _) :=
    fm.binf_le_compSubring w hinvcomp
  have htc : T ∈ w.compSubring A := hbinf cc.tBar_mem
  set ct : A := w.value A ⟨T, htc⟩ with hct

  have hT'val : w.HasValueAt T' (τ : AlgebraicClosure ℚ) :=
    (w.hasValueAt_iff_residue ht2 (τ : AlgebraicClosure ℚ)).mpr hres2
  have hT'c : T' ∈ w.compSubring A := ⟨τ, hT'val⟩
  have hvT' : w.value A ⟨T', hT'c⟩ = τ := w.value_eq_of_hasValueAt hT'val

  have huid : T * T' = (((jBar N) * (jNBar N))⁻¹ : modularFunctionFieldBar N) ^ (N - 1) := by
    rw [hT, hT']
    obtain ⟨m, hm⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    subst hm
    simp only [Nat.add_sub_cancel]
    exact AlgebraicCurve.Place.mul_inv_pow_succ_mul hjne hjNne m
  have hvmul : w.value A (⟨T, htc⟩ * ⟨T', hT'c⟩) = ct * τ := by
    rw [map_mul, hvT', hct]

  have hjLne := ModularCurve.CharPModel.jLine_ne_zero k N
  have hjNLne := ModularCurve.CharPModel.jNLine_ne_zero k N (dataAll N (dvd_refl N)) hsym
  have hjLne' : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ≠ 0 := hjLne
  have hjNLne' : (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ≠ 0 := hjNLne
  set v' := fm.spPlace hred dataAll hsep w with hv'

  have hshift : ∀ c : A, (T - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      (c : AlgebraicClosure ℚ)) ∈ w.toValuationSubring.nonunits →
      ((⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) / (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^ N
        - algebraMap k (modularFunctionFieldC k N) (red c)) ∈ v'.toValuationSubring.nonunits := by
    intro c hc
    have hmem := (fm.piInf_mem_spPlace_nonunits_iff hred dataAll hsep w hjpole
        (⟨T, cc.tBar_mem⟩ - ⟨constantsHom N A c, fm.constInf_mem c⟩)).mpr
      ⟨0, zero_mem (IsLocalRing.maximalIdeal A), by
        simpa [constantsHom, map_zero, sub_zero] using hc⟩
    have hpi : fm.piInf (⟨T, cc.tBar_mem⟩ - ⟨constantsHom N A c, fm.constInf_mem c⟩)
        = (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) / (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^ N
          - algebraMap k (modularFunctionFieldC k N) (red c) := by
      rw [map_sub, cc.piInf_t, fm.piInf_const]
      rw [div_eq_mul_inv, ← inv_pow]
    rwa [hpi] at hmem

  by_cases hmem : ((⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) / (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^ N : modularFunctionFieldC k N)
      ∈ v'.toValuationSubring.nonunits
  ·
    have hback := (fm.piInf_mem_spPlace_nonunits_iff hred dataAll hsep w hjpole
        ⟨T, cc.tBar_mem⟩).mp (by
      have hpi : fm.piInf (⟨T, cc.tBar_mem⟩ : fm.BInf)
          = (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) / (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^ N := by
        rw [cc.piInf_t, div_eq_mul_inv, inv_pow]
      rwa [hpi])
    obtain ⟨a, ha𝔪, hanu⟩ := hback
    refine ModularCurve.CharPModel.FibreModel.spPlace_d7_dictZero_of_t_small A ℓ N _hsq _hlN _data _hKr
      k red _halpha _hbeta hred dataAll hsym hsep fm cc w τ ht hpole hres ?_
    exact ⟨a, ha𝔪, by rw [hteq]; exact hanu⟩
  ·
    have hker𝔪 : ∀ a : A, red a = 0 → a ∈ IsLocalRing.maximalIdeal A := by
      intro a h0
      by_contra hnot
      have hu : IsUnit a := IsLocalRing.notMem_maximalIdeal.mp hnot
      have h2 : IsUnit (red a) := hu.map red
      rw [h0] at h2
      exact h2.ne_zero rfl
    have h𝔪ker : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A → red a = 0 := by
      intro a ha
      by_contra h0
      obtain ⟨b, hb⟩ := hred (red a)⁻¹
      have h1 : red (1 - a * b) = 0 := by
        rw [map_sub, map_one, map_mul, hb, mul_inv_cancel₀ h0, sub_self]
      have h2 := hker𝔪 _ h1
      have h3 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
        have h4 := Ideal.add_mem _ h2 (Ideal.mul_mem_right b _ ha)
        simp at h4
      exact ((Ideal.ne_top_iff_one _).mp
        (IsLocalRing.maximalIdeal.isMaximal A).ne_top) h3
    have hctne : red ct ≠ 0 := by
      intro h0
      have hstep := hshift ct (by
        simpa [hct] using AlgebraicCurve.Place.sub_value_mem_nonunits w A ⟨T, htc⟩)
      rw [h0, map_zero, sub_zero] at hstep
      exact hmem hstep

    have htilde : ((⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) / (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^ N
        - algebraMap k (modularFunctionFieldC k N) (red ct)) ∈ v'.toValuationSubring.nonunits :=
      hshift ct (by simpa [hct] using AlgebraicCurve.Place.sub_value_mem_nonunits w A ⟨T, htc⟩)
    have htval : v'.HasValueAt ((⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) / (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^ N) (red ct) := htilde
    have htinv := htval.inv hctne

    have hUd : ((⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) / (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^ N) * ((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^ N)
        = (((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) * (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N))⁻¹) ^ (N - 1) := by
      obtain ⟨m, hm⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
      subst hm
      simp only [Nat.add_sub_cancel]
      exact AlgebraicCurve.Place.div_pow_succ_mul_div_pow_succ hjLne' hjNLne' m

    have hpow : ∀ (m : ℕ) {f : modularFunctionFieldBar N} {a : AlgebraicClosure ℚ},
        w.HasValueAt f a → w.HasValueAt (f ^ m) (a ^ m) := by
      intro m
      induction m with
      | zero =>
        intro f a _
        simpa using w.hasValueAt_algebraMap 1
      | succ n ih =>
        intro f a hf
        rw [pow_succ, pow_succ]
        exact (ih hf).mul hf
    by_cases hτ : red τ = 0
    ·
      rcases Nat.lt_or_ge N 2 with hNlt | hN2
      ·
        exfalso
        have hexp : N - 1 = 0 := by omega
        have h2 := huid
        rw [hexp, pow_zero] at h2
        have h1 : (⟨T, htc⟩ * ⟨T', hT'c⟩ : w.compSubring A) = 1 := by
          apply Subtype.ext
          simpa using h2
        have hctτ : ct * τ = 1 := by rw [← hvmul, h1, map_one]
        have : red ct * red τ = 1 := by rw [← map_mul, hctτ, map_one]
        rw [hτ, mul_zero] at this
        exact zero_ne_one this
      ·
        have hjneg := ModularCurve.CharPModel.ord_jLine_neg_of_pole N A ℓ k red fm hred dataAll hsep w hjpole
        have hjNneg := sol_d0_jN_pole N A ℓ k red fm hred dataAll hsep hsym w hpole
        rw [hτ, map_zero, sub_zero]
        rcases eq_or_ne ((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^ N : modularFunctionFieldC k N) 0 with h0 | hne0
        · exact Or.inl h0
        · refine Or.inr ?_
          have hmulne : ((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) * (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) : modularFunctionFieldC k N) ≠ 0 :=
            mul_ne_zero hjLne' hjNLne'
          have htdne : ((⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) / (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^ N : modularFunctionFieldC k N) ≠ 0 :=
            div_ne_zero hjNLne' (pow_ne_zero _ hjLne')
          have hTd'eq : ((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^ N : modularFunctionFieldC k N)
              = (((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) * (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N))⁻¹) ^ (N - 1)
                * ((⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) / (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^ N)⁻¹ := by
            obtain ⟨m, hm⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
            subst hm
            simp only [Nat.add_sub_cancel]
            exact AlgebraicCurve.Place.div_pow_succ_eq_inv_pow_mul_inv hjLne' hjNLne' m
          have htinvO : (((⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) / (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^ N : modularFunctionFieldC k N)⁻¹)
              ∈ v'.toValuationSubring := by
            have h2 := v'.toValuationSubring.nonunits_subset htinv
            have h3 := add_mem h2 (v'.algebraMap_mem (red ct)⁻¹)
            simpa using h3
          have hUdord : 0 < v'.ord ((((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) * (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N))⁻¹) ^ (N - 1)) := by
            have h1 : v'.ord (((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) * (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N))⁻¹)
                = -(v'.ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) + v'.ord (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N)) := by
              rw [v'.ord_inv, v'.ord_mul hjLne' hjNLne']
            rw [← zpow_natCast, v'.ord_zpow, h1]
            have hb : 0 < -(v'.ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) + v'.ord (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N)) := by linarith
            have hc : (1 : ℤ) ≤ ((N - 1 : ℕ) : ℤ) := by
              have : 1 ≤ N - 1 := by omega
              exact_mod_cast this
            nlinarith
          rw [hTd'eq, v'.ord_mul (pow_ne_zero _ (inv_ne_zero hmulne)) (inv_ne_zero htdne)]
          have hordinv : 0 ≤ v'.ord (((⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) / (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^ N)⁻¹) :=
            ModularCurve.CharPModel.ord_nonneg_of_mem' _ (inv_ne_zero htdne) htinvO
          linarith
    ·
      rcases Nat.lt_or_ge N 2 with hNlt | hN2
      ·
        have hexp : N - 1 = 0 := by omega
        have h2 := huid
        rw [hexp, pow_zero] at h2
        have h1 : (⟨T, htc⟩ * ⟨T', hT'c⟩ : w.compSubring A) = 1 := by
          apply Subtype.ext
          simpa using h2
        have hctτ : ct * τ = 1 := by rw [← hvmul, h1, map_one]
        have hredeq : red ct * red τ = 1 := by rw [← map_mul, hctτ, map_one]
        have hτinv : red τ = (red ct)⁻¹ := by
          field_simp
          linear_combination hredeq
        have h3 := hUd
        rw [hexp, pow_zero] at h3
        have hTd'inv : ((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^ N : modularFunctionFieldC k N)
            = ((⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) / (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ^ N)⁻¹ := by
          exact eq_inv_of_mul_eq_one_right h3
        rcases eq_or_ne (((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^ N : modularFunctionFieldC k N)
            - algebraMap k _ (red τ)) 0 with h0 | hne0
        · exact Or.inl h0
        · refine Or.inr ?_
          have := (v'.hasValueAt_iff_ord_pos (sub_ne_zero.mp (by rwa [hTd'inv, hτinv] at hne0))).mp htinv
          rwa [hTd'inv, hτinv]
      ·
        exfalso
        have hv_unit : IsUnit (ct * τ) := by
          rw [← IsLocalRing.notMem_maximalIdeal]
          intro h𝔪
          have hk := h𝔪ker _ h𝔪
          rw [map_mul] at hk
          exact (mul_ne_zero hctne hτ) hk
        have huval : w.HasValueAt (T * T') ((ct * τ : A) : AlgebraicClosure ℚ) := by
          have h1 := w.hasValueAt_value A (⟨T, htc⟩ * ⟨T', hT'c⟩)
          rwa [hvmul] at h1
        have hvne : ((ct * τ : A) : AlgebraicClosure ℚ) ≠ 0 := by
          intro h0
          exact hv_unit.ne_zero (Subtype.ext h0)
        have huinvval := huval.inv hvne
        have huinv_eq : (T * T')⁻¹ = ((jBar N) * (jNBar N) : modularFunctionFieldBar N) ^ (N - 1) := by
          rw [huid, ← inv_pow, inv_inv]
        have hTne : T ≠ 0 := by
          rw [hT]
          exact mul_ne_zero hjNne (pow_ne_zero _ (inv_ne_zero hjne))
        have hT'ne : T' ≠ 0 := by
          rw [hT']
          exact mul_ne_zero hjne (pow_ne_zero _ (inv_ne_zero hjNne))
        have hprodval : w.HasValueAt (((jBar N) * (jNBar N) : modularFunctionFieldBar N) ^ (N - 1))
            ((ct * τ : A) : AlgebraicClosure ℚ)⁻¹ := by
          rw [← huinv_eq]
          exact huinvval

        have huordle : w.ord (T * T') ≤ 0 := by
          have hO : (((jBar N) * (jNBar N) : modularFunctionFieldBar N) ^ (N - 1))
              ∈ w.toValuationSubring := by
            have h2 := w.toValuationSubring.nonunits_subset hprodval
            have h3 := add_mem h2 (w.algebraMap_mem ((ct * τ : A) : AlgebraicClosure ℚ)⁻¹)
            simpa using h3
          have h4 : 0 ≤ w.ord ((T * T')⁻¹) := by
            rw [huinv_eq]
            exact ModularCurve.CharPModel.ord_nonneg_of_mem' _
              (by rw [← huinv_eq]; exact inv_ne_zero (mul_ne_zero hTne hT'ne)) hO
          rw [w.ord_inv] at h4
          linarith
        have huordge : 0 ≤ w.ord (T * T') := by
          have hO : (T * T') ∈ w.toValuationSubring := by
            have h2 := w.toValuationSubring.nonunits_subset huval
            have h3 := add_mem h2 (w.algebraMap_mem ((ct * τ : A) : AlgebraicClosure ℚ))
            simpa using h3
          exact ModularCurve.CharPModel.ord_nonneg_of_mem' _ (mul_ne_zero hTne hT'ne) hO
        have hordJJN : w.ord ((jBar N) * (jNBar N) : modularFunctionFieldBar N) = 0 := by
          have h1 : w.ord ((T * T')⁻¹) = 0 := by
            rw [w.ord_inv]
            omega
          rw [huinv_eq, ← zpow_natCast, w.ord_zpow] at h1
          have hNne : ((N - 1 : ℕ) : ℤ) ≠ 0 := by
            have : 1 ≤ N - 1 := by omega
            omega
          exact (mul_eq_zero.mp h1).resolve_left hNne
        have hjord : w.ord (jBar N : modularFunctionFieldBar N) = 0 ∧
            w.ord (jNBar N : modularFunctionFieldBar N) = 0 := by
          rw [w.ord_mul hjne hjNne] at hordJJN
          have h1 : w.ord (jBar N : modularFunctionFieldBar N) ≤ 0 := by simpa using hjpole 0
          have h2 : w.ord (jNBar N : modularFunctionFieldBar N) ≤ 0 := by have h__af := hpole 0; simp at h__af; exact h__af
          omega
        have hjO : (jBar N : modularFunctionFieldBar N) ∈ w.toValuationSubring :=
          ModularCurve.CharPModel.mem_of_ord_nonneg _ hjne (le_of_eq hjord.1.symm)
        have hjNO : (jNBar N : modularFunctionFieldBar N) ∈ w.toValuationSubring :=
          ModularCurve.CharPModel.mem_of_ord_nonneg _ hjNne (le_of_eq hjord.2.symm)
        have hw := AlgebraicCurve.Place.surj_residue_bar N dataAll w
        obtain ⟨cj, hcj⟩ := hw (IsLocalRing.residue w.toValuationSubring ⟨jBar N, hjO⟩)
        obtain ⟨cN, hcN⟩ := hw (IsLocalRing.residue w.toValuationSubring ⟨jNBar N, hjNO⟩)
        have hjval : w.HasValueAt (jBar N : modularFunctionFieldBar N) cj :=
          (w.hasValueAt_iff_residue hjO cj).mpr hcj.symm
        have hjNval : w.HasValueAt (jNBar N : modularFunctionFieldBar N) cN :=
          (w.hasValueAt_iff_residue hjNO cN).mpr hcN.symm
        have hcjA : cj ∉ A := by
          intro hmemA
          exact absurd ((w.hasValueAt_iff_ord_pos (sub_ne_zero.mp (jBar_sub_const_ne N cj))).mp hjval)
            (not_lt.mpr (hjpole ⟨cj, hmemA⟩))
        have hcNA : cN ∉ A := by
          intro hmemA
          exact absurd ((w.hasValueAt_iff_ord_pos
              (ModularCurve.CharPModel.jNBar_ne_const N (dataAll N (dvd_refl N)) hsym cN)).mp hjNval)
            (not_lt.mpr (hpole ⟨cN, hmemA⟩))
        have hcjinv : cj⁻¹ ∈ A ∧ (∀ hm : cj⁻¹ ∈ A, (⟨cj⁻¹, hm⟩ : A) ∈ IsLocalRing.maximalIdeal A) := by
          have hmem := (A.mem_or_inv_mem cj).resolve_left hcjA
          refine ⟨hmem, fun hm => ?_⟩
          by_contra hunit
          have hu : IsUnit (⟨cj⁻¹, hm⟩ : A) := IsLocalRing.notMem_maximalIdeal.mp hunit
          obtain ⟨u, hueq⟩ := hu
          have hne0 : cj ≠ 0 := fun h0 => hcjA (h0 ▸ A.zero_mem)
          have : cj ∈ A := by
            have h1 : (((u⁻¹ : (↥A)ˣ) : A) : AlgebraicClosure ℚ) * cj⁻¹ = 1 := by
              have h2 : ((u⁻¹ : (↥A)ˣ) : A) * ⟨cj⁻¹, hm⟩ = 1 := by
                rw [← hueq]
                exact u.inv_mul
              have h2' := congrArg Subtype.val h2
              simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h2'
              exact h2'
            have h3 : (((u⁻¹ : (↥A)ˣ) : A) : AlgebraicClosure ℚ) = cj := by
              field_simp at h1
              linear_combination h1
            exact h3 ▸ ((u⁻¹ : (↥A)ˣ) : A).2
          exact hcjA this
        have hcNinv : cN⁻¹ ∈ A ∧ (∀ hm : cN⁻¹ ∈ A, (⟨cN⁻¹, hm⟩ : A) ∈ IsLocalRing.maximalIdeal A) := by
          have hmem := (A.mem_or_inv_mem cN).resolve_left hcNA
          refine ⟨hmem, fun hm => ?_⟩
          by_contra hunit
          have hu : IsUnit (⟨cN⁻¹, hm⟩ : A) := IsLocalRing.notMem_maximalIdeal.mp hunit
          obtain ⟨u, hueq⟩ := hu
          have hne0 : cN ≠ 0 := fun h0 => hcNA (h0 ▸ A.zero_mem)
          have : cN ∈ A := by
            have h1 : (((u⁻¹ : (↥A)ˣ) : A) : AlgebraicClosure ℚ) * cN⁻¹ = 1 := by
              have h2 : ((u⁻¹ : (↥A)ˣ) : A) * ⟨cN⁻¹, hm⟩ = 1 := by
                rw [← hueq]
                exact u.inv_mul
              have h2' := congrArg Subtype.val h2
              simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h2'
              exact h2'
            have h3 : (((u⁻¹ : (↥A)ˣ) : A) : AlgebraicClosure ℚ) = cN := by
              field_simp at h1
              linear_combination h1
            exact h3 ▸ ((u⁻¹ : (↥A)ˣ) : A).2
          exact hcNA this

        have hequ : (cj * cN) ^ (N - 1) = ((ct * τ : A) : AlgebraicClosure ℚ)⁻¹ :=
          (hpow (N - 1) (hjval.mul hjNval)).unique hprodval

        have h𝔪elt : (⟨cj⁻¹, hcjinv.1⟩ * ⟨cN⁻¹, hcNinv.1⟩ : A) ^ (N - 1)
            ∈ IsLocalRing.maximalIdeal A := by
          have h1 : (⟨cj⁻¹, hcjinv.1⟩ * ⟨cN⁻¹, hcNinv.1⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
            have := hcjinv.2 hcjinv.1
            exact Ideal.mul_mem_right _ _ this
          exact Ideal.pow_mem_of_mem _ h1 _ (by omega)
        have hcoe_eq : ((ct * τ : A) : AlgebraicClosure ℚ)
            = (((⟨cj⁻¹, hcjinv.1⟩ * ⟨cN⁻¹, hcNinv.1⟩ : A) ^ (N - 1) : A) : AlgebraicClosure ℚ) := by
          have h2 : ((cj * cN) ^ (N - 1))⁻¹ = ((ct * τ : A) : AlgebraicClosure ℚ) := by
            rw [hequ, inv_inv]
          rw [← h2]
          push_cast
          rw [← inv_pow, mul_inv]
        have hctτ𝔪 : (ct * τ : A) ∈ IsLocalRing.maximalIdeal A := by
          have heq : (⟨cj⁻¹, hcjinv.1⟩ * ⟨cN⁻¹, hcNinv.1⟩ : A) ^ (N - 1) = ct * τ :=
            Subtype.ext hcoe_eq.symm
          rwa [heq] at h𝔪elt
        have hred0 : red (ct * τ) = 0 := h𝔪ker _ hctτ𝔪
        rw [map_mul] at hred0
        exact (mul_ne_zero hctne hτ) hred0

end
end
end S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero (solution)
