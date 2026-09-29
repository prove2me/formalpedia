-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.spPlace_d0_jN
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/5c6e8057-72cf-5b10-afc2-4dbc59a0a1be

import Definitions.Def_ModularCurve_SpecializationMap
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

p2m_open "ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve.CharPModel"
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.AlgebraicCurve"
open Polynomial
open IsLocalRing

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq jqN evalAtJ ModularPolynomialData modularFunctionFieldFull jqd_mem_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange EvalSymm CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.FibreModel modularFunctionFieldBar laurentMap_injective transcendental_coeffEmb_jq transcendental_jqModC"
p2m_open "ModularCurve"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar jNBar constantsHom affineBaseFin FibreModel"
p2m_open "ModularCurve.CharPModel"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.AlgebraicCurve AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.AlgebraicCurve.Place"

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
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve.CharPModel"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq jqN evalAtJ ModularPolynomialData modularFunctionFieldFull jqd_mem_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange EvalSymm CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.FibreModel modularFunctionFieldBar laurentMap_injective transcendental_coeffEmb_jq transcendental_jqModC"
p2m_open "ModularCurve"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar jNBar constantsHom affineBaseFin FibreModel"
p2m_open "ModularCurve.CharPModel"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.AlgebraicCurve AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.AlgebraicCurve.Place"

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
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve"

end CharPModel
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve"

noncomputable section

open IsLocalRing

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place IsCurveOver"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg ord ord_inv exists_unit_mul_zpow algebraMap_mem' toValuationSubring mem_of_eval_monic_eq_zero mem_maximalIdeal_iff_ord_pos ord_nonneg_of_mem mem_of_ord_nonneg"
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
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.AlgebraicCurve.Place"

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.AlgebraicCurve"

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq jqN evalAtJ ModularPolynomialData modularFunctionFieldFull jqd_mem_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange EvalSymm CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.FibreModel modularFunctionFieldBar laurentMap_injective transcendental_coeffEmb_jq transcendental_jqModC"
p2m_open "ModularCurve"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar jNBar constantsHom affineBaseFin FibreModel"
p2m_open "ModularCurve.CharPModel"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.AlgebraicCurve AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.AlgebraicCurve.Place"

section SolWork

variable {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {ℓ : ℕ} [Fact ℓ.Prime] {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}

namespace FibreModel p2m_export "ModularCurve.CharPModel.FibreModel" "spPlace piFin_mem_spPlace_nonunits_iff constFin_mem integralFin piFin_const jNBar_mem piFin_jN BFin" end FibreModel
p2m_open_scoped "ModularCurve.CharPModel.FibreModel" in
private theorem FibreModel.bfin_le_compSubring (fm : FibreModel N A ℓ k red)
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

end SolWork
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.AlgebraicCurve"
end CharPModel
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.AlgebraicCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.AlgebraicCurve"

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq jqN evalAtJ ModularPolynomialData modularFunctionFieldFull jqd_mem_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange EvalSymm CharPModel.jBar CharPModel.jNBar CharPModel.constantsHom CharPModel.FibreModel modularFunctionFieldBar laurentMap_injective transcendental_coeffEmb_jq transcendental_jqModC"
p2m_open "ModularCurve"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar jNBar constantsHom affineBaseFin FibreModel"
p2m_open "ModularCurve.CharPModel"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.AlgebraicCurve AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.AlgebraicCurve.Place"

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

end CharPModel
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.AlgebraicCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN.AlgebraicCurve"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (N : ℕ) [NeZero N]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] (k : Type*)
    [Field k] [CharP k ℓ] (red : A →+* k)
    (fm : ModularCurve.CharPModel.FibreModel N A ℓ k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularCurve.ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (hsym : ModularCurve.EvalSymm (dataAll N (dvd_refl N)).Φ) :
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∀ a : A,
    0 < w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) →
    0 < ((fm.spPlace hred dataAll hsep) w).ord
        (⟨jqNModC k N, jqNModC_mem k N⟩
          - algebraMap k (modularFunctionFieldC k N) (red a)) := by
  intro w a hord
  by_cases hfin : ∃ a₀ : A, 0 < w.ord
      ((ModularCurve.CharPModel.jBar N : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          (a₀ : AlgebraicClosure ℚ))
  · obtain ⟨a₀, ha₀⟩ := hfin
    have hbne : ((ModularCurve.CharPModel.jNBar N : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          (a : AlgebraicClosure ℚ)) ≠ 0 :=
      sub_ne_zero.mpr (jNBar_ne_const N (dataAll N (dvd_refl N)) hsym _)
    have hnu : ((ModularCurve.CharPModel.jNBar N : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          (a : AlgebraicClosure ℚ)) ∈ w.toValuationSubring.nonunits :=
      (w.mem_nonunits_iff_ord_pos hbne).mpr hord
    have hdict := (fm.piFin_mem_spPlace_nonunits_iff hred dataAll hsep w a₀ ha₀
        (⟨ModularCurve.CharPModel.jNBar N, fm.jNBar_mem⟩
          - ⟨ModularCurve.CharPModel.constantsHom N A a, fm.constFin_mem a⟩)).mpr
      ⟨0, (IsLocalRing.maximalIdeal A).zero_mem, by
        first | simpa using hnu | (simp at hnu ⊢; exact hnu) | (simp; exact hnu) | exact hnu⟩
    rw [map_sub, fm.piFin_jN, fm.piFin_const] at hdict
    have hlne : ((⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N)
        - algebraMap k (modularFunctionFieldC k N) (red a)) ≠ 0 :=
      sub_ne_zero.mpr (jNLine_ne_const k N (dataAll N (dvd_refl N)) hsym (red a))
    exact ((fm.spPlace hred dataAll hsep w).mem_nonunits_iff_ord_pos hlne).mp hdict
  · push Not at hfin
    exfalso
    have hbne : ((ModularCurve.CharPModel.jNBar N : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
        - algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
          (a : AlgebraicClosure ℚ)) ≠ 0 :=
      sub_ne_zero.mpr (jNBar_ne_const N (dataAll N (dvd_refl N)) hsym _)
    have hvN : (ModularCurve.CharPModel.jNBar N : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ∈ w.compSubring A := by
      refine w.mem_compSubring_of_hasValueAt a.2 ?_
      rw [AlgebraicCurve.Place.hasValueAt_iff]
      exact (w.mem_nonunits_iff_ord_pos hbne).mpr hord
    have hS : Subring.closure (Set.range ((algebraMap (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))).comp
          A.subtype) ∪ {ModularCurve.CharPModel.jNBar N}) ≤ w.compSubring A := by
      refine Subring.closure_le.mpr ?_
      rintro x (⟨a', rfl⟩ | rfl)
      · exact (w.algebraMap_mem_compSubring_iff A _).mpr a'.2
      · exact hvN
    have hjmem : (ModularCurve.CharPModel.jBar N : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ∈ w.compSubring A := by
      refine w.mem_compSubring_of_isIntegral' A hS ?_
      refine ⟨(dataAll N (dvd_refl N)).Φ.map
        ((Polynomial.aeval (R := ℤ)
          (⟨jNBar N, Subring.subset_closure (Set.mem_union_right _ rfl)⟩ :
            Subring.closure (Set.range ((algebraMap (AlgebraicClosure ℚ)
              (laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionFieldFull N))).comp A.subtype) ∪ {jNBar N}))).toRingHom),
        (dataAll N (dvd_refl N)).monic.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have hcomp : ((algebraMap
          (Subring.closure (Set.range ((algebraMap (AlgebraicClosure ℚ)
            (laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionFieldFull N))).comp A.subtype) ∪ {jNBar N}))
          (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))).comp
          ((Polynomial.aeval (R := ℤ)
            (⟨jNBar N, Subring.subset_closure (Set.mem_union_right _ rfl)⟩ :
              Subring.closure (Set.range ((algebraMap (AlgebraicClosure ℚ)
                (laurentBaseChange (AlgebraicClosure ℚ)
                  (modularFunctionFieldFull N))).comp A.subtype) ∪ {jNBar N}))).toRingHom))
          = (Polynomial.aeval (R := ℤ) (jNBar N)).toRingHom := by
        apply Polynomial.ringHom_ext
        · intro b
          simp only [eq_intCast, map_intCast]
        · rw [RingHom.comp_apply]
          rw [show (Polynomial.aeval (R := ℤ)
              (⟨jNBar N, Subring.subset_closure (Set.mem_union_right _ rfl)⟩ :
                Subring.closure (Set.range ((algebraMap (AlgebraicClosure ℚ)
                  (laurentBaseChange (AlgebraicClosure ℚ)
                    (modularFunctionFieldFull N))).comp A.subtype) ∪ {jNBar N}))).toRingHom
              Polynomial.X
              = (⟨jNBar N, Subring.subset_closure (Set.mem_union_right _ rfl)⟩ :
                Subring.closure (Set.range ((algebraMap (AlgebraicClosure ℚ)
                  (laurentBaseChange (AlgebraicClosure ℚ)
                    (modularFunctionFieldFull N))).comp A.subtype) ∪ {jNBar N}))
            from Polynomial.aeval_X _]
          rw [show (Polynomial.aeval (R := ℤ) (jNBar N)).toRingHom Polynomial.X = jNBar N
            from Polynomial.aeval_X _]
          rfl
      rw [hcomp]
      exact ModularCurve.CharPModel.barEvalSwap_subtype N (dataAll N (dvd_refl N)) hsym

    have hpos := w.ord_sub_value_pos (f := ⟨ModularCurve.CharPModel.jBar N, hjmem⟩)
      (jBar_ne_const N (w.value A ⟨ModularCurve.CharPModel.jBar N, hjmem⟩ : AlgebraicClosure ℚ))
    exact absurd hpos (not_lt.mpr (hfin (w.value A ⟨ModularCurve.CharPModel.jBar N, hjmem⟩)))

end
end S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d0_jN (solution)
