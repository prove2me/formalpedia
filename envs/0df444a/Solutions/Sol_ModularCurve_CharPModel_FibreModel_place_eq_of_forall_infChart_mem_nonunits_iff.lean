-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.place_eq_of_forall_infChart_mem_nonunits_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/95a73e02-405c-5b50-ba23-8c75a2c9a8b3

import Definitions.Def_ModularCurve_SpecializationMap
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel"
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.AlgebraicCurve"
open Polynomial
open IsLocalRing

noncomputable section

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd ModularPolynomialData CharPModel.FibreModel laurentMap_injective transcendental_jqModC"
p2m_open "ModularCurve"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar jNBar constantsHom affineBaseFin affineBaseInf FibreModel"
p2m_open "ModularCurve.CharPModel"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.AlgebraicCurve"

variable (N : ℕ) [NeZero N]

variable (A : ValuationSubring (AlgebraicClosure ℚ))

end CharPModel
end ModularCurve

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd ModularPolynomialData CharPModel.FibreModel laurentMap_injective transcendental_jqModC"
p2m_open "ModularCurve"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar jNBar constantsHom affineBaseFin affineBaseInf FibreModel"
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

end FibreEval
end CharPModel
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve"
namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd ModularPolynomialData CharPModel.FibreModel laurentMap_injective transcendental_jqModC"
p2m_open "ModularCurve"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar jNBar constantsHom affineBaseFin affineBaseInf FibreModel"
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
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve"

section BarFinDim

end BarFinDim
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve"
end CharPModel
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve"
set_option autoImplicit false
open Polynomial
namespace ValuationSubring
p2m_export "ValuationSubring" "comap subtype coe_mem_nonunits_iff mem_comap toSubring algebraMap_apply ext nonunits mem_nonunits_iff mem_top eq_of_le_of_ne_top mul_mem add_mem eq_top_iff valuation_le_one_iff algebra valuation inclusion"
p2m_open "ValuationSubring"
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (A : ValuationSubring K)
end ValuationSubring
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve"
namespace Subring
p2m_export "Subring" "mem_bot topEquiv inclusion subtype ext mem_top map mem_comap closure comap"
p2m_open "Subring"
variable {F : Type*} [Field F]
end Subring
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve"
set_option autoImplicit false
open IsLocalRing
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ne_top' algebraMap_mem' toValuationSubring"
p2m_open "AlgebraicCurve.Place"
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)
variable (A : ValuationSubring K)
end Place
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve"
end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve"
set_option autoImplicit false
namespace ValuationSubring
p2m_export "ValuationSubring" "comap subtype coe_mem_nonunits_iff mem_comap toSubring algebraMap_apply ext nonunits mem_nonunits_iff mem_top eq_of_le_of_ne_top mul_mem add_mem eq_top_iff valuation_le_one_iff algebra valuation inclusion"
p2m_open "ValuationSubring"
variable {K : Type*} [Field K] (A : ValuationSubring K)
section Quotient
open Polynomial
variable {F : Type*} [Field F] [Algebra K F]
variable {A}
end Quotient
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve"
end ValuationSubring
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve"
set_option autoImplicit false
open IsLocalRing IsDedekindDomain
namespace Subring
p2m_export "Subring" "mem_bot topEquiv inclusion subtype ext mem_top map mem_comap closure comap"
p2m_open "Subring"
variable {F : Type*} [Field F] {B : Subring F}
end Subring
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve"
namespace ValuationSubring
p2m_export "ValuationSubring" "comap subtype coe_mem_nonunits_iff mem_comap toSubring algebraMap_apply ext nonunits mem_nonunits_iff mem_top eq_of_le_of_ne_top mul_mem add_mem eq_top_iff valuation_le_one_iff algebra valuation inclusion"
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
private theorem mem_centreOver_iff (hO : ∀ r : R, algebraMap R F r ∈ O) {r : R} :
    r ∈ O.centreOver hO ↔ algebraMap R F r ∈ O.nonunits := by
  rw [centreOver, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

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
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ValuationSubring"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ne_top' algebraMap_mem' toValuationSubring"
p2m_open "AlgebraicCurve.Place"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
end Place
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ValuationSubring"
end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ValuationSubring"
set_option autoImplicit false
open IsLocalRing Polynomial
namespace Valuation
p2m_export "Valuation" "map_add' ext map integer comap"
p2m_open "Valuation"
variable {R Γ₀ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
end Valuation
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ValuationSubring"
namespace ValuationSubring
p2m_export "ValuationSubring" "comap subtype coe_mem_nonunits_iff mem_comap toSubring algebraMap_apply ext nonunits mem_nonunits_iff mem_top eq_of_le_of_ne_top mul_mem add_mem eq_top_iff valuation_le_one_iff algebra valuation inclusion"
p2m_open "ValuationSubring"
variable {K : Type*} [Field K] (A : ValuationSubring K)
variable {k : Type*} [Field k]
end ValuationSubring
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ValuationSubring"
set_option autoImplicit false
open scoped IntermediateField.algebraAdjoinAdjoin
open IntermediateField Polynomial
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext"
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

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ValuationSubring"
set_option autoImplicit false
open Polynomial
namespace ValuationSubring
p2m_export "ValuationSubring" "comap subtype coe_mem_nonunits_iff mem_comap toSubring algebraMap_apply ext nonunits mem_nonunits_iff mem_top eq_of_le_of_ne_top mul_mem add_mem eq_top_iff valuation_le_one_iff algebra valuation inclusion"
p2m_open "ValuationSubring"
variable {K : Type*} [Field K] (A : ValuationSubring K) {k : Type*} [Field k]
end ValuationSubring
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ValuationSubring"
set_option autoImplicit false
namespace RingHom
p2m_export "RingHom" "coe_comp inverse IsIntegral surjective ext comp_apply toAddMonoidHom mem_range codRestrict injective_int ker range comp toNonUnitalRingHom"
p2m_open "RingHom"
variable {B C : Type*} [CommRing B] [CommRing C] (π : B →+* C)
end RingHom
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ValuationSubring"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ne_top' algebraMap_mem' toValuationSubring"
p2m_open "AlgebraicCurve.Place"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
end Place
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ValuationSubring"
end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ValuationSubring"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ne_top' algebraMap_mem' toValuationSubring"
p2m_open "AlgebraicCurve.Place"
variable {K E : Type*} [Field K] [Field E] [Algebra K E]

private theorem _root_.IntermediateField.adjoin_simple_inv_eq (x : E) :
    IntermediateField.adjoin K ({x⁻¹} : Set E) = IntermediateField.adjoin K ({x} : Set E) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self K x)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have h := inv_mem (IntermediateField.mem_adjoin_simple_self K x⁻¹)
    rwa [inv_inv] at h

p2m_alias "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.IntermediateField.adjoin_simple_inv_eq" "IntermediateField.adjoin_simple_inv_eq"
end Place
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ValuationSubring"
end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ValuationSubring"
namespace ValuationSubring
p2m_export "ValuationSubring" "comap subtype coe_mem_nonunits_iff mem_comap toSubring algebraMap_apply ext nonunits mem_nonunits_iff mem_top eq_of_le_of_ne_top mul_mem add_mem eq_top_iff valuation_le_one_iff algebra valuation inclusion"
p2m_open "ValuationSubring"
variable {F : Type*} [Field F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]

private theorem eq_of_forall_mem_nonunits_iff {O₁ O₂ : ValuationSubring F}
    (h₁ : ∀ r : R, algebraMap R F r ∈ O₁) (hne₁ : O₁ ≠ ⊤)
    (h₂ : ∀ r : R, algebraMap R F r ∈ O₂) (hne₂ : O₂ ≠ ⊤)
    (h : ∀ r : R, algebraMap R F r ∈ O₁.nonunits ↔ algebraMap R F r ∈ O₂.nonunits) :
    O₁ = O₂ := by
  have hc : O₁.centreHeightOneSpectrum h₁ hne₁ = O₂.centreHeightOneSpectrum h₂ hne₂ := by
    ext r
    change r ∈ O₁.centreOver h₁ ↔ r ∈ O₂.centreOver h₂
    rw [mem_centreOver_iff, mem_centreOver_iff]
    exact h r
  rw [O₁.eq_valuationSubringAtPrime_centre h₁ hne₁, O₂.eq_valuationSubringAtPrime_centre h₂ hne₂,
    hc]

end ValuationSubring
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ValuationSubring"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ne_top' algebraMap_mem' toValuationSubring"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem _root_.AlgebraicCurve.Place.eq_of_forall_mem_nonunits_iff (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Algebra R F] [IsFractionRing R F] {v₁ v₂ : Place K F}
    (h₁ : ∀ r : R, algebraMap R F r ∈ v₁.toValuationSubring)
    (h₂ : ∀ r : R, algebraMap R F r ∈ v₂.toValuationSubring)
    (h : ∀ r : R, algebraMap R F r ∈ v₁.toValuationSubring.nonunits ↔
      algebraMap R F r ∈ v₂.toValuationSubring.nonunits) : v₁ = v₂ :=
  Place.ext (ValuationSubring.eq_of_forall_mem_nonunits_iff h₁ v₁.ne_top' h₂ v₂.ne_top' h)

p2m_export "AlgebraicCurve.Place" "eq_of_forall_mem_nonunits_iff"

private theorem eq_of_forall_mem_nonunits_iff_of_surjective (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Algebra R F] [IsFractionRing R F] {v₁ v₂ : Place K F}
    (h₁ : ∀ r : R, algebraMap R F r ∈ v₁.toValuationSubring)
    (h₂ : ∀ r : R, algebraMap R F r ∈ v₂.toValuationSubring)
    {ι : Type*} (f : ι → F) (hsurj : ∀ r : R, ∃ i, f i = algebraMap R F r)
    (h : ∀ i, f i ∈ v₁.toValuationSubring.nonunits ↔ f i ∈ v₂.toValuationSubring.nonunits) :
    v₁ = v₂ :=
  eq_of_forall_mem_nonunits_iff R h₁ h₂ fun r => by
    obtain ⟨i, hi⟩ := hsurj r
    rw [← hi]
    exact h i

variable (K) in

private theorem integralClosure_adjoin_le_of_forall_isIntegral_mem {j : F} {S : Subring F}
    (hK : ∀ c : K, algebraMap K F c ∈ S) (hj : j ∈ S)
    (hS : ∀ x : F, (∃ p : Polynomial S, p.Monic ∧ Polynomial.eval₂ S.subtype x p = 0) → x ∈ S)
    (r : integralClosure (Algebra.adjoin K ({j} : Set F)) F) : (r : F) ∈ S := by

  let S' : Subalgebra K F := { S with algebraMap_mem' := hK }
  have hle : Algebra.adjoin K ({j} : Set F) ≤ S' := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hj)
  let φ : Algebra.adjoin K ({j} : Set F) →+* S :=
    (Subalgebra.val _).toRingHom.codRestrict S (fun y => hle y.2)

  obtain ⟨p, hp, hpr⟩ : IsIntegral (Algebra.adjoin K ({j} : Set F)) (r : F) := r.2
  refine hS r ⟨p.map φ, hp.map φ, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hpr

private theorem exists_eq_of_integralClosure_adjoin {j : F} {B : Type*} (π : B → F) {S : Subring F}
    (hrange : ∀ x, x ∈ S ↔ ∃ b, π b = x)
    (hK : ∀ c : K, algebraMap K F c ∈ S) (hj : j ∈ S)
    (hS : ∀ x : F, (∃ p : Polynomial S, p.Monic ∧ Polynomial.eval₂ S.subtype x p = 0) → x ∈ S)
    (r : integralClosure (Algebra.adjoin K ({j} : Set F)) F) :
    ∃ b, π b = algebraMap (integralClosure (Algebra.adjoin K ({j} : Set F)) F) F r :=
  (hrange r).mp (integralClosure_adjoin_le_of_forall_isIntegral_mem K hK hj hS r)

end Place
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ValuationSubring"

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ValuationSubring"

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd ModularPolynomialData CharPModel.FibreModel laurentMap_injective transcendental_jqModC"
p2m_open "ModularCurve"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar jNBar constantsHom affineBaseFin affineBaseInf FibreModel"
p2m_open "ModularCurve.CharPModel"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.AlgebraicCurve AlgebraicCurve.Place P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.AlgebraicCurve.Place"

section SolWork

variable {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {ℓ : ℕ} [Fact ℓ.Prime] {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}

private noncomputable def lineClosure (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    Subalgebra (Algebra.adjoin k ({jLine k N} : Set (modularFunctionFieldC k N)))
      (modularFunctionFieldC k N) :=
  integralClosure (Algebra.adjoin k ({jLine k N} : Set (modularFunctionFieldC k N)))
    (modularFunctionFieldC k N)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem transcendental_jLineInv (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    Transcendental k (((jLine k N)⁻¹ : modularFunctionFieldC k N)) := by
  intro h
  exact transcendental_jLine k N (by simpa using h.inv)

private noncomputable def lineClosureInf (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    Subalgebra (Algebra.adjoin k (({(jLine k N)⁻¹} : Set (modularFunctionFieldC k N))))
      (modularFunctionFieldC k N) :=
  integralClosure (Algebra.adjoin k (({(jLine k N)⁻¹} : Set (modularFunctionFieldC k N))))
    (modularFunctionFieldC k N)

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve _root_.ModularCurve.CharPModel _root_.P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel IsLocalRing in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 3200000 in

theorem _root_.P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (fm : ModularCurve.CharPModel.FibreModel N A ℓ k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularCurve.ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (v₁ v₂ : Place k (modularFunctionFieldC k N))
    (hj₁ : ((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N))⁻¹
      ∈ v₁.toValuationSubring)
    (hj₂ : ((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N))⁻¹
      ∈ v₂.toValuationSubring)
    (hagree : ∀ b : fm.BInf,
      ((fm.piInf b : modularFunctionFieldC k N) ∈ v₁.toValuationSubring.nonunits ↔
        (fm.piInf b : modularFunctionFieldC k N) ∈ v₂.toValuationSubring.nonunits)) :
    v₁ = v₂ := by
  classical
  have hjeq : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) = jLine k N := rfl
  rw [hjeq] at hj₁ hj₂
  have hconstR : ∀ c : k,
      algebraMap k (modularFunctionFieldC k N) c ∈ fm.piInf.range := by
    intro c
    obtain ⟨a, rfl⟩ := hred c
    exact ⟨⟨constantsHom N A a, fm.constInf_mem a⟩, (fm.piInf_const a).symm ▸ rfl⟩
  haveI hSepLine : Algebra.IsSeparable
      (IntermediateField.adjoin k (({(jLine k N)⁻¹} : Set (modularFunctionFieldC k N))))
      (modularFunctionFieldC k N) := by
    rw [IntermediateField.adjoin_simple_inv_eq (jLine k N)]
    exact isSeparable_line_fibre k N (dataAll N (dvd_refl N)) hsep
  haveI hFDLine : FiniteDimensional
      (IntermediateField.adjoin k (({(jLine k N)⁻¹} : Set (modularFunctionFieldC k N))))
      (modularFunctionFieldC k N) := by
    rw [IntermediateField.adjoin_simple_inv_eq (jLine k N)]
    exact finiteDimensional_adjoin_jC k N (dataAll N (dvd_refl N))
  haveI hDed : IsDedekindDomain (lineClosureInf k N) :=
    isDedekindDomain_integralClosure_adjoin (K := k)
      (F := modularFunctionFieldC k N) (transcendental_jLineInv k N)
  haveI hFrac : IsFractionRing (lineClosureInf k N) (modularFunctionFieldC k N) :=
    isFractionRing_integralClosure_adjoin (K := k)
      (F := modularFunctionFieldC k N) (transcendental_jLineInv k N)
  exact AlgebraicCurve.Place.eq_of_forall_mem_nonunits_iff_of_surjective
    (lineClosureInf k N)
    (fun r => integralClosure_adjoin_le_valuationSubring _
      (fun c => v₁.algebraMap_mem' c) hj₁ r)
    (fun r => integralClosure_adjoin_le_valuationSubring _
      (fun c => v₂.algebraMap_mem' c) hj₂ r)
    (fun b : fm.BInf => (fm.piInf b : modularFunctionFieldC k N))
    (AlgebraicCurve.Place.exists_eq_of_integralClosure_adjoin
      (fun b : fm.BInf => (fm.piInf b : modularFunctionFieldC k N))
      (fun x => RingHom.mem_range) hconstR
      ⟨⟨(jBar N)⁻¹, fm.jInvBar_mem⟩, fm.piInf_jInv⟩ fm.intClosed_piInf)
    (fun b => hagree b)

end SolWork
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ValuationSubring"
end CharPModel
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ValuationSubring"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ValuationSubring"

end
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff.ValuationSubring"

end
end
end S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff (solution)
