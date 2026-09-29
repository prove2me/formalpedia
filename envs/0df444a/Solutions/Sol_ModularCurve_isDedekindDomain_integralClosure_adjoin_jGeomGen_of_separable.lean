-- Prove2me | solution 1 for ModularCurve.isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/2749bb08-0421-5596-bf1d-88885e088053

import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable.ModularCurve"

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "jGeomGen qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jNum constantCoeff_jNum jNumQ jq ofPowerSeries_coeff_of_neg jqN evalAtJ ModularPolynomialData jq_mem modularFunctionFieldFull modularFunctionField_le_full jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem laurentMap_injective coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange EvalSymm"
p2m_open "ModularCurve"
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

private theorem laurentMap_injective {f : R →+* S} (hf : Function.Injective f) {x y : LaurentSeries
    R}
    (h : x.map f = y.map f) : x = y := by
  ext g
  have hg := congrArg (fun z : LaurentSeries S => z.coeff g) h
  simpa only [HahnSeries.map_coeff] using hf hg

private theorem map_eval₂Bivar (Φ : Polynomial (Polynomial ℤ)) (f : R →+* S) (u v : LaurentSeries R)
    :
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
p2m_reactivate "P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable.ModularCurve.CharPModel"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable.ModularCurve.CharPModel P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable.ModularCurve.CharPModel P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable.ModularCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "jGeomGen qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jNum constantCoeff_jNum jNumQ jq ofPowerSeries_coeff_of_neg jqN evalAtJ ModularPolynomialData jq_mem modularFunctionFieldFull modularFunctionField_le_full jqModC jqNModC map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem laurentMap_injective coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange EvalSymm"
p2m_open "ModularCurve"
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

private theorem tjq_pow (K : Type*) [CommRing K] (n : ℕ) :
    (jqModC K) ^ n = HahnSeries.single (-(n : ℤ)) 1 *
      HahnSeries.ofPowerSeries ℤ K ((jNum.map (Int.castRingHom K)) ^ n) := by
  have h : n • (-1 : ℤ) = -(n : ℤ) := by simp
  rw [jqModC, mul_pow, HahnSeries.single_pow, one_pow, h, ← map_pow]

private theorem tjq_constantCoeff_map (K : Type*) [CommRing K] :
    PowerSeries.constantCoeff (jNum.map (Int.castRingHom K)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum, map_one]

private theorem tjq_coeff_pow_self (K : Type*) [CommRing K] (n : ℕ) :
    ((jqModC K) ^ n).coeff (-(n : ℤ)) = 1 := by
  rw [tjq_pow, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, neg_add_cancel,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff, map_pow, tjq_constantCoeff_map, one_pow]

private theorem tjq_coeff_pow_of_lt (K : Type*) [CommRing K] {n : ℕ} {m : ℤ}
    (hm : m < -(n : ℤ)) : ((jqModC K) ^ n).coeff m = 0 := by
  rw [tjq_pow, HahnSeries.coeff_single_mul, one_mul]
  exact ofPowerSeries_coeff_of_neg _ (by omega)

private theorem tjq_algebraMap_eq_single (K : Type*) [CommRing K] (c : K) :
    algebraMap K (LaurentSeries K) c = HahnSeries.single 0 c := by
  have h1 : algebraMap K (PowerSeries K) c = PowerSeries.C c := by simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
  rfl

private theorem tjq_aeval_eq_zero (K : Type*) [CommRing K] {p : Polynomial K}
    (hp : Polynomial.aeval (jqModC K) p = 0) : p = 0 := by
  by_contra hp0
  set n := p.natDegree with hn
  have hcoeff : (Polynomial.aeval (jqModC K) p).coeff (-(n : ℤ)) = p.coeff n := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum,
      Finset.sum_eq_single n]
    · rw [tjq_algebraMap_eq_single, HahnSeries.coeff_single_zero_mul,
        tjq_coeff_pow_self, mul_one]
    · intro i hi hin
      have hilt : i < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hin
      rw [tjq_algebraMap_eq_single, HahnSeries.coeff_single_zero_mul,
        tjq_coeff_pow_of_lt, mul_zero]
      omega
    · intro hn'
      exact absurd (Finset.self_mem_range_succ n) hn'
  rw [hp] at hcoeff
  simp only [HahnSeries.coeff_zero] at hcoeff
  exact hp0 (Polynomial.leadingCoeff_eq_zero.mp hcoeff.symm)

private theorem tjq_transcendental (K : Type*) [CommRing K] :
    Transcendental K (jqModC K) :=
  transcendental_iff.mpr fun _ hp => tjq_aeval_eq_zero K hp

private theorem coeffEmb_jq_eq_jqModC :
    coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
  have hmap : jNumQ.map (algebraMap ℚ (AlgebraicClosure ℚ))
      = jNum.map (Int.castRingHom (AlgebraicClosure ℚ)) := by
    ext n
    simp [jNumQ, PowerSeries.coeff_map]
  rw [jq, jqModC, map_mul]
  congr 1
  · ext k
    rw [coeffEmb_coeff]
    by_cases hk : k = (-1 : ℤ) <;> simp [hk]
  · ext k
    rw [coeffEmb_coeff]
    by_cases hk : 0 ≤ k
    · lift k to ℕ using hk
      rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
        ← hmap, PowerSeries.coeff_map]
    · rw [ofPowerSeries_coeff_of_neg _ (by omega), ofPowerSeries_coeff_of_neg _ (by omega),
        map_zero]

section ResidueFieldInline

variable {K₀ F₀ F₀' : Type*} [Field K₀] [Field F₀] [Field F₀'] [Algebra K₀ F₀] [Algebra K₀ F₀']
  [Algebra F₀ F₀'] [IsScalarTower K₀ F₀ F₀'] [FiniteDimensional F₀ F₀']

open IsLocalRing in
private theorem rf_linearIndependent_lift (w : AlgebraicCurve.Place K₀ F₀') {ι : Type*}
    [Fintype ι] (x : ι → w.toValuationSubring)
    (hx : LinearIndependent (w.restrict F₀).ResidueField
      fun i => (residue w.toValuationSubring (x i) : w.ResidueField)) :
    LinearIndependent F₀ fun i => ((x i : w.toValuationSubring) : F₀') := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  obtain ⟨i₀, hi₀⟩ : ∃ i, g i ≠ 0 := not_forall.mp hne
  set O : ValuationSubring F₀ := (w.restrict F₀).toValuationSubring
  have hne' : (Finset.univ.filter fun i => g i ≠ 0).Nonempty := ⟨i₀, by simpa using hi₀⟩
  obtain ⟨m, hm, hmmax⟩ := Finset.exists_max_image _ (fun i => O.valuation (g i)) hne'
  have hgm : g m ≠ 0 := by simpa using hm
  have hb : ∀ i, g i / g m ∈ O := by
    intro i
    by_cases hi : g i = 0
    · simp [hi]
    · apply O.mem_of_valuation_le_one
      rw [map_div₀]
      have hm0 : (0 : O.ValueGroup) < O.valuation (g m) := by
        rw [zero_lt_iff]; exact (map_ne_zero _).mpr hgm
      exact (div_le_one₀ hm0).mpr (hmmax i (by simpa using hi))
  let b : ι → O := fun i => ⟨g i / g m, hb i⟩
  have hrel : ∑ i, AlgebraicCurve.Place.restrictInclusion F₀ w (b i) * x i = 0 := by
    apply Subtype.ext
    have hcoe : ((∑ i, AlgebraicCurve.Place.restrictInclusion F₀ w (b i) * x i :
        w.toValuationSubring) : F₀') =
        ∑ i, algebraMap F₀ F₀' (g i / g m) * (x i : F₀') := by
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [MulMemClass.coe_mul, AlgebraicCurve.Place.coe_restrictInclusion]
    rw [hcoe]
    have : ∑ i, algebraMap F₀ F₀' (g i / g m) * (x i : F₀') =
        algebraMap F₀ F₀' (g m)⁻¹ * ∑ i, g i • ((x i : w.toValuationSubring) : F₀') := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, div_eq_inv_mul, map_mul, mul_assoc]
    rw [this, hg, mul_zero]
    rfl
  have hres : ∑ i, (residue O (b i) : (w.restrict F₀).ResidueField) •
      (residue w.toValuationSubring (x i) : w.ResidueField) = 0 := by
    have h := congrArg (residue w.toValuationSubring) hrel
    rw [map_sum, map_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, AlgebraicCurve.Place.algebraMap_residueField_eq,
      AlgebraicCurve.Place.restrictResidueMap_residue, map_mul]
  have hm1 := (Fintype.linearIndependent_iff.mp hx) _ hres m
  have hbm : b m = 1 := Subtype.ext (div_self hgm)
  rw [hbm, map_one] at hm1
  exact one_ne_zero hm1

open IsLocalRing in
private theorem rf_finite_residueField (w : AlgebraicCurve.Place K₀ F₀') :
    Module.Finite (w.restrict F₀).ResidueField w.ResidueField := by
  classical
  rw [← Module.rank_lt_aleph0_iff]
  refine lt_of_le_of_lt (rank_le (n := Module.finrank F₀ F₀') fun s hs => ?_)
    Cardinal.natCast_lt_aleph0
  choose x hx using fun y : s => residue_surjective (R := w.toValuationSubring)
    (y : w.ResidueField)
  have hs' : LinearIndependent (w.restrict F₀).ResidueField
      fun i : s => (residue w.toValuationSubring (x i) : w.ResidueField) := by
    simpa only [hx] using hs
  have := rf_linearIndependent_lift (F₀ := F₀) w x hs'
  simpa [Fintype.card_coe] using this.fintype_card_le_finrank

end ResidueFieldInline
p2m_reactivate "P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable.ModularCurve.CharPModel P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable.ModularCurve"

private theorem transcendental_jBar (N : ℕ) [NeZero N] :
    Transcendental (AlgebraicClosure ℚ) (jBar N) := by
  have h := tjq_transcendental (AlgebraicClosure ℚ)
  rw [← coeffEmb_jq_eq_jqModC] at h
  exact transcendental_subtype _
    (coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionField_le_full N (jq_mem N))) h

private theorem transcendental_jC (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    Transcendental k (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) :=
  transcendental_subtype _ (jqModC_mem k N) (tjq_transcendental k)

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
    ({⟨jqModC k, jqModC_mem k N⟩} : Set (modularFunctionFieldC k
        N)))).toLinearEquiv.finiteDimensional

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
p2m_reactivate "P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable.ModularCurve.CharPModel P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable.ModularCurve"

end CharPModel
p2m_reactivate "P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable.ModularCurve.CharPModel P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable.ModularCurve.CharPModel P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable.ModularCurve.CharPModel P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable.ModularCurve"

set_option autoImplicit false

noncomputable section

open scoped IntermediateField.algebraAdjoinAdjoin
open IntermediateField Polynomial

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.restrictInclusion Place.coe_restrictInclusion Place.restrictResidueMap_residue Place.algebraMap_residueField_eq"
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
  have : j = algebraMap (Algebra.adjoin K ({j} : Set F)) F ⟨j, Algebra.self_mem_adjoin_singleton K
      j⟩ :=
    rfl
  rw [this]
  exact isIntegral_algebraMap

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable.ModularCurve.CharPModel P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable.ModularCurve.CharPModel P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable.ModularCurve"

open _root_.ModularCurve.CharPModel _root_.P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable.ModularCurve.CharPModel in
theorem solution
    (k : Type*) [Field k] (N : ℕ) [NeZero N] (dataN : ModularPolynomialData N)
    (hsep : ((dataN.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable) :
    FiniteDimensional ↥(IntermediateField.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N) ∧
    Algebra.IsSeparable ↥(IntermediateField.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N) ∧
    IsDedekindDomain ↥(integralClosure ↥(Algebra.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N)) ∧
    IsFractionRing ↥(integralClosure ↥(Algebra.adjoin k ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N))) ↥(modularFunctionFieldC k N)) ↥(modularFunctionFieldC k N) := by
  haveI hFD : FiniteDimensional
      (IntermediateField.adjoin k ({jGeomGen k N} : Set (modularFunctionFieldC k N)))
      (modularFunctionFieldC k N) := finiteDimensional_adjoin_jC k N dataN
  haveI hSep : Algebra.IsSeparable
      (IntermediateField.adjoin k ({jGeomGen k N} : Set (modularFunctionFieldC k N)))
      (modularFunctionFieldC k N) := isSeparable_line_fibre k N dataN hsep
  have hj : Transcendental k (jGeomGen k N) := transcendental_jC k N
  exact ⟨hFD, hSep,
    isDedekindDomain_integralClosure_adjoin (K := k) (F := modularFunctionFieldC k N) (j := jGeomGen k N) hj,
    isFractionRing_integralClosure_adjoin (K := k) (F := modularFunctionFieldC k N) (j := jGeomGen k N) hj⟩

end S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable
end P2MW
export P2MW.S_ModularCurve_isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable (solution)
