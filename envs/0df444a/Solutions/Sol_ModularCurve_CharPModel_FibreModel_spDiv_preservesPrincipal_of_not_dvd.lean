-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.spDiv_preservesPrincipal_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/6d92a048-13fd-575b-87ae-8fc4538ebcc6

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_ValuationSubring_ReduceAt
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_eq_ord_coeffMap
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_modularFunctionFieldBar_eq_modularFunctionFieldC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_spDiv_preservesPrincipal_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000

set_option autoImplicit false

open AlgebraicCurve

noncomputable section

namespace SpecializationPrincipal

p2m_open "ModularCurve~dedekindPsi_pos Polynomial IsLocalRing"

section PowerBasis

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

omit [NeZero N] in
private theorem dedekindPsi_pos [NeZero N] : 0 < dedekindPsi N := by
  unfold dedekindPsi
  have h1 : 1 ∈ N.divisors.filter Squarefree := by simp [Nat.mem_divisors, NeZero.ne N]
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun d => N / d) (fun _ _ => Nat.zero_le _) h1)
  simpa using Nat.pos_of_ne_zero (NeZero.ne N)

private abbrev J : modularFunctionFieldFullC K N := ⟨jqModC K, jqModC_mem_full K N⟩

private abbrev JN : modularFunctionFieldFullC K N := ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩

private abbrev KJ : IntermediateField K (modularFunctionFieldFullC K N) :=
  IntermediateField.adjoin K ({J K N} : Set (modularFunctionFieldFullC K N))

private scoped instance algKJ : Algebra (KJ K N) (modularFunctionFieldFullC K N) := inferInstance

private scoped instance modKJ : Module (KJ K N) (modularFunctionFieldFullC K N) := inferInstance

private scoped instance towKJ : IsScalarTower K (KJ K N) (modularFunctionFieldFullC K N) := inferInstance

private scoped instance freeKJ : Module.Free (KJ K N) (modularFunctionFieldFullC K N) :=
  Module.Free.of_divisionRing _ _

variable (ℓ : ℕ) [CharP K ℓ]

omit [NeZero N] in
private theorem natCast_ne_zero [NeZero N] (hlN : ¬ ℓ ∣ N) : (N : K) ≠ 0 :=
  fun h => hlN ((CharP.cast_eq_zero_iff K ℓ N).mp h)

private theorem finrank_eq (hlN : ¬ ℓ ∣ N) :
    Module.finrank (KJ K N) (modularFunctionFieldFullC K N) = dedekindPsi N :=
  finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K N (natCast_ne_zero K N ℓ hlN)

private theorem finite (hlN : ¬ ℓ ∣ N) : Module.Finite (KJ K N) (modularFunctionFieldFullC K N) :=
  Module.finite_of_finrank_pos (by rw [finrank_eq K N ℓ hlN]; exact dedekindPsi_pos N)

private theorem isIntegral_JN (hlN : ¬ ℓ ∣ N) : IsIntegral (KJ K N) (JN K N) := by
  haveI := finite K N ℓ hlN
  exact Algebra.IsIntegral.isIntegral _

private theorem adjoin_JN_eq_top (hlN : ¬ ℓ ∣ N) :
    IntermediateField.adjoin (KJ K N) ({JN K N} : Set (modularFunctionFieldFullC K N)) = ⊤ := by
  apply IntermediateField.restrictScalars_injective K
  rw [IntermediateField.adjoin_simple_adjoin_simple, IntermediateField.restrictScalars_top, eq_top_iff]
  intro x _
  have hxC : (x : LaurentSeries K) ∈ modularFunctionFieldC K N := by
    rw [modularFunctionFieldC_eq_modularFunctionFieldFullC K ℓ N hlN]; exact x.2

  have hle : modularFunctionFieldC K N ≤
      (IntermediateField.adjoin K ({J K N, JN K N} : Set (modularFunctionFieldFullC K N))).map
        (modularFunctionFieldFullC K N).val := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro z (rfl | rfl)
    · rw [IntermediateField.coe_map]
      exact ⟨J K N, IntermediateField.subset_adjoin K _ (Set.mem_insert _ _), rfl⟩
    · rw [IntermediateField.coe_map]
      exact ⟨JN K N, IntermediateField.subset_adjoin K _ (Set.mem_insert_of_mem _ rfl), rfl⟩
  have hx : (x : LaurentSeries K) ∈ ((IntermediateField.adjoin K ({J K N, JN K N} :
      Set (modularFunctionFieldFullC K N))).map (modularFunctionFieldFullC K N).val : Set (LaurentSeries K)) :=
    hle hxC
  rw [IntermediateField.coe_map, Set.mem_image] at hx
  obtain ⟨x', hx', hxx'⟩ := hx
  obtain rfl : x' = x := Subtype.ext hxx'
  exact hx'

private theorem natDegree_minpoly_JN (hlN : ¬ ℓ ∣ N) :
    (minpoly (KJ K N) (JN K N)).natDegree = dedekindPsi N := by
  rw [← IntermediateField.adjoin.finrank (isIntegral_JN K N ℓ hlN), adjoin_JN_eq_top K N ℓ hlN,
    IntermediateField.finrank_top', finrank_eq K N ℓ hlN]

omit [NeZero N] in
private theorem coe_aeval_J (p : K[X]) :
    ((aeval (J K N) p : modularFunctionFieldFullC K N) : LaurentSeries K) = aeval (jqModC K) p :=
  (aeval_algHom_apply (modularFunctionFieldFullC K N).val (J K N) p).symm

omit [NeZero N] in
private theorem aeval_J_mem (p : K[X]) : aeval (J K N) p ∈ KJ K N :=
  IntermediateField.algebra_adjoin_le_adjoin _ _ (Polynomial.aeval_mem_adjoin_singleton _ _)

private theorem indep (hlN : ¬ ℓ ∣ N) (a : Fin (dedekindPsi N) → K[X])
    (h : ∑ i, aeval (jqModC K) (a i) * jqNModC K N ^ (i : ℕ) = 0) : ∀ i, a i = 0 := by
  classical
  have hli : LinearIndependent (KJ K N) fun i : Fin (dedekindPsi N) => (JN K N) ^ (i : ℕ) := by
    have := linearIndependent_pow (K := KJ K N) (JN K N)
    rwa [natDegree_minpoly_JN K N ℓ hlN] at this
  have hrel : ∑ i, (⟨aeval (J K N) (a i), aeval_J_mem K N (a i)⟩ : KJ K N) • (JN K N) ^ (i : ℕ) = 0 := by
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero, ← h, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [IntermediateField.smul_def, smul_eq_mul, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
    exact congrArg (· * _) (coe_aeval_J K N (a i))
  have h0 := Fintype.linearIndependent_iff.mp hli _ hrel
  intro i
  have h1 : aeval (J K N) (a i) = 0 := congrArg Subtype.val (h0 i)
  have h2 : aeval (jqModC K) (a i) = 0 := by
    rw [← coe_aeval_J K N (a i), h1]
    rfl
  exact (transcendental_iff.mp (transcendental_jqModC K)) _ h2

private theorem repr (hlN : ¬ ℓ ∣ N) (g : LaurentSeries K) (hg : g ∈ modularFunctionFieldC K N) :
    ∃ (a : Fin (dedekindPsi N) → K[X]) (b : K[X]), aeval (jqModC K) b ≠ 0 ∧
      g * aeval (jqModC K) b = ∑ i, aeval (jqModC K) (a i) * jqNModC K N ^ (i : ℕ) := by
  classical
  have hgF : g ∈ modularFunctionFieldFullC K N := by
    rw [← modularFunctionFieldC_eq_modularFunctionFieldFullC K ℓ N hlN]; exact hg
  obtain ⟨G, hGdef⟩ : ∃ G : modularFunctionFieldFullC K N, G = ⟨g, hgF⟩ := ⟨_, rfl⟩
  have hint := isIntegral_JN K N ℓ hlN
  have hmem : G ∈ (IntermediateField.adjoin (KJ K N) ({JN K N} : Set (modularFunctionFieldFullC K N))).toSubalgebra := by
    rw [adjoin_JN_eq_top K N ℓ hlN]; trivial
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, Algebra.adjoin_singleton_eq_range_aeval,
    AlgHom.mem_range] at hmem
  obtain ⟨p, hp⟩ := hmem
  have hdeg : (p %ₘ minpoly (KJ K N) (JN K N)).natDegree < dedekindPsi N := by
    rw [← natDegree_minpoly_JN K N ℓ hlN]
    exact natDegree_modByMonic_lt p (minpoly.monic hint) (minpoly.ne_one _ _)
  set P := p %ₘ minpoly (KJ K N) (JN K N) with hPdef
  have hG : G = ∑ i : Fin (dedekindPsi N), P.coeff i • (JN K N) ^ (i : ℕ) := by
    rw [← hp, ← aeval_modByMonic_eq_self_of_root (minpoly.aeval (KJ K N) (JN K N)) (p := p),
      aeval_eq_sum_range' hdeg, ← Fin.sum_univ_eq_sum_range]

  obtain ⟨r, s, hs, hrs⟩ : ∃ r s : Fin (dedekindPsi N) → K[X], (∀ i, aeval (J K N) (s i) ≠ 0) ∧
      ∀ i : Fin (dedekindPsi N), ((P.coeff (i : ℕ) : KJ K N) : modularFunctionFieldFullC K N) * aeval (J K N) (s i)
        = aeval (J K N) (r i) := by
    have hK : ∀ i : Fin (dedekindPsi N), ∃ r s : K[X], ((P.coeff (i : ℕ) : KJ K N) : modularFunctionFieldFullC K N)
        = aeval (J K N) r / aeval (J K N) s :=
      fun i => (IntermediateField.mem_adjoin_simple_iff (F := K) (α := J K N) _).mp (P.coeff (i : ℕ)).2
    choose r s hrs using hK
    refine ⟨fun i => if aeval (J K N) (s i) = 0 then 0 else r i,
      fun i => if aeval (J K N) (s i) = 0 then 1 else s i, fun i => ?_, fun i => ?_⟩
    · show aeval (J K N) (if aeval (J K N) (s i) = 0 then 1 else s i) ≠ 0
      by_cases h : aeval (J K N) (s i) = 0
      · rw [if_pos h, map_one]; exact one_ne_zero
      · rw [if_neg h]; exact h
    · show _ * aeval (J K N) (if aeval (J K N) (s i) = 0 then 1 else s i)
        = aeval (J K N) (if aeval (J K N) (s i) = 0 then 0 else r i)
      by_cases h : aeval (J K N) (s i) = 0
      · rw [if_pos h, if_pos h, map_one, mul_one, map_zero, hrs i, h, div_zero]
      · rw [if_neg h, if_neg h, hrs i, div_mul_cancel₀ _ h]
  refine ⟨fun i => r i * ∏ i' ∈ Finset.univ.erase i, s i', ∏ i, s i, ?_, ?_⟩
  · rw [← coe_aeval_J K N, map_prod]
    intro h0
    exact (Finset.prod_ne_zero_iff.mpr fun i _ => hs i) (Subtype.ext (by simpa using h0) : (∏ i, aeval (J K N) (s i)) = 0)
  · have hT : ∀ i, aeval (J K N) (r i * ∏ i' ∈ Finset.univ.erase i, s i')
        = ((P.coeff i : KJ K N) : modularFunctionFieldFullC K N) * ∏ i', aeval (J K N) (s i') := by
      intro i
      rw [map_mul, map_prod, ← hrs i, mul_assoc,
        Finset.mul_prod_erase Finset.univ (fun i' => aeval (J K N) (s i')) (Finset.mem_univ i)]
    have h1F : G * aeval (J K N) (∏ i, s i)
        = ∑ i, aeval (J K N) (r i * ∏ i' ∈ Finset.univ.erase i, s i') * (JN K N) ^ (i : ℕ) := by
      rw [map_prod, hG, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hT i, IntermediateField.smul_def, smul_eq_mul]
      ring
    have h1 : g * aeval (jqModC K) (∏ i, s i)
        = ((∑ i, aeval (J K N) (r i * ∏ i' ∈ Finset.univ.erase i, s i') * (JN K N) ^ (i : ℕ) :
            modularFunctionFieldFullC K N) : LaurentSeries K) := by
      rw [← h1F, MulMemClass.coe_mul, coe_aeval_J K N, hGdef]
    rw [h1, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_aeval_J K N]

end PowerBasis

section Scale

variable (A : ValuationSubring (AlgebraicClosure ℚ))

private theorem exists_scale {n : ℕ} (a : Fin n → (AlgebraicClosure ℚ)[X]) (ha : ∃ i, a i ≠ 0) :
    ∃ (c : AlgebraicClosure ℚ) (q : Fin n → A[X]) (i₀ : Fin n) (n₀ : ℕ), c ≠ 0 ∧
      (∀ i, (q i).map (algebraMap A (AlgebraicClosure ℚ)) = C c⁻¹ * a i) ∧ (q i₀).coeff n₀ = 1 := by
  classical
  obtain ⟨i₁, hi₁⟩ := ha
  let T : Finset (Σ _ : Fin n, ℕ) := Finset.univ.sigma fun i => (a i).support
  have hT : T.Nonempty :=
    ⟨⟨i₁, (a i₁).natDegree⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, natDegree_mem_support_of_nonzero hi₁⟩⟩
  obtain ⟨⟨i₀, n₀⟩, hmem, hmax⟩ := Finset.exists_max_image T (fun t => A.valuation ((a t.1).coeff t.2)) hT
  have hc : (a i₀).coeff n₀ ≠ 0 := mem_support_iff.mp (Finset.mem_sigma.mp hmem).2
  set c := (a i₀).coeff n₀ with hcdef
  have hvc : A.valuation c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
  have hcoef : ∀ i k, c⁻¹ * (a i).coeff k ∈ A := by
    intro i k
    by_cases hk : k ∈ (a i).support
    · have hle : A.valuation ((a i).coeff k) ≤ A.valuation c :=
        hmax ⟨i, k⟩ (Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hk⟩)
      rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
      calc (A.valuation c)⁻¹ * A.valuation ((a i).coeff k)
          ≤ (A.valuation c)⁻¹ * A.valuation c := mul_le_mul_right hle _
        _ = 1 := inv_mul_cancel₀ hvc
    · rw [Polynomial.notMem_support_iff.mp hk, mul_zero]
      exact zero_mem A
  have hl : ∀ i, C c⁻¹ * a i ∈ Polynomial.lifts (algebraMap A (AlgebraicClosure ℚ)) := by
    intro i
    rw [lifts_iff_coeff_lifts]
    intro k
    rw [coeff_C_mul]
    exact ⟨⟨_, hcoef i k⟩, rfl⟩
  choose q hq using fun i => (mem_lifts _).mp (hl i)
  refine ⟨c, q, i₀, n₀, hc, hq, ?_⟩
  have h1 := congrArg (fun p => p.coeff n₀) (hq i₀)
  simp only [coeff_map, coeff_C_mul] at h1
  rw [← hcdef, inv_mul_cancel₀ hc] at h1
  have h2 : (((q i₀).coeff n₀ : A) : AlgebraicClosure ℚ) = 1 := h1
  exact_mod_cast h2

private theorem coeffMap_sum {S : Type*} [CommRing S] (φ : A →+* S) {n : ℕ} (q : Fin n → A[X]) (N : ℕ) [NeZero N] :
    coeffMap φ (∑ i, aeval (jqModC A) (q i) * jqNModC A N ^ (i : ℕ))
      = ∑ i, aeval (jqModC S) ((q i).map φ) * jqNModC S N ^ (i : ℕ) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, coeffMap_jqNModC]
  congr 1
  rw [aeval_def, aeval_def, eval₂_map, Polynomial.hom_eval₂, coeffMap_jqModC]
  congr 1
  ext a : 1
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [HahnSeries.algebraMap_apply', HahnSeries.algebraMap_apply', ← PowerSeries.C_eq_algebraMap,
    ← PowerSeries.C_eq_algebraMap, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply,
    HahnSeries.C_apply, coeffMap_single]

end Scale

section Constant

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem ord_algebraMap {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have hu : IsUnit (algebraMap K v.toValuationSubring c) := hc.isUnit.map _
  have h := v.ord_coe_unit hu.unit
  rwa [IsUnit.unit_spec, Place.coe_algebraMap] at h

private theorem degree_mapDomain {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F']
    [IsAlgClosed K] [IsCurveOver K F] [IsAlgClosed K'] [IsCurveOver K' F']
    (f : Place K F → Place K' F') (D : Divisor K F) :
    Divisor.degree (Finsupp.mapDomain f D) = Divisor.degree D := by
  simp only [Divisor.degree, Finsupp.liftAddHom_apply]
  rw [Finsupp.sum_mapDomain_index_addMonoidHom]
  refine Finsupp.sum_congr fun P _ => ?_
  simp [IsCurveOver.deg_eq_one_of_isAlgClosed]

end Constant

end SpecializationPrincipal
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spDiv_preservesPrincipal_of_not_dvd.SpecializationPrincipal"

p2m_open "ModularCurve~dedekindPsi_pos" in open  IsLocalRing Polynomial SpecializationPrincipal in
theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField A) ℓ]
    (hℓN : ¬ ℓ ∣ N)
    (fm : ModularCurve.CharPModel.FibreModel N A ℓ (IsLocalRing.ResidueField A)
      (IsLocalRing.residue A))
    (cc : fm.CuspChart)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularCurve.ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (IsLocalRing.ResidueField A)))).map
      (algebraMap (Polynomial (IsLocalRing.ResidueField A)) (RatFunc (IsLocalRing.ResidueField A)))).Separable) :
    fm.SpDivPreservesPrincipal Ideal.Quotient.mk_surjective dataAll hsep := by
  classical

  set Kb := AlgebraicClosure ℚ with hKb
  set k := ResidueField A with hk
  have h0N : ¬ 0 ∣ N := fun h => NeZero.ne N (zero_dvd_iff.mp h)
  have hBar : modularFunctionFieldBar N = modularFunctionFieldC Kb N :=
    modularFunctionFieldBar_eq_modularFunctionFieldC N
  haveI : IsCurveOver Kb (modularFunctionFieldBar N) := by
    rw [hBar]; exact isCurveOver_modularFunctionFieldC_of_perfectField Kb N
  haveI : IsCurveOver k (modularFunctionFieldC k N) := isCurveOver_modularFunctionFieldC_of_perfectField k N
  refine ⟨fun D hD => ?_, fun D hD hP => ?_⟩
  ·
    rw [Divisor.mem_degZero] at hD ⊢
    show Divisor.degree (Finsupp.mapDomain _ D) = 0
    rw [degree_mapDomain, hD]
  ·
    obtain ⟨g, hg0, hgD⟩ := hP
    have hgC : (g : LaurentSeries Kb) ∈ modularFunctionFieldC Kb N := hBar ▸ g.2
    obtain ⟨a, b, hb, hgab⟩ := SpecializationPrincipal.repr Kb N 0 h0N g hgC
    have ha : ∃ i, a i ≠ 0 := by
      by_contra h
      push Not at h
      have h1 : (g : LaurentSeries Kb) * aeval (jqModC Kb) b = 0 := by
        rw [hgab]; exact Finset.sum_eq_zero fun i _ => by rw [h i, map_zero, zero_mul]
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact hg0 (Subtype.ext h2)
      · exact hb h2
    obtain ⟨c, q, i₀, n₀, hc, hq, hq1⟩ := SpecializationPrincipal.exists_scale A a ha
    obtain ⟨c', q', i₀', n₀', hc', hq', hq1'⟩ := SpecializationPrincipal.exists_scale A (fun _ : Fin 1 => b)
      ⟨0, fun h => hb (by rw [show b = 0 from h, map_zero])⟩

    set y : LaurentSeries A := ∑ i, aeval (jqModC A) (q i) * jqNModC A N ^ (i : ℕ) with hy
    set y' : LaurentSeries A := ∑ i, aeval (jqModC A) (q' i) * jqNModC A N ^ (i : ℕ) with hy'

    have hbj : aeval (jqModC Kb) b ∈ modularFunctionFieldBar N := by
      rw [hBar]
      exact (Algebra.adjoin_le (Set.singleton_subset_iff.mpr (jqModC_mem Kb N)) :
        Algebra.adjoin Kb {jqModC Kb} ≤ (modularFunctionFieldC Kb N).toSubalgebra)
          (Polynomial.aeval_mem_adjoin_singleton Kb _)
    obtain ⟨B, hB⟩ : ∃ B : modularFunctionFieldBar N, B = ⟨aeval (jqModC Kb) b, hbj⟩ := ⟨_, rfl⟩
    have hB0 : B ≠ 0 := fun h => hb (by have := congrArg Subtype.val h; rw [hB] at this; simpa using this)
    have hyu : coeffMap A.subtype y = algebraMap Kb (LaurentSeries Kb) c⁻¹ * ((g : LaurentSeries Kb) * aeval (jqModC Kb) b) := by
      rw [hy, SpecializationPrincipal.coeffMap_sum A A.subtype q N, hgab, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (q i).map A.subtype = C c⁻¹ * a i from hq i, map_mul, aeval_C, mul_assoc]
    have hyu' : coeffMap A.subtype y' = algebraMap Kb (LaurentSeries Kb) c'⁻¹ * aeval (jqModC Kb) b := by
      rw [hy', SpecializationPrincipal.coeffMap_sum A A.subtype q' N, Fin.sum_univ_one,
        show (q' 0).map A.subtype = C c'⁻¹ * b from hq' 0, map_mul, aeval_C, Fin.val_zero, pow_zero, mul_one]
    have hyBar : coeffMap A.subtype y ∈ modularFunctionFieldBar N := by
      rw [hyu]; exact mul_mem ((modularFunctionFieldBar N).algebraMap_mem _) (mul_mem g.2 hbj)
    have hyBar' : coeffMap A.subtype y' ∈ modularFunctionFieldBar N := by
      rw [hyu']; exact mul_mem ((modularFunctionFieldBar N).algebraMap_mem _) hbj
    obtain ⟨u, hu⟩ : ∃ u : modularFunctionFieldBar N, u = ⟨coeffMap A.subtype y, hyBar⟩ := ⟨_, rfl⟩
    obtain ⟨u', hu'⟩ : ∃ u' : modularFunctionFieldBar N, u' = ⟨coeffMap A.subtype y', hyBar'⟩ := ⟨_, rfl⟩
    have hu_eq : u = algebraMap Kb (modularFunctionFieldBar N) c⁻¹ * (g * B) := Subtype.ext (by
      rw [hu, hB, MulMemClass.coe_mul, MulMemClass.coe_mul]; exact hyu)
    have hu'_eq : u' = algebraMap Kb (modularFunctionFieldBar N) c'⁻¹ * B := Subtype.ext (by
      rw [hu', hB, MulMemClass.coe_mul]; exact hyu')
    have hu0 : u ≠ 0 := by
      rw [hu_eq]; exact mul_ne_zero ((_root_.map_ne_zero _).mpr (inv_ne_zero hc)) (mul_ne_zero hg0 hB0)
    have hu'0 : u' ≠ 0 := by
      rw [hu'_eq]; exact mul_ne_zero ((_root_.map_ne_zero _).mpr (inv_ne_zero hc')) hB0

    have hmemk : ∀ (n : ℕ) (r : Fin n → A[X]),
        ∑ i, aeval (jqModC k) ((r i).map (residue A)) * jqNModC k N ^ (i : ℕ) ∈ modularFunctionFieldC k N := by
      intro n r
      refine sum_mem fun i _ => mul_mem ?_ (pow_mem (jqNModC_mem k N) _)
      exact (Algebra.adjoin_le (Set.singleton_subset_iff.mpr (jqModC_mem k N)) :
        Algebra.adjoin k {jqModC k} ≤ (modularFunctionFieldC k N).toSubalgebra)
          (Polynomial.aeval_mem_adjoin_singleton k _)
    have hyk : coeffMap (residue A) y ∈ modularFunctionFieldC k N := by
      rw [hy, SpecializationPrincipal.coeffMap_sum A (residue A) q N]; exact hmemk _ q
    have hyk' : coeffMap (residue A) y' ∈ modularFunctionFieldC k N := by
      rw [hy', SpecializationPrincipal.coeffMap_sum A (residue A) q' N]; exact hmemk _ q'
    have hyne : coeffMap (residue A) y ≠ 0 := by
      intro h0
      rw [hy, SpecializationPrincipal.coeffMap_sum A (residue A) q N] at h0
      have h2 := SpecializationPrincipal.indep k N ℓ hℓN (fun i => (q i).map (residue A)) h0 i₀
      have h3 := congrArg (fun p => p.coeff n₀) h2
      simp only [coeff_map, hq1, map_one, coeff_zero] at h3
      exact one_ne_zero h3
    have hyne' : coeffMap (residue A) y' ≠ 0 := by
      intro h0
      rw [hy', SpecializationPrincipal.coeffMap_sum A (residue A) q' N, Fin.sum_univ_one, Fin.val_zero, pow_zero,
        mul_one] at h0
      have h2 : (q' 0).map (residue A) = 0 :=
        (transcendental_iff.mp (transcendental_jqModC k)) _ h0
      have hi : i₀' = 0 := Subsingleton.elim _ _
      have h3 := congrArg (fun p => p.coeff n₀') h2
      rw [hi] at hq1'
      simp only [coeff_map, hq1', map_one, coeff_zero] at h3
      exact one_ne_zero h3

    obtain ⟨Du, hDu, -⟩ := (IsCurveOver.hasPrincipalDivisors (K := Kb) (F := modularFunctionFieldBar N)).exists_divisor
      u hu0
    have hDu_lit : ∀ P, Du P = P.ord (⟨coeffMap A.subtype y, hyBar⟩ : modularFunctionFieldBar N) := fun P => by
      rw [hDu P, hu]
    set Du' := Du - D with hDu'def
    have hou : ∀ P : Place Kb (modularFunctionFieldBar N), P.ord u = P.ord g + P.ord B := fun P => by
      rw [hu_eq, P.ord_mul ((_root_.map_ne_zero _).mpr (inv_ne_zero hc)) (mul_ne_zero hg0 hB0),
        SpecializationPrincipal.ord_algebraMap P (inv_ne_zero hc), zero_add, P.ord_mul hg0 hB0]
    have hou' : ∀ P : Place Kb (modularFunctionFieldBar N), P.ord u' = P.ord B := fun P => by
      rw [hu'_eq, P.ord_mul ((_root_.map_ne_zero _).mpr (inv_ne_zero hc')) hB0,
        SpecializationPrincipal.ord_algebraMap P (inv_ne_zero hc'), zero_add]
    have hDu' : ∀ P, Du' P = P.ord u' := fun P => by
      rw [hDu'def, Finsupp.sub_apply, hDu P, hgD P, hou, hou']
      ring

    have hDu'_lit : ∀ P, Du' P = P.ord (⟨coeffMap A.subtype y', hyBar'⟩ : modularFunctionFieldBar N) := fun P => by
      rw [hDu' P, hu']
    have h1 := CharPModel.FibreModel.mapDomain_spPlace_eq_ord_coeffMap N ℓ A hℓN fm cc dataAll hsep y hyBar hyk hyne
      Du hDu_lit
    have h2 := CharPModel.FibreModel.mapDomain_spPlace_eq_ord_coeffMap N ℓ A hℓN fm cc dataAll hsep y' hyBar' hyk'
      hyne' Du' hDu'_lit
    refine ⟨⟨coeffMap (residue A) y, hyk⟩ / ⟨coeffMap (residue A) y', hyk'⟩,
      div_ne_zero (fun h => hyne (congrArg Subtype.val h)) (fun h => hyne' (congrArg Subtype.val h)), fun Q => ?_⟩
    have hD : D = Du - Du' := by rw [hDu'def, sub_sub_cancel]
    show Finsupp.mapDomain (fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep) D Q = _
    have hz : (⟨coeffMap (residue A) y, hyk⟩ : modularFunctionFieldC k N) ≠ 0 := fun h => hyne (congrArg Subtype.val h)
    have hz' : (⟨coeffMap (residue A) y', hyk'⟩ : modularFunctionFieldC k N) ≠ 0 := fun h => hyne' (congrArg Subtype.val h)
    rw [hD, Finsupp.mapDomain_sub, Finsupp.sub_apply, h1 Q, h2 Q, div_eq_mul_inv, Q.ord_mul hz (inv_ne_zero hz'),
      Q.ord_inv]
    ring

end
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_spDiv_preservesPrincipal_of_not_dvd.SpecializationPrincipal"

end S_ModularCurve_CharPModel_FibreModel_spDiv_preservesPrincipal_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_spDiv_preservesPrincipal_of_not_dvd (solution)
