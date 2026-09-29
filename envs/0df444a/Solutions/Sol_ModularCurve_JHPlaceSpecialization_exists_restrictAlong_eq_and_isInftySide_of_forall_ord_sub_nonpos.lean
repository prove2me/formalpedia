-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.exists_restrictAlong_eq_and_isInftySide_of_forall_ord_sub_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/b4cae3b4-66d2-50e4-87ba-66d1255ea03f

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_WeierstrassCurve_ReductionMap
import Theorems.Thm_AlgebraicCurve_exists_place_over_of_simple_root_along
import Theorems.Thm_AlgebraicCurve_Place_ord_norm_sub_eq_ord_eval
import Theorems.Thm_ModularCurve_ModularPolynomialData_eq_all
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_le
import Theorems.Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_le_mul_dedekindPsi_sub
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_exists_kroneckerCongruence_of_prime
import Theorems.Thm_ModularCurve_xHFunctionFieldBar_div_sup_adjoin_qExpand_jqModC_eq_xHFunctionFieldBar
import Theorems.Thm_ModularCurve_finrankAlong_eq_add_one_of_coe_eq_xHFunctionFieldBar
import Theorems.Thm_ModularCurve_finiteAlong_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_exists_restrictAlong_eq_and_isInftySide_of_forall_ord_sub_nonpos
p2m_attr_erase "instance" "ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple Polynomial

noncomputable section

namespace CuspNormalizationH

section PlaceFurniture

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem ord_pos_of_not_isUnit {a : v.toValuationSubring} (ha : ¬ IsUnit a) (h0 : (a : F) ≠ 0) :
    0 < v.ord (a : F) := by
  have hnn : 0 ≤ v.ord (a : F) := v.ord_nonneg_of_mem a.2
  rcases hnn.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow h0 hπ
    rw [← heq, zpow_zero, mul_one] at hu
    apply ha
    have : a = (u : v.toValuationSubring) := Subtype.ext hu
    rw [this]
    exact u.isUnit

private theorem not_isUnit_of_ord_pos {a : v.toValuationSubring} (h : 0 < v.ord (a : F)) : ¬ IsUnit a := by
  intro hu
  obtain ⟨u, rfl⟩ := hu
  rw [v.ord_coe_unit u] at h
  exact lt_irrefl _ h

private theorem hasValue_of_ord_sub_pos {g : F} {c : K} (h : 0 < v.ord (g - algebraMap K F c)) :
    v.HasValue g c := by
  have hne : g - algebraMap K F c ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at h
    exact lt_irrefl _ h
  have hmem : g - algebraMap K F c ∈ v.toValuationSubring := v.mem_of_ord_nonneg hne h.le
  have hg : g ∈ v.toValuationSubring := by
    have := add_mem hmem (v.algebraMap_mem' c)
    rwa [sub_add_cancel] at this
  refine ⟨hg, ?_⟩
  have hmax : (⟨g - algebraMap K F c, hmem⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring :=
    (mem_maximalIdeal _).mpr (not_isUnit_of_ord_pos v h)
  have hsplit : (⟨g, hg⟩ : v.toValuationSubring)
      = ⟨g - algebraMap K F c, hmem⟩ + algebraMap K v.toValuationSubring c :=
    Subtype.ext (by simp)
  rw [hsplit, map_add, (residue_eq_zero_iff _).mpr hmax, zero_add]
  exact v.residue_algebraMap c

private theorem ord_sub_pos_of_hasValue {g : F} {c : K} (h : v.HasValue g c) (hne : g ≠ algebraMap K F c) :
    0 < v.ord (g - algebraMap K F c) := by
  obtain ⟨hg, hres⟩ := h
  have hmem : g - algebraMap K F c ∈ v.toValuationSubring := sub_mem hg (v.algebraMap_mem' c)
  refine ord_pos_of_not_isUnit v (a := ⟨g - algebraMap K F c, hmem⟩) ?_ (sub_ne_zero.mpr hne)
  rw [← mem_nonunits_iff, ← mem_maximalIdeal, ← residue_eq_zero_iff]
  have hsplit : (⟨g - algebraMap K F c, hmem⟩ : v.toValuationSubring)
      = ⟨g, hg⟩ - algebraMap K v.toValuationSubring c :=
    Subtype.ext (by simp)
  rw [hsplit, map_sub, hres, sub_eq_zero]
  exact (v.residue_algebraMap c).symm

private theorem surjective_algebraMap_residueField_of_deg_eq_one [IsAlgClosed K] (h : v.deg = 1) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  have h' : Module.finrank K v.ResidueField = Nat.succ 0 := h
  haveI : Module.Finite K v.ResidueField := Module.finite_of_finrank_eq_succ h'
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

end PlaceFurniture

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type} [Field k] [CharP k q]
  {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

omit [Fact q.Prime] in

private theorem red_eq_zero_of_mem_nonunits (hq : q.Prime) (r : A →+* k) (m : A) (hm : m ∈ nonunits A) :
    r m = 0 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : CharZero (AlgebraicClosure ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (AlgebraicClosure ℚ)).injective

  set P : Ideal A := RingHom.ker r with hP
  haveI hPprime : P.IsPrime := RingHom.ker_isPrime r
  haveI : Nontrivial (A ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hPprime.ne_top
  have hqP : ((q : ℕ) : A) ∈ P := by
    rw [hP, RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]

  haveI hchar : CharP (A ⧸ P) q := by
    have h0 : ((q : ℕ) : A ⧸ P) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
      exact hqP
    rcases (Nat.dvd_prime hq).mp (ringChar.dvd h0) with h1 | h2
    · exact absurd h1 CharP.ringChar_ne_one
    · exact ringChar.eq_iff.mp h2
  letI : Algebra (ZMod q) (A ⧸ P) := ZMod.algebra (A ⧸ P) q

  haveI : Algebra.IsIntegral (ZMod q) (A ⧸ P) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x

    have halg : IsAlgebraic ℤ (a : AlgebraicClosure ℚ) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr (Algebra.IsAlgebraic.isAlgebraic _)
    obtain ⟨p, hp0, hpa⟩ := halg
    have hp₁a : Polynomial.aeval (a : AlgebraicClosure ℚ) p.primPart = 0 := by
      have h := hpa
      rw [p.eq_C_content_mul_primPart, map_mul, Polynomial.aeval_C, eq_intCast] at h
      exact (mul_eq_zero.mp h).resolve_left
        (Int.cast_ne_zero.mpr fun hc => hp0 (Polynomial.content_eq_zero_iff.mp hc))
    set p₁ := p.primPart with hp₁
    have hprim : p₁.IsPrimitive := p.isPrimitive_primPart

    have hA : Polynomial.aeval a p₁ = 0 := by
      apply Subtype.val_injective
      rw [ZeroMemClass.coe_zero,
        show ((Polynomial.aeval a p₁ : A) : AlgebraicClosure ℚ) = Polynomial.aeval (a : AlgebraicClosure ℚ) p₁
          from (Polynomial.aeval_algHom_apply (algebraMap A (AlgebraicClosure ℚ)).toIntAlgHom a p₁).symm]
      exact hp₁a
    have hQ : Polynomial.aeval (Ideal.Quotient.mk P a) p₁ = 0 := by
      have h := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ ℤ P) a p₁
      rw [hA, map_zero] at h
      exact h

    have h1q := hq.one_lt
    have hred : p₁.map (algebraMap ℤ (ZMod q)) ≠ 0 := by
      intro h0
      have hdvd : Polynomial.C (q : ℤ) ∣ p₁ := by
        rw [Polynomial.C_dvd_iff_dvd_coeff]
        intro i
        have hi := congrArg (fun Q : Polynomial (ZMod q) => Q.coeff i) h0
        simp only [Polynomial.coeff_map, Polynomial.coeff_zero, algebraMap_int_eq, eq_intCast] at hi
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hi
      rcases Int.isUnit_iff.mp (hprim (q : ℤ) hdvd) with h1 | h1 <;> omega
    refine IsAlgebraic.isIntegral ⟨p₁.map (algebraMap ℤ (ZMod q)), hred, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      Subsingleton.elim ((algebraMap (ZMod q) (A ⧸ P)).comp (algebraMap ℤ (ZMod q))) (algebraMap ℤ (A ⧸ P)),
      ← Polynomial.aeval_def]
    exact hQ
  have hfield : IsField (A ⧸ P) := isField_of_isIntegral_of_isField' (Field.toIsField (ZMod q))
  have hPm : P = maximalIdeal A := IsLocalRing.eq_maximalIdeal (Ideal.Quotient.maximal_of_isField P hfield)
  have hmP : m ∈ P := by
    rw [hPm]
    exact (mem_maximalIdeal _).mpr hm
  rwa [hP, RingHom.mem_ker] at hmP

private def normPoly (data : ModularPolynomialData q) (S : Type*) [CommRing S] (z : S) : Polynomial S :=
  data.Φ.sum fun b cb => C (cb.sum fun a c => (c : S) * z ^ (q * (q + 1) - a - q * b)) * X ^ b

private theorem normPoly_map {S S' : Type*} [CommRing S] [CommRing S'] (f : S →+* S') (z : S) :
    (normPoly data S z).map f = normPoly data S' (f z) := by
  simp only [normPoly, Polynomial.sum_def]
  rw [← Polynomial.coe_mapRingHom, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Polynomial.coe_mapRingHom, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, map_sum]
  congr 2
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, map_pow, map_intCast]

omit [Fact q.Prime] in

private theorem dedekindPsi_prime' (hq : q.Prime) : dedekindPsi q = q + 1 := by
  classical
  rw [dedekindPsi, Nat.Prime.divisors hq]
  have h1q : (1 : ℕ) ∉ ({q} : Finset ℕ) := by
    rw [Finset.mem_singleton]
    exact hq.one_lt.ne
  rw [Finset.filter_insert, if_pos squarefree_one, Finset.filter_singleton, if_pos hq.prime.squarefree,
    Finset.sum_insert h1q, Finset.sum_singleton, Nat.div_one, Nat.div_self hq.pos]

private theorem supp_bound (hq : q.Prime) (hsym : EvalSymm data.Φ) {a b : ℕ} (hb : b ∈ data.Φ.support)
    (ha : a ∈ (data.Φ.coeff b).support) : a + q * b ≤ q * (q + 1) := by
  have hb' : b ≤ q + 1 := by
    have h := Polynomial.le_natDegree_of_mem_supp b hb
    rwa [data.natDegree_eq, dedekindPsi_prime' hq] at h
  have h1 : a ≤ q * (q + 1 - b) := by
    refine (Polynomial.le_natDegree_of_mem_supp a ha).trans ?_
    have h := ModularPolynomialData.natDegree_coeff_le_mul_dedekindPsi_sub q data hsym b
    rwa [dedekindPsi_prime' hq] at h
  calc a + q * b ≤ q * (q + 1 - b) + q * b := Nat.add_le_add_right h1 _
    _ = q * (q + 1 - b + b) := (Nat.mul_add q _ _).symm
    _ = q * (q + 1) := by rw [Nat.sub_add_cancel hb']

private theorem supp_bound' {a b : ℕ} (ha : a ∈ (data.Φ.coeff b).support) : a ≤ q + 1 :=
  (Polynomial.le_natDegree_of_mem_supp a ha).trans (ModularPolynomialData.natDegree_coeff_le q data b)

private theorem monic_normPoly {S : Type*} [CommRing S] [Nontrivial S] (hq : q.Prime) (z : S) :
    (normPoly data S z).Monic ∧ (normPoly data S z).natDegree = q + 1 := by
  have hdΦ : data.Φ.natDegree = q + 1 := by rw [data.natDegree_eq, dedekindPsi_prime' hq]
  have hc1 : data.Φ.coeff (q + 1) = 1 := by rw [← hdΦ]; exact data.monic.coeff_natDegree
  have hle : (normPoly data S z).natDegree ≤ q + 1 := by
    rw [normPoly, Polynomial.sum_def]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun b hb => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    rw [← hdΦ]
    exact Polynomial.le_natDegree_of_mem_supp b hb
  have hcoeff : (normPoly data S z).coeff (q + 1) = 1 := by
    rw [normPoly, Polynomial.sum_def, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    have hmem : q + 1 ∈ data.Φ.support := by
      rw [Polynomial.mem_support_iff, hc1]
      exact one_ne_zero
    rw [if_pos hmem, hc1, ← Polynomial.C_1, Polynomial.sum_C_index]
    · rw [Int.cast_one, one_mul, Nat.sub_zero, Nat.sub_self, pow_zero]
    · rw [Int.cast_zero, zero_mul]
  have hmonic : (normPoly data S z).Monic :=
    Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ hle hcoeff
  refine ⟨hmonic, le_antisymm hle ?_⟩
  exact Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff]; exact one_ne_zero)

private theorem normPoly_eval_div {S : Type*} [Field S] (hq : q.Prime) (hsym : EvalSymm data.Φ)
    (z y : S) (hz : z ≠ 0) :
    (normPoly data S z⁻¹).eval (y / z ^ q)
      = (z ^ (q * (q + 1)))⁻¹ * data.Φ.eval₂ (Polynomial.aeval (R := ℤ) z).toRingHom y := by
  have hae : ∀ p : Polynomial ℤ, (Polynomial.aeval (R := ℤ) z).toRingHom p = Polynomial.aeval z p :=
    fun _ => rfl

  rw [normPoly, Polynomial.sum_def, Polynomial.eval_finsetSum, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  beta_reduce
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.sum_def,
    Finset.sum_mul, hae, Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  beta_reduce

  have hbound := supp_bound (data := data) hq hsym hb ha
  have hE : q * (q + 1) - a - q * b + a + q * b = q * (q + 1) := by omega
  have hzpow : z ^ (q * (q + 1)) = z ^ (q * (q + 1) - a - q * b) * z ^ a * z ^ (q * b) := by
    rw [← pow_add, ← pow_add, hE]
  rw [eq_intCast, hzpow, inv_pow, div_pow, ← pow_mul]
  field_simp

private theorem normPoly_zero {S : Type*} [CommRing S] (hq : q.Prime) (hsym : EvalSymm data.Φ) :
    normPoly data S 0 = X ^ (q + 1) + C (((data.Φ.coeff q).coeff q : ℤ) : S) * X ^ q := by
  have hdΦ : data.Φ.natDegree = q + 1 := by rw [data.natDegree_eq, dedekindPsi_prime' hq]
  have hc1 : data.Φ.coeff (q + 1) = 1 := by rw [← hdΦ]; exact data.monic.coeff_natDegree
  have h2 : 2 ≤ q := hq.two_le
  have hqq : q * (q + 1) = q * q + q := by ring
  have hmem : q + 1 ∈ data.Φ.support := by
    rw [Polynomial.mem_support_iff, hc1]
    exact one_ne_zero

  have hinner : ∀ b ∈ data.Φ.support,
      (∑ a ∈ (data.Φ.coeff b).support,
        (((data.Φ.coeff b).coeff a : ℤ) : S) * (0 : S) ^ (q * (q + 1) - a - q * b))
        = if b = q + 1 then 1 else if b = q then (((data.Φ.coeff q).coeff q : ℤ) : S) else 0 := by
    intro b hb
    have hb' : b ≤ q + 1 := by
      have h := Polynomial.le_natDegree_of_mem_supp b hb
      rwa [hdΦ] at h
    by_cases hb1 : b = q + 1
    · subst hb1
      rw [if_pos rfl, hc1]
      have hs : (1 : Polynomial ℤ).support ⊆ {0} := by
        rw [← Polynomial.C_1]
        exact Polynomial.support_C_subset _
      rw [Finset.sum_subset hs]
      · rw [Finset.sum_singleton, Polynomial.coeff_one_zero, Int.cast_one, one_mul, Nat.sub_zero, Nat.sub_self,
          pow_zero]
      · intro a _ ha
        rw [Polynomial.notMem_support_iff.mp ha, Int.cast_zero, zero_mul]
    rw [if_neg hb1]
    by_cases hbq : b = q
    · subst hbq
      rw [if_pos rfl]
      rw [Finset.sum_eq_single b]
      · rw [show b * (b + 1) - b - b * b = 0 by omega, pow_zero, mul_one]
      · intro a ha hne
        have hle : a ≤ b := by
          have h := supp_bound (data := data) hq hsym hb ha
          have : a ≤ b * (b + 1) - b * b := by omega
          rwa [hqq, Nat.add_sub_cancel_left] at this
        have hlt : a < b := lt_of_le_of_ne hle hne
        rw [zero_pow (by omega), mul_zero]
      · intro hnot
        rw [Polynomial.notMem_support_iff.mp hnot, Int.cast_zero, zero_mul]
    · rw [if_neg hbq]
      refine Finset.sum_eq_zero fun a ha => ?_
      have ha' := supp_bound' (data := data) ha
      have hlt : b ≤ q - 1 := by omega
      have hqb : q * b ≤ q * q - q := by
        have h := Nat.mul_le_mul_left q hlt
        rwa [Nat.mul_sub_one] at h
      have h2q := hq.two_le
      have hpos : 0 < q * (q + 1) - a - q * b := by
        have hb1' : b + 1 ≤ q := by omega
        have h1 : q * b + q ≤ q * q := by
          have h := Nat.mul_le_mul_left q hb1'
          rwa [Nat.mul_add_one] at h
        have h2 : q * (q + 1) = q * q + q := Nat.mul_add_one q q
        have h3 : a + q * b < q * (q + 1) := by
          rw [h2]
          linarith
        omega
      rw [zero_pow hpos.ne', mul_zero]
  ext n
  rw [normPoly, Polynomial.sum_def, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow, Polynomial.sum_def]
  rw [Finset.sum_ite_eq, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow]
  by_cases hn : n ∈ data.Φ.support
  · rw [if_pos hn, hinner n hn]
    by_cases hn1 : n = q + 1
    · rw [if_pos hn1, if_pos hn1, if_neg (by omega), mul_zero, add_zero]
    · rw [if_neg hn1, if_neg hn1, zero_add]
      by_cases hnq : n = q
      · rw [if_pos hnq, if_pos hnq, mul_one]
      · rw [if_neg hnq, if_neg hnq, mul_zero]
  · rw [if_neg hn]
    have hn1 : n ≠ q + 1 := fun h => hn (h ▸ hmem)
    rw [if_neg hn1, zero_add]
    by_cases hnq : n = q
    · subst hnq
      rw [if_pos rfl, mul_one, Polynomial.notMem_support_iff.mp hn, Polynomial.coeff_zero, Int.cast_zero]
    · rw [if_neg hnq, mul_zero]

private theorem coeff_q_q_modEq (hq : q.Prime) (hKr : KroneckerCongruence q data) :
    ((((data.Φ.coeff q).coeff q : ℤ)) : ZMod q) = -1 := by
  have h := congrArg (fun P : Polynomial (Polynomial (ZMod q)) => (P.coeff q).coeff q)
    (hKr : reduceModBivar q data.Φ = _)
  simp only [reduceModBivar, Polynomial.coe_mapRingHom, Polynomial.coeff_map, eq_intCast] at h
  rw [h]
  have h0 : q ≠ 0 := hq.ne_zero
  have h1 : q ≠ 1 := hq.one_lt.ne'
  have e : (C (X : Polynomial (ZMod q)) ^ q - X) * (C X - X ^ q)
      = C (X ^ (q + 1)) - C (X ^ q) * X ^ q - C X * X ^ 1 + X ^ (q + 1) := by
    simp only [map_pow, pow_one]
    ring
  rw [e, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_C,
    if_neg h0, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, if_neg h1, Polynomial.coeff_X_pow, if_neg (by omega : q ≠ q + 1)]
  simp

private theorem exists_root_normPoly (hq : q.Prime) (hsym : EvalSymm data.Φ) (hKr : KroneckerCongruence q data)
    (hqA : ((q : ℕ) : A) ∈ nonunits A) (u : A) (hu : u ∈ nonunits A) :
    ∃ b : A, (normPoly data A u).eval b = 0 ∧ (b - 1) ∈ nonunits A ∧
      IsUnit ((derivative (normPoly data A u)).eval b) := by
  classical
  haveI : NeZero q := ⟨hq.ne_zero⟩

  have hures : residue A u = 0 := (residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hu)
  have hqres : ((q : ℕ) : ResidueField A) = 0 := by
    rw [← map_natCast (residue A), residue_eq_zero_iff]
    exact (mem_maximalIdeal _).mpr hqA
  have hc : ((((data.Φ.coeff q).coeff q : ℤ)) : ResidueField A) = -1 := by
    have h := coeff_q_q_modEq (data := data) hq hKr
    rw [← sub_eq_zero, sub_neg_eq_add, ← Int.cast_one, ← Int.cast_add, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    obtain ⟨m, hm⟩ := h
    rw [← sub_eq_zero, sub_neg_eq_add, ← Int.cast_one, ← Int.cast_add, hm, Int.cast_mul, Int.cast_natCast,
      hqres, zero_mul]
  have hred : (normPoly data A u).map (residue A) = X ^ q * (X - 1) := by
    rw [normPoly_map, hures, normPoly_zero (data := data) hq hsym, hc, map_neg, map_one]
    ring

  set g := normPoly data A u with hg
  have hgm := monic_normPoly (data := data) (S := A) hq u
  set gQ := g.map (algebraMap A (AlgebraicClosure ℚ)) with hgQ
  have hgQm : gQ.Monic := hgm.1.map _
  have hsplit : gQ.Splits := IsAlgClosed.splits _
  have hrootsA : ∀ r ∈ gQ.roots, r ∈ A := by
    intro r hr
    have hint : IsIntegral A r := ⟨g, hgm.1, by
      rw [← Polynomial.eval_map]
      exact (Polynomial.mem_roots hgQm.ne_zero).mp hr⟩
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := AlgebraicClosure ℚ)).mp hint
    rw [← hy]
    exact y.2

  let lift : AlgebraicClosure ℚ → A := fun r => if h : r ∈ A then ⟨r, h⟩ else 0
  have hlift : ∀ r ∈ gQ.roots, ((lift r : A) : AlgebraicClosure ℚ) = r := by
    intro r hr
    simp only [lift, dif_pos (hrootsA r hr)]
  have hprod : g = (gQ.roots.map fun r => X - C (lift r)).prod := by
    apply Polynomial.map_injective (algebraMap A (AlgebraicClosure ℚ)) Subtype.val_injective
    rw [Polynomial.map_multiset_prod, Multiset.map_map]
    have hcongr : gQ.roots.map ((Polynomial.map (algebraMap A (AlgebraicClosure ℚ))) ∘ fun r => X - C (lift r))
        = gQ.roots.map fun r => X - C r := by
      refine Multiset.map_congr rfl fun r hr => ?_
      simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      rw [show algebraMap A (AlgebraicClosure ℚ) (lift r) = r from hlift r hr]
    rw [hcongr, ← hgQ]
    conv_lhs => rw [hsplit.eq_prod_roots_of_monic hgQm]

  have heval : ((gQ.roots.map fun r => (1 : ResidueField A) - residue A (lift r)).prod) = 0 := by
    have h := congrArg (fun P : Polynomial A => (P.map (residue A)).eval 1) hprod
    beta_reduce at h
    rw [hred, Polynomial.map_multiset_prod, Multiset.map_map, Polynomial.eval_multiset_prod, Multiset.map_map]
      at h
    rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one, sub_self,
      mul_zero] at h
    have key : (gQ.roots.map fun r => (1 : ResidueField A) - residue A (lift r)).prod
        = (gQ.roots.map (Polynomial.eval 1 ∘ (Polynomial.map (residue A) ∘ fun r => X - C (lift r)))).prod := by
      congr 1
      refine Multiset.map_congr rfl fun r _ => ?_
      simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [key]
    exact h.symm
  obtain ⟨r, hr, ht0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp heval)
  have hres1 : residue A (lift r) = 1 := (sub_eq_zero.mp ht0).symm
  refine ⟨lift r, ?_, ?_, ?_⟩
  ·
    apply Subtype.val_injective
    show algebraMap A (AlgebraicClosure ℚ) (g.eval (lift r)) = ((0 : A) : AlgebraicClosure ℚ)
    rw [ZeroMemClass.coe_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ← hgQ]
    change Polynomial.eval ((lift r : A) : AlgebraicClosure ℚ) gQ = 0
    rw [hlift r hr]
    exact (Polynomial.mem_roots hgQm.ne_zero).mp hr
  ·
    rw [← mem_maximalIdeal, ← residue_eq_zero_iff, map_sub, map_one, hres1, sub_self]
  ·
    rw [← residue_ne_zero_iff_isUnit, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map,
      ← Polynomial.derivative_map, hred, hres1]
    have hd : derivative ((X : Polynomial (ResidueField A)) ^ q * (X - 1)) = X ^ q := by
      rw [show (X : Polynomial (ResidueField A)) ^ q * (X - 1) = X ^ (q + 1) - X ^ q by ring,
        Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X_pow, Nat.cast_add,
        Nat.cast_one, hqres, zero_add, Polynomial.C_1, one_mul, Nat.add_sub_cancel, map_zero, zero_mul,
        sub_zero]
    rw [hd, Polynomial.eval_pow, Polynomial.eval_X, one_pow]
    exact one_ne_zero

section LevelElements

theorem jqModC_mem_gammaH (L : ℕ) [NeZero L] (H₀ : Subgroup (ZMod L)ˣ) :
    jqModC ℚ ∈ qExpFunctionFieldC ℚ (CohCarrier.GammaH L H₀) :=
  qExpFunctionFieldC_mono ℚ (CohCarrier.GammaH_le_Gamma0 _)
    (ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ L (ModularCurve.jqModC_mem_full ℚ L))

def jBarOf (L : ℕ) [NeZero L] (H₀ : Subgroup (ZMod L)ˣ) : ↥(xHFunctionFieldBar L H₀) :=
  ⟨jqModC (AlgebraicClosure ℚ), by
    have h := coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqModC_mem_gammaH L H₀)
    have e : coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ) :=
      map_jqModC (K := ℚ) (algebraMap ℚ (AlgebraicClosure ℚ))
    rw [e] at h
    exact h⟩

@[scoped simp] theorem coe_jBarOf (L : ℕ) [NeZero L] (H₀ : Subgroup (ZMod L)ˣ) :
    ((jBarOf L H₀ : ↥(xHFunctionFieldBar L H₀)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := rfl

theorem jBarOf_ne_zero (L : ℕ) [NeZero L] (H₀ : Subgroup (ZMod L)ˣ) : jBarOf L H₀ ≠ 0 := by
  intro h
  have hc := congrArg (fun x : ↥(xHFunctionFieldBar L H₀) => (x : LaurentSeries (AlgebraicClosure ℚ)).coeff (-1)) h
  simp only [coe_jBarOf, ZeroMemClass.coe_zero] at hc
  rw [coeff_jqModC_neg_one] at hc
  simp at hc

theorem jBarOf_ne_algebraMap (L : ℕ) [NeZero L] (H₀ : Subgroup (ZMod L)ˣ) (c : AlgebraicClosure ℚ) :
    jBarOf L H₀ ≠ algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar L H₀) c := by
  intro h
  have hc := congrArg (fun x : ↥(xHFunctionFieldBar L H₀) => (x : LaurentSeries (AlgebraicClosure ℚ)).coeff (-1)) h
  simp only [coe_jBarOf] at hc
  have e2 : ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar L H₀) c : ↥(xHFunctionFieldBar L H₀)) :
      LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.single 0 c :=
    ModularCurve.algebraMap_laurentSeries_eq_single (AlgebraicClosure ℚ) c
  rw [coeff_jqModC_neg_one, e2, HahnSeries.coeff_single_of_ne (show (-1 : ℤ) ≠ 0 by decide)] at hc
  exact one_ne_zero hc

end LevelElements

section AlphaH

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
  (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]

def YH : ↥(xHFunctionFieldBar M H) :=
  ⟨qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)), by
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    have h := ModularCurve.xHFunctionFieldBar_div_sup_adjoin_qExpand_jqModC_eq_xHFunctionFieldBar p M H hpM hpM2 hHp
    have hm : qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) ∈
        xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) ⊔
          IntermediateField.adjoin (AlgebraicClosure ℚ) {qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ))} :=
      (le_sup_right : IntermediateField.adjoin (AlgebraicClosure ℚ) _ ≤ _) (IntermediateField.mem_adjoin_simple_self _ _)
    rw [h] at hm
    exact hm⟩

@[scoped simp] theorem coe_YH : ((YH p M H hpM hpM2 hHp : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
    qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) := rfl

theorem intPolyRingHom_ext' {S : Type*} [Semiring S] {f g : Polynomial ℤ →+* S}
    (h : f Polynomial.X = g Polynomial.X) : f = g :=
  Polynomial.ringHom_ext
    (fun a => DFunLike.congr_fun (RingHom.ext_int (f.comp Polynomial.C) (g.comp Polynomial.C)) a) h

theorem modularPolynomial_eval₂_jBar_YH (data : ModularPolynomialData p) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jBarOf M H)).toRingHom (YH p M H hpM hpM2 hHp) = 0 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  apply (algebraMap ↥(xHFunctionFieldBar M H) (LaurentSeries (AlgebraicClosure ℚ))).injective
  rw [Polynomial.hom_eval₂, map_zero]
  have hcomp : (algebraMap ↥(xHFunctionFieldBar M H) (LaurentSeries (AlgebraicClosure ℚ))).comp
      (Polynomial.aeval (R := ℤ) (jBarOf M H)).toRingHom
      = (coeffEmb (AlgebraicClosure ℚ)).comp evalAtJ := by
    apply intPolyRingHom_ext'
    simp only [RingHom.coe_comp, Function.comp_apply, evalAtJ_X]
    show algebraMap _ _ (Polynomial.aeval (R := ℤ) (jBarOf M H) Polynomial.X) = _
    rw [Polynomial.aeval_X]
    show jqModC (AlgebraicClosure ℚ) = coeffEmb (AlgebraicClosure ℚ) jq
    rw [← jqModC_rat]
    exact (map_jqModC (K := ℚ) (algebraMap ℚ (AlgebraicClosure ℚ))).symm
  rw [hcomp]
  have hval : algebraMap ↥(xHFunctionFieldBar M H) (LaurentSeries (AlgebraicClosure ℚ)) (YH p M H hpM hpM2 hHp)
      = coeffEmb (AlgebraicClosure ℚ) (jqN p) := by
    show qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) = _
    rw [jqN, ← jqModC_rat]
    symm
    have h1 := ModularCurve.coeffSemilinearAut.coeffMap_qExpand (algebraMap ℚ (AlgebraicClosure ℚ)) p (jqModC ℚ)
    rw [ModularCurve.coeffSemilinearAut.coeffMap_jqModC] at h1
    exact h1
  rw [hval, ← Polynomial.hom_eval₂, data.eval_eq_zero, map_zero]

def tInfH : ↥(xHFunctionFieldBar M H) := YH p M H hpM hpM2 hHp / jBarOf M H ^ p

end AlphaH

section MinpolyH

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
  (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
  (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
  (hα : α.IsIntegral)
  (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))

include hα_coe in

theorem alpha_jBarOf : α (jBarOf (M / p) (infSubgroup p M H hpM)) = jBarOf M H :=
  Subtype.ext (by rw [hα_coe]; rfl)

theorem algebraMap_algAlphaH (x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
    letI := algebraAlong α
    algebraMap ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) x = α x := rfl

include hpM2 hHp hα_coe

theorem finrank_eq :
    letI := algebraAlong α
    Module.finrank ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) = p + 1 := by
  letI := algebraAlong α
  have h := ModularCurve.finrankAlong_eq_add_one_of_coe_eq_xHFunctionFieldBar p M H hpM hpM2 hHp α hα_coe
  unfold finrankAlong at h
  exact h

theorem moduleFinite :
    letI := algebraAlong α
    Module.Finite ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) := by
  letI := algebraAlong α
  exact Module.finite_of_finrank_pos (by rw [finrank_eq p M H hpM hpM2 hHp α hα_coe]; omega)

theorem adjoin_YH_eq_top :
    letI := algebraAlong α
    IntermediateField.adjoin ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) {YH p M H hpM hpM2 hHp} = ⊤ := by
  letI := algebraAlong α
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  set E := IntermediateField.adjoin ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) {YH p M H hpM hpM2 hHp} with hE
  rw [eq_top_iff]
  intro z _

  let S : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
    (E.restrictScalars (AlgebraicClosure ℚ)).map (xHFunctionFieldBar M H).val
  have hmemS : ∀ y : ↥(xHFunctionFieldBar M H), y ∈ E → (y : LaurentSeries (AlgebraicClosure ℚ)) ∈ S := fun y hy =>
    (IntermediateField.mem_map (S := IntermediateField.restrictScalars (AlgebraicClosure ℚ) E)).mpr ⟨y, (IntermediateField.mem_restrictScalars _).mpr hy, rfl⟩
  have hS1 : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) ≤ S := by
    intro x hx
    have h1 := hmemS (α ⟨x, hx⟩) (IntermediateField.algebraMap_mem E ⟨x, hx⟩)
    rwa [hα_coe] at h1
  have hS2 : IntermediateField.adjoin (AlgebraicClosure ℚ) {qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ))} ≤ S := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact hmemS _ (IntermediateField.mem_adjoin_simple_self _ (YH p M H hpM hpM2 hHp))
  have hS : xHFunctionFieldBar M H ≤ S := by
    rw [← ModularCurve.xHFunctionFieldBar_div_sup_adjoin_qExpand_jqModC_eq_xHFunctionFieldBar p M H hpM hpM2 hHp]
    exact sup_le hS1 hS2
  obtain ⟨z', hz', hzz'⟩ := (IntermediateField.mem_map (S := IntermediateField.restrictScalars (AlgebraicClosure ℚ) E)).mp (hS z.2)
  have : z' = z := Subtype.ext hzz'
  rw [← this]
  exact (IntermediateField.mem_restrictScalars _).mp hz'

theorem minpoly_YH (data : ModularPolynomialData p) :
    letI := algebraAlong α
    minpoly ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (YH p M H hpM hpM2 hHp)
      = data.Φ.map (Polynomial.aeval (R := ℤ) (jBarOf (M / p) (infSubgroup p M H hpM))).toRingHom := by
  letI := algebraAlong α
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI := moduleFinite p M H hpM hpM2 hHp α hα_coe
  set P := data.Φ.map (Polynomial.aeval (R := ℤ) (jBarOf (M / p) (infSubgroup p M H hpM))).toRingHom with hP
  have hPm : P.Monic := data.monic.map _
  have hPdeg : P.natDegree = p + 1 := by
    rw [hP, data.monic.natDegree_map, data.natDegree_eq, dedekindPsi_prime' hp]
  have hPY : Polynomial.aeval (YH p M H hpM hpM2 hHp) P = 0 := by
    rw [Polynomial.aeval_def, hP, Polynomial.eval₂_map]
    have hc : (algebraMap ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H)).comp
        (Polynomial.aeval (R := ℤ) (jBarOf (M / p) (infSubgroup p M H hpM))).toRingHom
        = (Polynomial.aeval (R := ℤ) (jBarOf M H)).toRingHom := by
      apply intPolyRingHom_ext'
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X]
      exact alpha_jBarOf p M H hpM α hα_coe
    rw [hc]
    exact modularPolynomial_eval₂_jBar_YH p M H hpM hpM2 hHp data
  have hint : IsIntegral ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (YH p M H hpM hpM2 hHp) :=
    Algebra.IsIntegral.isIntegral _
  have hdvd := minpoly.dvd _ _ hPY
  have hdegY : (minpoly ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (YH p M H hpM hpM2 hHp)).natDegree = p + 1 := by
    rw [← IntermediateField.adjoin.finrank hint, adjoin_YH_eq_top p M H hpM hpM2 hHp α hα_coe,
      IntermediateField.finrank_top', finrank_eq p M H hpM hpM2 hHp α hα_coe]
  symm
  exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hPm hdvd (by rw [hPdeg, hdegY])

theorem minpoly_tInfH (data : ModularPolynomialData p) (hsym : EvalSymm data.Φ)
    (w : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (hJ' : (jBarOf (M / p) (infSubgroup p M H hpM))⁻¹ ∈ w.toValuationSubring) :
    letI := algebraAlong α
    (normPoly data w.toValuationSubring ⟨(jBarOf (M / p) (infSubgroup p M H hpM))⁻¹, hJ'⟩).map
        (algebraMap w.toValuationSubring ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
      = minpoly ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (tInfH p M H hpM hpM2 hHp) ∧
    (minpoly ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (tInfH p M H hpM hpM2 hHp)).natDegree
      = Module.finrank ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) ∧
    Module.finrank ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) = p + 1 := by
  letI := algebraAlong α
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI := moduleFinite p M H hpM hpM2 hHp α hα_coe
  have hfr := finrank_eq p M H hpM hpM2 hHp α hα_coe
  set J := jBarOf (M / p) (infSubgroup p M H hpM) with hJdef
  have hJ0 : J ≠ 0 := jBarOf_ne_zero _ _
  have hy_int : IsIntegral ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (YH p M H hpM hpM2 hHp) := Algebra.IsIntegral.isIntegral _
  have hdeg_y : (minpoly ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (YH p M H hpM hpM2 hHp)).natDegree = p + 1 := by
    rw [minpoly_YH p M H hpM hpM2 hHp α hα_coe data, data.monic.natDegree_map, data.natDegree_eq, dedekindPsi_prime' hp]

  have hJα : algebraMap ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) J = jBarOf M H := by
    rw [algebraMap_algAlphaH]
    exact alpha_jBarOf p M H hpM α hα_coe
  have ht : tInfH p M H hpM hpM2 hHp
      = algebraMap ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) (J⁻¹ ^ p)
        * YH p M H hpM hpM2 hHp := by
    rw [map_pow, map_inv₀, hJα]
    show YH p M H hpM hpM2 hHp / jBarOf M H ^ p = _
    rw [div_eq_mul_inv, inv_pow]
    exact mul_comm _ _
  have hJM0 : jBarOf M H ≠ 0 := jBarOf_ne_zero _ _
  have hy' : YH p M H hpM hpM2 hHp
      = algebraMap ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) (J ^ p)
        * tInfH p M H hpM hpM2 hHp := by
    rw [ht, ← mul_assoc, ← map_mul, ← mul_pow, mul_inv_cancel₀ hJ0, one_pow, map_one, one_mul]
  have hadj : IntermediateField.adjoin ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) {tInfH p M H hpM hpM2 hHp}
      = IntermediateField.adjoin ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) {YH p M H hpM hpM2 hHp} := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff, ht]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self _ _)
    · rw [IntermediateField.adjoin_simple_le_iff, hy']
      exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self _ _)
  have ht_int : IsIntegral ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (tInfH p M H hpM hpM2 hHp) := Algebra.IsIntegral.isIntegral _
  have hdeg_t : (minpoly ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (tInfH p M H hpM hpM2 hHp)).natDegree = p + 1 := by
    rw [← IntermediateField.adjoin.finrank ht_int, hadj, IntermediateField.adjoin.finrank hy_int, hdeg_y]

  have hQF : (normPoly data w.toValuationSubring ⟨J⁻¹, hJ'⟩).map
      (algebraMap w.toValuationSubring ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
      = normPoly data ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) J⁻¹ :=
    normPoly_map _ _
  have hQFm := monic_normPoly (data := data) (S := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) hp J⁻¹
  have haeval : Polynomial.aeval (tInfH p M H hpM hpM2 hHp)
      (normPoly data ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) J⁻¹) = 0 := by
    rw [Polynomial.aeval_def]
    change Polynomial.eval₂ α.toRingHom _ _ = 0
    have hjM0 : jBarOf M H ≠ 0 := hJM0
    have hz : α.toRingHom J⁻¹ = (jBarOf M H)⁻¹ := by
      show α J⁻¹ = _
      rw [map_inv₀, alpha_jBarOf p M H hpM α hα_coe]
    rw [Polynomial.eval₂_eq_eval_map, normPoly_map, hz]
    show Polynomial.eval (YH p M H hpM hpM2 hHp / jBarOf M H ^ p) _ = 0
    rw [normPoly_eval_div (data := data) hp hsym (jBarOf M H) (YH p M H hpM hpM2 hHp) hjM0,
      modularPolynomial_eval₂_jBar_YH, mul_zero]
  have hdvd : minpoly ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (tInfH p M H hpM hpM2 hHp)
      ∣ normPoly data ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) J⁻¹ :=
    minpoly.dvd _ _ haeval
  have heq : normPoly data ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) J⁻¹
      = minpoly ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (tInfH p M H hpM hpM2 hHp) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic ht_int) hQFm.1 hdvd
      (by rw [hQFm.2, hdeg_t])
  refine ⟨?_, ?_, hfr⟩
  · rw [hQF, heq]
  · rw [hdeg_t, hfr]

end MinpolyH

section PlaceH

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
  (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
  (hα : α.IsIntegral)
  (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
  [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]

include hpM2 hHp hA hα_coe in
theorem cusp_inftyH
    (w : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (hw : ∀ a : A, w.ord (jBarOf (M / p) (infSubgroup p M H hpM)
      - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ)) ≤ 0) :
    ∃ c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      c.restrictAlong α hα = w ∧
      ∃ τ : A, IsLocalRing.residue A τ = 1 ∧ c.HasValue (tInfH p M H hpM hpM2 hHp) (τ : AlgebraicClosure ℚ) := by
  letI := algebraAlong α
  classical
  have hq : p.Prime := Fact.out
  haveI : NeZero p := ⟨hq.ne_zero⟩
  haveI : CharP (IsLocalRing.ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA

  obtain ⟨data, hKr⟩ := ModularCurve.exists_kroneckerCongruence_of_prime p

  have hsym : EvalSymm data.Φ := by
    obtain ⟨d', hd'⟩ := exists_modularPolynomialData_evalSymm p
    rw [ModularPolynomialData.eq_all p data d']
    exact hd'
  have hJ0 : (jBarOf (M / p) (infSubgroup p M H hpM)) ≠ 0 := jBarOf_ne_zero _ _

  have hordJ : w.ord (jBarOf (M / p) (infSubgroup p M H hpM)) ≤ 0 := by
    have h := hw 0
    simp only [ZeroMemClass.coe_zero, map_zero, sub_zero] at h
    exact h
  have hJ' : (jBarOf (M / p) (infSubgroup p M H hpM))⁻¹ ∈ w.toValuationSubring :=
    w.mem_of_ord_nonneg (inv_ne_zero hJ0) (by rw [w.ord_inv]; omega)

  have hdeg1 : w.deg = 1 := by
    haveI := (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM)).1
    apply AlgebraicCurve.Place.deg_eq_one_of_isAlgClosed w
    haveI : Module.Finite (AlgebraicClosure ℚ) w.ResidueField := AlgebraicCurve.IsCurveOver.finite_residueField w
    exact Module.finrank_pos.ne'
  have hsurj := surjective_algebraMap_residueField_of_deg_eq_one w hdeg1
  obtain ⟨u, hu, -⟩ := w.exists_hasValue_of_surjective hsurj hJ'

  have huA : ∃ hu' : u ∈ A, (⟨u, hu'⟩ : A) ∈ nonunits A := by
    by_cases hu0 : u = 0
    · subst hu0
      refine ⟨A.zero_mem, ?_⟩
      have e : (⟨(0 : AlgebraicClosure ℚ), A.zero_mem⟩ : A) = 0 := rfl
      rw [e]
      exact not_isUnit_zero
    ·
      have hunit : IsUnit (⟨(jBarOf (M / p) (infSubgroup p M H hpM))⁻¹, hJ'⟩ : w.toValuationSubring) := by
        rw [← residue_ne_zero_iff_isUnit, hu.residue_eq]
        exact (_root_.map_ne_zero _).mpr hu0
      have hordJ' : w.ord (jBarOf (M / p) (infSubgroup p M H hpM))⁻¹ = 0 := by
        obtain ⟨v, hv⟩ := hunit
        have h := w.ord_coe_unit v
        rwa [hv] at h
      have hJmem : (jBarOf (M / p) (infSubgroup p M H hpM)) ∈ w.toValuationSubring :=
        w.mem_of_ord_nonneg hJ0 (by rw [w.ord_inv] at hordJ'; omega)
      have hval : w.HasValue (jBarOf (M / p) (infSubgroup p M H hpM)) u⁻¹ := by
        refine ⟨hJmem, ?_⟩
        have hprod : (⟨(jBarOf (M / p) (infSubgroup p M H hpM)), hJmem⟩ : w.toValuationSubring) * ⟨(jBarOf (M / p) (infSubgroup p M H hpM))⁻¹, hJ'⟩ = 1 :=
          Subtype.ext (mul_inv_cancel₀ hJ0)
        have h1 := congrArg (residue w.toValuationSubring) hprod
        rw [map_mul, map_one, hu.residue_eq] at h1
        rw [map_inv₀]
        exact eq_inv_of_mul_eq_one_left h1
      have hpos : 0 < w.ord ((jBarOf (M / p) (infSubgroup p M H hpM)) - algebraMap _ _ u⁻¹) :=
        ord_sub_pos_of_hasValue w hval (jBarOf_ne_algebraMap _ _ _)
      have hnotA : u⁻¹ ∉ A := fun hmem => absurd hpos (not_lt.mpr (hw ⟨u⁻¹, hmem⟩))
      have huA' : u ∈ A := by
        rcases A.mem_or_inv_mem u with h | h
        · exact h
        · exact absurd h hnotA
      refine ⟨huA', fun hunitA => hnotA ?_⟩
      obtain ⟨v, hv⟩ := hunitA
      have h1 : ((v⁻¹ : Aˣ) : A).1 * u = 1 := by
        have h := congrArg Subtype.val v.inv_mul
        rw [hv] at h
        exact h
      rw [← eq_inv_of_mul_eq_one_left h1]
      exact Subtype.mem _
  obtain ⟨huA', hunon⟩ := huA
  obtain ⟨uA, huAdef⟩ : ∃ uA : A, uA = ⟨u, huA'⟩ := ⟨_, rfl⟩
  rw [← huAdef] at hunon

  have hqA : ((p : ℕ) : A) ∈ nonunits A := by
    intro hunitq
    have h := congrArg (IsLocalRing.residue ↥A) (IsUnit.mul_val_inv hunitq)
    rw [map_mul, map_one, map_natCast, CharP.cast_eq_zero (IsLocalRing.ResidueField ↥A) p, zero_mul] at h
    exact zero_ne_one h

  obtain ⟨b, hbroot, hb1, hbder⟩ := exists_root_normPoly (data := data) hq hsym hKr hqA uA hunon

  have hredb : IsLocalRing.residue ↥A b = 1 := by
    have h := red_eq_zero_of_mem_nonunits (q := p) hq (IsLocalRing.residue ↥A) (b - 1) hb1
    rwa [map_sub, map_one, sub_eq_zero] at h

  obtain ⟨Q, hQdef⟩ : ∃ Q : Polynomial w.toValuationSubring,
      Q = normPoly data w.toValuationSubring ⟨(jBarOf (M / p) (infSubgroup p M H hpM))⁻¹, hJ'⟩ := ⟨_, rfl⟩
  have hQm : Q.Monic := by
    rw [hQdef]; exact (monic_normPoly (data := data) hq _).1
  obtain ⟨bO, hbOdef⟩ : ∃ bO : w.toValuationSubring,
      bO = algebraMap (AlgebraicClosure ℚ) w.toValuationSubring (b : AlgebraicClosure ℚ) := ⟨_, rfl⟩
  haveI : CharZero (↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) (↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))).injective
  haveI : CharZero (↥(xHFunctionFieldBar M H)) :=
    charZero_of_injective_algebraMap
      (algebraMap (AlgebraicClosure ℚ) (↥(xHFunctionFieldBar M H))).injective
  have hT : ∀ (L : ℕ) (H₀ : Subgroup (ZMod L)ˣ), ModularGroup.T ∈ CohCarrier.GammaH L H₀ := fun L H₀ => by
    apply ModularCurve.Gamma1_le_GammaH
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.T]
  haveI : (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM))
  haveI : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)
  have hfin : FiniteAlong (AlgebraicClosure ℚ) α :=
    ModularCurve.finiteAlong_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ) (hT _ _) (hT _ _) α
  haveI : Module.Finite (↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (↥(xHFunctionFieldBar M H)) := by
    have h := hfin
    unfold FiniteAlong at h
    exact h

  have hx : (Q.map (algebraMap w.toValuationSubring (↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))))).eval₂
      (α).toRingHom ((tInfH p M H hpM hpM2 hHp)) = 0 := by
    rw [hQdef]
    have hL4a := (minpoly_tInfH p M H hpM hpM2 hHp α hα_coe data hsym w hJ').1

    rw [hL4a]
    have h := minpoly.aeval ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (tInfH p M H hpM hpM2 hHp)
    rw [Polynomial.aeval_def] at h
    exact h

  have hres_eval : ∀ P : Polynomial w.toValuationSubring,
      residue w.toValuationSubring (P.eval bO)
        = (P.map (residue w.toValuationSubring)).eval
            (algebraMap (AlgebraicClosure ℚ) w.ResidueField (b : AlgebraicClosure ℚ)) := by
    intro P
    rw [Polynomial.eval_map, ← w.residue_algebraMap, hbOdef]
    exact (Polynomial.eval₂_at_apply _ _).symm
  have hQres : Q.map (residue w.toValuationSubring)
      = (normPoly data (AlgebraicClosure ℚ) u).map (algebraMap (AlgebraicClosure ℚ) w.ResidueField) := by
    rw [hQdef, normPoly_map, normPoly_map]
    congr 1
    exact hu.residue_eq
  have hrootA : (normPoly data (AlgebraicClosure ℚ) u).eval (b : AlgebraicClosure ℚ) = 0 := by
    have h := congrArg A.subtype hbroot
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, normPoly_map, huAdef] at h
    exact h
  have hderA : (derivative (normPoly data (AlgebraicClosure ℚ) u)).eval (b : AlgebraicClosure ℚ) ≠ 0 := by
    have h : A.subtype ((derivative (normPoly data A uA)).eval b) ≠ 0 :=
      (_root_.map_ne_zero_iff _ Subtype.val_injective).mpr hbder.ne_zero
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ← Polynomial.derivative_map, normPoly_map,
      huAdef] at h
    exact h
  have hroot_mem : Q.eval bO ∈ maximalIdeal w.toValuationSubring := by
    rw [← residue_eq_zero_iff, hres_eval, hQres, Polynomial.eval_map, Polynomial.eval₂_at_apply, hrootA,
      map_zero]
  have hsimple : IsUnit ((derivative Q).eval bO) := by
    rw [← residue_ne_zero_iff_isUnit, hres_eval, ← Polynomial.derivative_map, hQres,
      Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    exact (_root_.map_ne_zero _).mpr hderA

  have hL4 := minpoly_tInfH p M H hpM hpM2 hHp α hα_coe data hsym w hJ'
  rw [← hQdef] at hL4
  obtain ⟨hQmin, hdeg, hfr⟩ := hL4
  have hroot_ne : ((Q.eval bO : w.toValuationSubring) : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) ≠ 0 := by
    intro h0
    have hint : IsIntegral (↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) ((tInfH p M H hpM hpM2 hHp)) := Algebra.IsIntegral.isIntegral _
    have hr : (minpoly (↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) ((tInfH p M H hpM hpM2 hHp))).IsRoot (bO : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) := by
      rw [← hQmin, Polynomial.IsRoot, Polynomial.eval_map]
      change Polynomial.eval₂ _ (algebraMap w.toValuationSubring (↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) bO) Q = 0
      rw [Polynomial.eval₂_at_apply]
      exact h0
    have h1 := Polynomial.degree_eq_one_of_irreducible_of_root (minpoly.irreducible hint) hr
    have h2 : (minpoly (↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) ((tInfH p M H hpM hpM2 hHp))).natDegree = 1 :=
      Polynomial.natDegree_eq_of_degree_eq_some h1
    rw [hdeg, hfr] at h2
    have := hq.two_le
    omega
  have hroot : 0 < w.ord ((Q.eval bO : w.toValuationSubring) : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :=
    ord_pos_of_not_isUnit w (fun hu' => (mem_maximalIdeal _).mp hroot_mem hu') hroot_ne

  have hnorm : w.ord (Algebra.norm (↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
        ((tInfH p M H hpM hpM2 hHp) - α (bO : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))))
        = w.ord ((Q.eval bO : w.toValuationSubring) : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) := by
    exact Place.ord_norm_sub_eq_ord_eval w Q hQmin hdeg bO

  obtain ⟨c, hc, hcval, -, -, -⟩ :=
    exists_place_over_of_simple_root_along (α) hα hfin w hQm hx bO
      hroot hsimple hnorm
  refine ⟨c, hc, b, hredb, hasValue_of_ord_sub_pos c ?_⟩
  have hb : α (bO : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
      = algebraMap (AlgebraicClosure ℚ) (↥(xHFunctionFieldBar M H)) (b : AlgebraicClosure ℚ) := by
    rw [hbOdef, Place.coe_algebraMap, AlgHom.commutes]
  rw [← hb]
  exact hcval

end PlaceH

end CuspNormalizationH
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_exists_restrictAlong_eq_and_isInftySide_of_forall_ord_sub_nonpos.CuspNormalizationH"

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    (b : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (hb : ∀ x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
      ((x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
      ∀ a : ↥A, b.ord (x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ)) ≤ 0) :
    ∃ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      W.restrictAlong α hα = b ∧ JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) W := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  have hw := hb (CuspNormalizationH.jBarOf (M / p) (infSubgroup p M H hpM)) rfl
  obtain ⟨W, hW, τ, hτ, hval⟩ := CuspNormalizationH.cusp_inftyH p M H hpM hpM2 hHp A hA α hα hα_coe b hw
  refine ⟨W, hW, ?_, CuspNormalizationH.jBarOf M H, CuspNormalizationH.YH p M H hpM hpM2 hHp, rfl, rfl, τ, hτ, hval⟩

  intro x hx a
  have hxα : x = α (CuspNormalizationH.jBarOf (M / p) (infSubgroup p M H hpM)) := by
    apply Subtype.ext
    rw [hα_coe]
    exact hx
  have h := AlgebraicCurve.Place.ord_restrictAlong α hα W
    (CuspNormalizationH.jBarOf (M / p) (infSubgroup p M H hpM)
      - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ))
  rw [map_sub, AlgHom.commutes, hW] at h
  rw [hxα, h]
  exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hw a)

end
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_exists_restrictAlong_eq_and_isInftySide_of_forall_ord_sub_nonpos.CuspNormalizationH"

end S_ModularCurve_JHPlaceSpecialization_exists_restrictAlong_eq_and_isInftySide_of_forall_ord_sub_nonpos
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_exists_restrictAlong_eq_and_isInftySide_of_forall_ord_sub_nonpos (solution)
