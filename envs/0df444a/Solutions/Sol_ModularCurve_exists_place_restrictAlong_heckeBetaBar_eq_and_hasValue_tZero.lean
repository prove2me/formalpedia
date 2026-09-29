-- Prove2me | solution 1 for ModularCurve.exists_place_restrictAlong_heckeBetaBar_eq_and_hasValue_tZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/9c34bbd1-6bf3-5e6d-a588-d7fc685d64fd

import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_AlgebraicCurve_exists_place_over_of_simple_root_along
import Theorems.Thm_AlgebraicCurve_Place_ord_norm_sub_eq_ord_eval
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaBar_of_prime
import Theorems.Thm_ModularCurve_minpoly_heckeAlphaBar_along_heckeBetaBar
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaBar
import Theorems.Thm_ModularCurve_ModularPolynomialData_eq_all
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_le
import Theorems.Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_le_mul_dedekindPsi_sub
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_place_restrictAlong_heckeBetaBar_eq_and_hasValue_tZero
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple Polynomial

noncomputable section

namespace CuspNormalization

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
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.sum_def,
    Finset.sum_mul, hae, Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_

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

private def jBar (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩

private theorem heckeAlphaBar_jBar (q : ℕ) [NeZero q] :
    heckeAlphaBar (AlgebraicClosure ℚ) N q (jBar N) = jFun N q :=
  Subtype.ext (by rw [coe_heckeAlphaBar]; rfl)

private theorem intPolyRingHom_ext {S : Type*} [Semiring S] {f g : Polynomial ℤ →+* S}
    (h : f Polynomial.X = g Polynomial.X) : f = g :=
  Polynomial.ringHom_ext
    (fun a => DFunLike.congr_fun (RingHom.ext_int (f.comp Polynomial.C) (g.comp Polynomial.C)) a) h

private theorem modularPolynomial_eval₂_jFun_jQFun (data : ModularPolynomialData q) [NeZero q] :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jFun N q)).toRingHom (jQFun N q) = 0 := by
  apply (algebraMap (modularFunctionFieldBar (N * q)) (LaurentSeries (AlgebraicClosure ℚ))).injective
  rw [Polynomial.hom_eval₂, map_zero]
  have hcomp : (algebraMap (modularFunctionFieldBar (N * q)) (LaurentSeries (AlgebraicClosure ℚ))).comp
      (Polynomial.aeval (R := ℤ) (jFun N q)).toRingHom
      = (coeffEmb (AlgebraicClosure ℚ)).comp evalAtJ := by
    apply intPolyRingHom_ext
    simp only [RingHom.coe_comp, Function.comp_apply, evalAtJ_X]
    show algebraMap _ _ (Polynomial.aeval (R := ℤ) (jFun N q) Polynomial.X) = _
    rw [Polynomial.aeval_X]
    rfl
  rw [hcomp]
  have hval : algebraMap (modularFunctionFieldBar (N * q)) (LaurentSeries (AlgebraicClosure ℚ)) (jQFun N q)
      = coeffEmb (AlgebraicClosure ℚ) (jqN q) := rfl
  rw [hval, ← Polynomial.hom_eval₂, data.eval_eq_zero, map_zero]

private theorem jBar_ne_zero : jBar N ≠ 0 := by
  intro h
  have hc : ((jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)).coeff (-1) = 0 := by
    rw [h]; simp
  have e1 : ((jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
      = jqModC (AlgebraicClosure ℚ) :=
    map_jqModC (K := ℚ) (algebraMap ℚ (AlgebraicClosure ℚ))
  rw [e1, coeff_jqModC_neg_one] at hc
  exact one_ne_zero hc

private theorem jBar_ne_algebraMap (c : AlgebraicClosure ℚ) :
    jBar N ≠ algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c := by
  intro h
  have hc := congrArg
    (fun x : modularFunctionFieldBar N => (x : LaurentSeries (AlgebraicClosure ℚ)).coeff (-1)) h
  have e1 : ((jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
      = jqModC (AlgebraicClosure ℚ) :=
    map_jqModC (K := ℚ) (algebraMap ℚ (AlgebraicClosure ℚ))
  have e2 : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c : modularFunctionFieldBar N) :
      LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.single 0 c := by
    exact ModularCurve.algebraMap_laurentSeries_eq_single (AlgebraicClosure ℚ) c
  have hL : ((jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)).coeff (-1) = 1 := by
    rw [e1]
    exact coeff_jqModC_neg_one (AlgebraicClosure ℚ)
  have hR : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c : modularFunctionFieldBar N) :
      LaurentSeries (AlgebraicClosure ℚ)).coeff (-1) = 0 := by
    rw [e2]
    exact HahnSeries.coeff_single_of_ne (show (-1 : ℤ) ≠ 0 by decide)
  rw [hL, hR] at hc
  exact one_ne_zero hc

private theorem heckeBetaBar_jBar (q : ℕ) [NeZero q] :
    heckeBetaBar (AlgebraicClosure ℚ) N q (jBar N) = jQFun N q :=
  Subtype.ext (by
    rw [coe_heckeBetaBar]
    exact (ModularCurve.coeffSemilinearAut.coeffMap_qExpand
      (algebraMap ℚ (AlgebraicClosure ℚ)) q jq).symm)

@[reducible] private noncomputable def algBeta :
    Algebra (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) :=
  algebraAlong (heckeBetaBar (AlgebraicClosure ℚ) N q)

private theorem modularPolynomial_eval₂_jQFun_jFun (data : ModularPolynomialData q) (hsym : EvalSymm data.Φ)
    [NeZero q] :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jQFun N q)).toRingHom (jFun N q) = 0 := by
  apply (algebraMap (modularFunctionFieldBar (N * q)) (LaurentSeries (AlgebraicClosure ℚ))).injective
  rw [Polynomial.hom_eval₂, map_zero]
  have hcomp : (algebraMap (modularFunctionFieldBar (N * q)) (LaurentSeries (AlgebraicClosure ℚ))).comp
      (Polynomial.aeval (R := ℤ) (jQFun N q)).toRingHom
      = (coeffEmb (AlgebraicClosure ℚ)).comp (evalAtJqN q) := by
    apply intPolyRingHom_ext
    simp only [RingHom.coe_comp, Function.comp_apply, evalAtJqN_X]
    show algebraMap _ _ (Polynomial.aeval (R := ℤ) (jQFun N q) Polynomial.X) = _
    rw [Polynomial.aeval_X]
    rfl
  rw [hcomp]
  have hval : algebraMap (modularFunctionFieldBar (N * q)) (LaurentSeries (AlgebraicClosure ℚ)) (jFun N q)
      = coeffEmb (AlgebraicClosure ℚ) jq := rfl
  rw [hval, ← Polynomial.hom_eval₂, evalAtJqN_def, hsym (jqN q) jq, ← evalAtJ_def, data.eval_eq_zero, map_zero]

private theorem normPoly_eval₂_tZero (hsym : EvalSymm data.Φ)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hJ' : (jBar N)⁻¹ ∈ w.toValuationSubring) :
    ((normPoly data w.toValuationSubring ⟨(jBar N)⁻¹, hJ'⟩).map
        (algebraMap w.toValuationSubring (modularFunctionFieldBar N))).eval₂
      (heckeBetaBar (AlgebraicClosure ℚ) N q).toRingHom (tZero N q) = 0 := by
  have hq : q.Prime := Fact.out
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hjQ0 : jQFun N q ≠ 0 := by
    rw [← heckeBetaBar_jBar (N := N) q]
    exact (_root_.map_ne_zero _).mpr jBar_ne_zero
  have hz : ((heckeBetaBar (AlgebraicClosure ℚ) N q).toRingHom.comp
      (algebraMap w.toValuationSubring (modularFunctionFieldBar N))) ⟨(jBar N)⁻¹, hJ'⟩ = (jQFun N q)⁻¹ := by
    show heckeBetaBar (AlgebraicClosure ℚ) N q ((jBar N)⁻¹) = _
    rw [map_inv₀, heckeBetaBar_jBar]
  have ht : tZero N q = jFun N q / jQFun N q ^ q := rfl
  rw [Polynomial.eval₂_map, Polynomial.eval₂_eq_eval_map, normPoly_map, hz, ht,
    normPoly_eval_div (data := data) hq hsym (jQFun N q) (jFun N q) hjQ0,
    modularPolynomial_eval₂_jQFun_jFun data hsym, mul_zero]

section Beta

attribute [local instance] algBeta

omit [NeZero N] in
private theorem algebraMap_eq_heckeBetaBar :
    algebraMap (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q))
      = (heckeBetaBar (AlgebraicClosure ℚ) N q).toRingHom := rfl

omit [NeZero N] in
private theorem algebraMap_algBeta (x : modularFunctionFieldBar N) :
    algebraMap (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) x
      = heckeBetaBar (AlgebraicClosure ℚ) N q x := rfl

private theorem minpoly_tZero (hqN : ¬ q ∣ N) (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hJ' : (jBar N)⁻¹ ∈ w.toValuationSubring) :
    (normPoly data w.toValuationSubring ⟨(jBar N)⁻¹, hJ'⟩).map
        (algebraMap w.toValuationSubring (modularFunctionFieldBar N))
      = minpoly (modularFunctionFieldBar N) (tZero N q) ∧
    (minpoly (modularFunctionFieldBar N) (tZero N q)).natDegree
      = Module.finrank (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) ∧
    Module.finrank (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) = q + 1 := by
  have hq : q.Prime := Fact.out
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hsym : EvalSymm data.Φ := by
    obtain ⟨d', hd'⟩ := exists_modularPolynomialData_evalSymm q
    rw [ModularPolynomialData.eq_all q data d']
    exact hd'
  haveI : Module.Finite (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) := by
    have h := finiteAlong_heckeBetaBar_of_prime (AlgebraicClosure ℚ) N q
    unfold FiniteAlong at h
    exact h
  have hfr : Module.finrank (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) = q + 1 := by
    have h := finrankAlong_heckeBetaBar (AlgebraicClosure ℚ) N q
    rw [if_neg hqN] at h
    exact h

  have hmin_y : minpoly (modularFunctionFieldBar N) (jFun N q)
      = data.Φ.map (Polynomial.aeval (R := ℤ) (jBar N)).toRingHom := by
    rw [← heckeAlphaBar_jBar (N := N) q]
    exact minpoly_heckeAlphaBar_along_heckeBetaBar N q hqN data hsym
  have hy_int : IsIntegral (modularFunctionFieldBar N) (jFun N q) := Algebra.IsIntegral.isIntegral _
  have hdeg_y : (minpoly (modularFunctionFieldBar N) (jFun N q)).natDegree = q + 1 := by
    rw [hmin_y, data.monic.natDegree_map, data.natDegree_eq, dedekindPsi_prime' hq]

  have hJβ : algebraMap (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) (jBar N) = jQFun N q := by
    rw [algebraMap_algBeta]
    exact heckeBetaBar_jBar (N := N) q
  have ht : tZero N q
      = algebraMap (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) ((jBar N)⁻¹ ^ q)
        * jFun N q := by
    rw [map_pow, map_inv₀, hJβ]
    show jFun N q / jQFun N q ^ q = _
    rw [div_eq_mul_inv, inv_pow]
    exact mul_comm _ _
  have hy' : jFun N q
      = algebraMap (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) ((jBar N) ^ q)
        * tZero N q := by
    rw [ht, ← mul_assoc, ← map_mul, ← mul_pow, mul_inv_cancel₀ jBar_ne_zero, one_pow, map_one, one_mul]
  have hadj : IntermediateField.adjoin (modularFunctionFieldBar N) {tZero N q}
      = IntermediateField.adjoin (modularFunctionFieldBar N) {jFun N q} := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff, ht]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self _ _)
    · rw [IntermediateField.adjoin_simple_le_iff, hy']
      exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self _ _)
  have ht_int : IsIntegral (modularFunctionFieldBar N) (tZero N q) := Algebra.IsIntegral.isIntegral _
  have hdeg_t : (minpoly (modularFunctionFieldBar N) (tZero N q)).natDegree = q + 1 := by
    rw [← IntermediateField.adjoin.finrank ht_int, hadj, IntermediateField.adjoin.finrank hy_int, hdeg_y]
  have hQF : (normPoly data w.toValuationSubring ⟨(jBar N)⁻¹, hJ'⟩).map
      (algebraMap w.toValuationSubring (modularFunctionFieldBar N))
      = normPoly data (modularFunctionFieldBar N) (jBar N)⁻¹ :=
    normPoly_map _ _
  have hQFm := monic_normPoly (data := data) (S := modularFunctionFieldBar N) hq (jBar N)⁻¹
  have haeval : Polynomial.aeval (tZero N q) (normPoly data (modularFunctionFieldBar N) (jBar N)⁻¹) = 0 := by
    rw [Polynomial.aeval_def, algebraMap_eq_heckeBetaBar]
    have h := normPoly_eval₂_tZero (data := data) hsym w hJ'
    rw [hQF] at h
    exact h
  have hdvd : minpoly (modularFunctionFieldBar N) (tZero N q)
      ∣ normPoly data (modularFunctionFieldBar N) (jBar N)⁻¹ :=
    minpoly.dvd _ _ haeval
  have heq : normPoly data (modularFunctionFieldBar N) (jBar N)⁻¹
      = minpoly (modularFunctionFieldBar N) (tZero N q) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic ht_int) hQFm.1 hdvd
      (by rw [hQFm.2, hdeg_t])
  refine ⟨?_, ?_, hfr⟩
  · rw [hQF, heq]
  · rw [hdeg_t, hfr]

include hKr in

private theorem cusp_zero (hqN : ¬ q ∣ N)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hw : ∀ a : A, w.ord
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0) :
    ∃ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      c.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ = w ∧
      ∃ τ : A, red τ = 1 ∧ c.HasValue (tZero N q) (τ : AlgebraicClosure ℚ) := by
  classical
  have hq : q.Prime := Fact.out
  haveI : NeZero q := ⟨hq.ne_zero⟩

  have hsym : EvalSymm data.Φ := by
    obtain ⟨d', hd'⟩ := exists_modularPolynomialData_evalSymm q
    rw [ModularPolynomialData.eq_all q data d']
    exact hd'
  change ∀ a : A, w.ord (jBar N
    - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0 at hw
  have hJ0 : jBar N ≠ 0 := jBar_ne_zero

  have hordJ : w.ord (jBar N) ≤ 0 := by
    have h := hw 0
    simp only [ZeroMemClass.coe_zero, map_zero, sub_zero] at h
    exact h
  have hJ' : (jBar N)⁻¹ ∈ w.toValuationSubring :=
    w.mem_of_ord_nonneg (inv_ne_zero hJ0) (by rw [w.ord_inv]; omega)

  have hsurj := surjective_algebraMap_residueField_of_deg_eq_one w (deg_eq_one_modularFunctionFieldBar N w)
  obtain ⟨u, hu, -⟩ := w.exists_hasValue_of_surjective hsurj hJ'

  have huA : ∃ hu' : u ∈ A, (⟨u, hu'⟩ : A) ∈ nonunits A := by
    by_cases hu0 : u = 0
    · subst hu0
      refine ⟨A.zero_mem, ?_⟩
      have e : (⟨(0 : AlgebraicClosure ℚ), A.zero_mem⟩ : A) = 0 := rfl
      rw [e]
      exact not_isUnit_zero
    ·
      have hunit : IsUnit (⟨(jBar N)⁻¹, hJ'⟩ : w.toValuationSubring) := by
        rw [← residue_ne_zero_iff_isUnit, hu.residue_eq]
        exact (_root_.map_ne_zero _).mpr hu0
      have hordJ' : w.ord (jBar N)⁻¹ = 0 := by
        obtain ⟨v, hv⟩ := hunit
        have h := w.ord_coe_unit v
        rwa [hv] at h
      have hJmem : jBar N ∈ w.toValuationSubring :=
        w.mem_of_ord_nonneg hJ0 (by rw [w.ord_inv] at hordJ'; omega)
      have hval : w.HasValue (jBar N) u⁻¹ := by
        refine ⟨hJmem, ?_⟩
        have hprod : (⟨jBar N, hJmem⟩ : w.toValuationSubring) * ⟨(jBar N)⁻¹, hJ'⟩ = 1 :=
          Subtype.ext (mul_inv_cancel₀ hJ0)
        have h1 := congrArg (residue w.toValuationSubring) hprod
        rw [map_mul, map_one, hu.residue_eq] at h1
        rw [map_inv₀]
        exact eq_inv_of_mul_eq_one_left h1
      have hpos : 0 < w.ord (jBar N - algebraMap _ _ u⁻¹) :=
        ord_sub_pos_of_hasValue w hval (jBar_ne_algebraMap _)
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

  have hqA : ((q : ℕ) : A) ∈ nonunits A := by
    intro hunitq
    have h := congrArg red (IsUnit.mul_val_inv hunitq)
    rw [map_mul, map_one, map_natCast, CharP.cast_eq_zero k q, zero_mul] at h
    exact zero_ne_one h

  obtain ⟨b, hbroot, hb1, hbder⟩ := exists_root_normPoly (data := data) hq hsym hKr hqA uA hunon

  have hredb : red b = 1 := by
    have h := red_eq_zero_of_mem_nonunits (q := q) hq red (b - 1) hb1
    rwa [map_sub, map_one, sub_eq_zero] at h

  obtain ⟨Q, hQdef⟩ : ∃ Q : Polynomial w.toValuationSubring,
      Q = normPoly data w.toValuationSubring ⟨(jBar N)⁻¹, hJ'⟩ := ⟨_, rfl⟩
  have hQm : Q.Monic := by
    rw [hQdef]; exact (monic_normPoly (data := data) hq _).1
  obtain ⟨bO, hbOdef⟩ : ∃ bO : w.toValuationSubring,
      bO = algebraMap (AlgebraicClosure ℚ) w.toValuationSubring (b : AlgebraicClosure ℚ) := ⟨_, rfl⟩
  haveI : CharZero (modularFunctionFieldBar N) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).injective
  haveI : CharZero (modularFunctionFieldBar (N * q)) :=
    charZero_of_injective_algebraMap
      (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).injective
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  have hfin : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q) :=
    finiteAlong_heckeBetaBar_of_prime (AlgebraicClosure ℚ) N q
  haveI : Module.Finite (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) := by
    have h := hfin
    unfold FiniteAlong at h
    exact h

  have hx : (Q.map (algebraMap w.toValuationSubring (modularFunctionFieldBar N))).eval₂
      (heckeBetaBar (AlgebraicClosure ℚ) N q).toRingHom (tZero N q) = 0 := by
    rw [hQdef]
    exact normPoly_eval₂_tZero (data := data) hsym w hJ'

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

  have hL4 := minpoly_tZero (data := data) hqN w hJ'
  rw [← hQdef] at hL4
  obtain ⟨hQmin, hdeg, hfr⟩ := hL4
  have hroot_ne : ((Q.eval bO : w.toValuationSubring) : modularFunctionFieldBar N) ≠ 0 := by
    intro h0
    have hint : IsIntegral (modularFunctionFieldBar N) (tZero N q) := Algebra.IsIntegral.isIntegral _
    have hr : (minpoly (modularFunctionFieldBar N) (tZero N q)).IsRoot (bO : modularFunctionFieldBar N) := by
      rw [← hQmin, Polynomial.IsRoot, Polynomial.eval_map]
      change Polynomial.eval₂ _ (algebraMap w.toValuationSubring (modularFunctionFieldBar N) bO) Q = 0
      rw [Polynomial.eval₂_at_apply]
      exact h0
    have h1 := Polynomial.degree_eq_one_of_irreducible_of_root (minpoly.irreducible hint) hr
    have h2 : (minpoly (modularFunctionFieldBar N) (tZero N q)).natDegree = 1 :=
      Polynomial.natDegree_eq_of_degree_eq_some h1
    rw [hdeg, hfr] at h2
    have := hq.two_le
    omega
  have hroot : 0 < w.ord ((Q.eval bO : w.toValuationSubring) : modularFunctionFieldBar N) :=
    ord_pos_of_not_isUnit w (fun hu' => (mem_maximalIdeal _).mp hroot_mem hu') hroot_ne

  have hnorm : w.ord (Algebra.norm (modularFunctionFieldBar N)
        (tZero N q - heckeBetaBar (AlgebraicClosure ℚ) N q (bO : modularFunctionFieldBar N)))
        = w.ord ((Q.eval bO : w.toValuationSubring) : modularFunctionFieldBar N) := by
    rw [← algebraMap_algBeta]
    exact Place.ord_norm_sub_eq_ord_eval w Q hQmin hdeg bO

  obtain ⟨c, hc, hcval, -, -, -⟩ :=
    exists_place_over_of_simple_root_along (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ hfin w hQm hx bO
      hroot hsimple hnorm
  refine ⟨c, hc, b, hredb, hasValue_of_ord_sub_pos c ?_⟩
  have hb : heckeBetaBar (AlgebraicClosure ℚ) N q (bO : modularFunctionFieldBar N)
      = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (b : AlgebraicClosure ℚ) := by
    rw [hbOdef, Place.coe_algebraMap, AlgHom.commutes]
  rw [← hb]
  exact hcval

end Beta

end CuspNormalization

theorem solution
    (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N]
    (k : Type) [Field k] [CharP k q] (red : A →+* k)
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q) (hqN : ¬ q ∣ N)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hw : ∀ a : A, w.ord
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0) :
    ∃ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      c.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ = w ∧
      ∃ τ : A, red τ = 1 ∧ c.HasValue (tZero N q) (τ : AlgebraicClosure ℚ) :=
  CuspNormalization.cusp_zero (data := data) (hKr := hKr) hqN w hw

end

end S_ModularCurve_exists_place_restrictAlong_heckeBetaBar_eq_and_hasValue_tZero
end P2MW
export P2MW.S_ModularCurve_exists_place_restrictAlong_heckeBetaBar_eq_and_hasValue_tZero (solution)
