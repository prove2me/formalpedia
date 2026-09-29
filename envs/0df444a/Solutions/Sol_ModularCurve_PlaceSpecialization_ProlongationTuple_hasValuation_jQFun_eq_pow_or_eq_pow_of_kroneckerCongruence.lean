-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.hasValuation_jQFun_eq_pow_or_eq_pow_of_kroneckerCongruence
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/e2565fc2-906b-5b9c-9063-cf7e2ff71fe1

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_PlaceDepth
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Theorems.Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_le
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_prime
import Theorems.Thm_ModularCurve_swapBivar_eq_of_evalSymm
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValuation_jQFun_eq_pow_or_eq_pow_of_kroneckerCongruence
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace A1SolDev

open ModularCurve.PlaceSpecialization.ProlongationTuple

private theorem evalModularPair_value_eq_zero {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]
    (data : ModularPolynomialData q) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    {J J' : AlgebraicClosure ℚ} (hJ : W.HasValue (jFun N q) J) (hJ' : W.HasValue (jQFun N q) J') :
    evalModularPair J J' data.Φ = 0 := by

  have hhom : Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) jq = evalAtJ :=
    Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)
  have h0 : evalModularPair jq (jqN q) data.Φ = 0 := by
    show data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) jq) (jqN q) = 0
    rw [hhom]
    exact data.eval_eq_zero

  have h1 : evalModularPair (jFun N q) (jQFun N q) data.Φ = 0 := by
    apply (algebraMap (modularFunctionFieldBar (N * q)) (LaurentSeries (AlgebraicClosure ℚ))).injective
    rw [map_evalModularPair, map_zero]
    have h := congrArg (coeffEmb (AlgebraicClosure ℚ)) h0
    rw [map_evalModularPair, map_zero] at h
    exact h

  have h2 : evalModularPair (⟨jFun N q, hJ.mem⟩ : W.toValuationSubring) ⟨jQFun N q, hJ'.mem⟩ data.Φ = 0 := by
    apply Subtype.val_injective
    exact (map_evalModularPair W.toValuationSubring.subtype _ _ _).trans h1

  apply W.algebraMap_residueField_injective
  rw [map_evalModularPair, map_zero, ← hJ.residue_eq, ← hJ'.residue_eq, ← map_evalModularPair, h2, map_zero]

private theorem natDegree_Φ {q : ℕ} [hq : Fact q.Prime] (data : ModularPolynomialData q) :
    data.Φ.natDegree = q + 1 := by
  rw [data.natDegree_eq, dedekindPsi_prime hq.out]

private theorem coeff_top {q : ℕ} [hq : Fact q.Prime] (data : ModularPolynomialData q) :
    data.Φ.coeff (q + 1) = 1 := by
  have h := data.monic.coeff_natDegree
  rwa [natDegree_Φ data] at h

private theorem swapInner_coeff (c : Polynomial ℤ) (i : ℕ) :
    (swapInner c).coeff i = Polynomial.C (c.coeff i) := by
  induction c using Polynomial.induction_on' with
  | add p r hp hr => simp only [map_add, Polynomial.coeff_add, hp, hr]
  | monomial m a =>
    simp only [swapInner, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_monomial,
      Polynomial.coeff_monomial, Polynomial.algebraMap_apply, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    split_ifs <;> simp_all

private theorem swapBivar_coeff_coeff (Φ : Polynomial (Polynomial ℤ)) (i j : ℕ) :
    ((swapBivar Φ).coeff i).coeff j = (Φ.coeff j).coeff i := by
  induction Φ using Polynomial.induction_on' with
  | add p r hp hr => simp only [map_add, Polynomial.coeff_add, hp, hr]
  | monomial n c =>
    simp only [swapBivar, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, Polynomial.coeff_monomial]
    rw [← Polynomial.C_pow, Polynomial.coeff_mul_C, swapInner_coeff, Polynomial.coeff_C_mul_X_pow]
    split_ifs <;> simp_all

private theorem natDegree_coeff_le_of_pos {q : ℕ} [hq : Fact q.Prime] (data : ModularPolynomialData q) {i : ℕ}
    (hi : 0 < i) : (data.Φ.coeff i).natDegree ≤ q := by
  have hsymm : swapBivar data.Φ = data.Φ := swapBivar_eq_of_evalSymm (data.evalSymm_of_prime q)
  have htop : (data.Φ.coeff i).coeff (q + 1) = 0 := by
    have h := swapBivar_coeff_coeff data.Φ (q + 1) i
    rw [hsymm, coeff_top data, Polynomial.coeff_one, if_neg (by omega)] at h
    exact h.symm
  have hle : (data.Φ.coeff i).natDegree ≤ q + 1 := data.natDegree_coeff_le q i
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rcases Nat.lt_or_ge (q + 1) n with h | h
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hle h)
  · have : n = q + 1 := by omega
    rw [this]
    exact htop

private noncomputable def principal (q : ℕ) : Polynomial (Polynomial ℤ) :=
  (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q)

private theorem principal_eq (q : ℕ) :
    principal q = Polynomial.C (Polynomial.X ^ (q + 1)) - Polynomial.C (Polynomial.X ^ q) * Polynomial.X ^ q -
      Polynomial.C Polynomial.X * Polynomial.X + Polynomial.X ^ (q + 1) := by
  unfold principal
  simp only [Polynomial.C_pow]
  ring

private theorem principal_coeff (q : ℕ) (i : ℕ) :
    (principal q).coeff i =
      (if i = 0 then Polynomial.X ^ (q + 1) else 0) - (if i = q then Polynomial.X ^ q else 0) -
        (if i = 1 then Polynomial.X else 0) + (if i = q + 1 then 1 else 0) := by
  rw [principal_eq, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_C,
    Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_X_pow]

private theorem reduceModBivar_principal (q : ℕ) :
    reduceModBivar q (principal q) =
      (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) := by
  unfold principal
  simp only [map_mul, map_sub, map_pow, reduceModBivar_X, reduceModBivar_C_X]

private theorem dvd_coeff_sub_principal {q : ℕ} [hq : Fact q.Prime] (data : ModularPolynomialData q)
    (hKr : KroneckerCongruence q data) (i k : ℕ) :
    (q : ℤ) ∣ ((data.Φ - principal q).coeff i).coeff k := by
  have h : reduceModBivar q (data.Φ - principal q) = 0 := by
    rw [map_sub, reduceModBivar_principal, sub_eq_zero]
    exact hKr
  have h1 := congrArg (fun P => Polynomial.coeff (Polynomial.coeff P i) k) h
  simp only [reduceModBivar, Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_zero,
    eq_intCast] at h1
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp h1

private theorem valuation_eval₂_le_of_dvd (A : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) (p : Polynomial ℤ)
    {d : ℕ} (hp : ∀ k, (q : ℤ) ∣ p.coeff k) (hd : p.natDegree ≤ d) {J : AlgebraicClosure ℚ}
    (hJ : 1 ≤ A.valuation J) :
    A.valuation (p.eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) J) ≤
      A.valuation (q : AlgebraicClosure ℚ) * A.valuation J ^ d := by
  rw [Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hd)]
  refine Valuation.map_sum_le _ fun k hk => ?_
  obtain ⟨m, hm⟩ := hp k
  have hm1 : A.valuation (m : AlgebraicClosure ℚ) ≤ 1 := A.valuation_le_one ⟨(m : AlgebraicClosure ℚ), by simp⟩
  have hk' : k ≤ d := by simpa [Nat.lt_succ_iff] using hk
  simp only [hm, map_mul, map_pow, eq_intCast, Int.cast_natCast]
  refine le_trans (mul_le_mul' (mul_le_mul' le_rfl hm1) (pow_le_pow_right₀ hJ hk')) ?_
  rw [mul_one]

private theorem coeff_eval_eq {q : ℕ} [hq : Fact q.Prime] (data : ModularPolynomialData q) (i : ℕ)
    (J : AlgebraicClosure ℚ) :
    (data.Φ.coeff i).eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) J =
      ((principal q).coeff i).eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) J +
        ((data.Φ - principal q).coeff i).eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) J := by
  rw [← Polynomial.eval₂_add, Polynomial.coeff_sub, add_sub_cancel]

private theorem natDegree_remainder_le {q : ℕ} [hq : Fact q.Prime] (data : ModularPolynomialData q) (i : ℕ) :
    ((data.Φ - principal q).coeff i).natDegree ≤ q + 1 ∧
      (0 < i → ((data.Φ - principal q).coeff i).natDegree ≤ q) := by
  have hprin : ((principal q).coeff i).natDegree ≤ q + 1 ∧ (0 < i → ((principal q).coeff i).natDegree ≤ q) := by
    rw [principal_coeff]
    constructor
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ((Polynomial.natDegree_sub_le _ _).trans (max_le
        ((Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)) ?_)) ?_) <;> (try split_ifs) <;> simp
    · intro hi
      rw [if_neg hi.ne']
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ((Polynomial.natDegree_sub_le _ _).trans (max_le
        ((Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)) ?_)) ?_) <;> (try split_ifs) <;> simp
      exact hq.out.one_lt.le
  rw [Polynomial.coeff_sub]
  constructor
  · exact (Polynomial.natDegree_sub_le _ _).trans (max_le (data.natDegree_coeff_le q i) hprin.1)
  · intro hi
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le (natDegree_coeff_le_of_pos data hi) (hprin.2 hi))

private theorem coeff_sizes {q : ℕ} [hq : Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hqA : A.valuation (q : AlgebraicClosure ℚ) < 1) (data : ModularPolynomialData q)
    (hKr : KroneckerCongruence q data) {J : AlgebraicClosure ℚ} {γ : A.ValueGroup} (hJ : A.valuation J = γ)
    (hγ : 1 < γ) :
    A.valuation ((data.Φ.coeff 0).eval₂ (Int.castRingHom _) J) = γ ^ (q + 1) ∧
    A.valuation ((data.Φ.coeff q).eval₂ (Int.castRingHom _) J) = γ ^ q ∧
    (∀ i, 1 ≤ i → i ≤ q - 1 → A.valuation ((data.Φ.coeff i).eval₂ (Int.castRingHom _) J) < γ ^ q) ∧
    data.Φ.coeff (q + 1) = 1 := by
  have hγ0 : γ ≠ 0 := (zero_lt_one.trans hγ).ne'
  have hJ1 : 1 ≤ A.valuation J := by rw [hJ]; exact hγ.le
  have hsmall : ∀ d : ℕ, A.valuation (q : AlgebraicClosure ℚ) * γ ^ d < γ ^ d := fun d => by
    have hpos : (0 : A.ValueGroup) < γ ^ d := zero_lt_iff.2 (pow_ne_zero _ hγ0)
    simpa only [one_mul] using mul_lt_mul_of_pos_right hqA hpos
  have hrem : ∀ i, A.valuation (((data.Φ - principal q).coeff i).eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) J) ≤
      A.valuation (q : AlgebraicClosure ℚ) * γ ^ (q + 1) := fun i => by
    rw [← hJ]
    exact valuation_eval₂_le_of_dvd A q _ (dvd_coeff_sub_principal data hKr i) (natDegree_remainder_le data i).1 hJ1
  have hrem' : ∀ i, 0 < i →
      A.valuation (((data.Φ - principal q).coeff i).eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) J) ≤
        A.valuation (q : AlgebraicClosure ℚ) * γ ^ q := fun i hi => by
    rw [← hJ]
    exact valuation_eval₂_le_of_dvd A q _ (dvd_coeff_sub_principal data hKr i) ((natDegree_remainder_le data i).2 hi)
      hJ1
  have hq0 : (0 : ℕ) ≠ q := hq.out.ne_zero.symm
  have hq1 : (1 : ℕ) ≠ q := hq.out.one_lt.ne
  refine ⟨?_, ?_, ?_, coeff_top data⟩
  ·
    have hp : ((principal q).coeff 0).eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) J = J ^ (q + 1) := by
      rw [principal_coeff]
      simp [hq0]
    rw [coeff_eval_eq, hp, Valuation.map_add_eq_of_lt_left _ ?_, Valuation.map_pow, hJ]
    rw [Valuation.map_pow, hJ]
    exact lt_of_le_of_lt (hrem 0) (hsmall _)
  ·
    have hp : ((principal q).coeff q).eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) J = -(J ^ q) := by
      rw [principal_coeff]
      simp [hq0.symm, hq1.symm]
    rw [coeff_eval_eq, hp, Valuation.map_add_eq_of_lt_left _ ?_, Valuation.map_neg, Valuation.map_pow, hJ]
    rw [Valuation.map_neg, Valuation.map_pow, hJ]
    exact lt_of_le_of_lt (hrem' q hq.out.pos) (hsmall _)
  ·
    intro i hi1 hiq
    have hiq' : i ≠ q := by omega
    have hiq1 : i ≠ q + 1 := by omega
    have hi0 : i ≠ 0 := by omega
    have hγq : γ < γ ^ q := by
      simpa only [pow_one] using pow_lt_pow_right₀ hγ hq.out.one_lt
    have hp : A.valuation (((principal q).coeff i).eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) J) < γ ^ q := by
      rw [principal_coeff, if_neg hi0, if_neg hiq', if_neg hiq1]
      by_cases hi : i = 1
      · rw [if_pos hi]
        simp only [zero_sub, sub_zero, add_zero, Polynomial.eval₂_neg, Polynomial.eval₂_X, Valuation.map_neg, hJ]
        exact hγq
      · rw [if_neg hi]
        simp only [sub_zero, add_zero, Polynomial.eval₂_zero, Valuation.map_zero]
        exact zero_lt_iff.2 (pow_ne_zero _ hγ0)
    rw [coeff_eval_eq]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hp (lt_of_le_of_lt (hrem' i (by omega)) (hsmall _)))

namespace NewtonSizes

open Polynomial

section generic

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

private theorem not_dominant {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → K}
    (hsum : ∑ i ∈ s, f i = 0) {j : ι} (hj : j ∈ s) (hne : v (f j) ≠ 0)
    (hlt : ∀ i ∈ s, i ≠ j → v (f i) < v (f j)) : False := by
  have h := v.map_sum_eq_of_lt hj (fun i hi => by
    have hi' := Finset.mem_sdiff.1 hi
    exact hlt i hi'.1 (by simpa using hi'.2))
  rw [hsum, v.map_zero] at h
  exact hne h.symm

private theorem no_dominant_term {P : K[X]} {n : ℕ} (hdeg : P.natDegree < n) {y : K} (hy : P.IsRoot y)
    {j : ℕ} (hj : j < n) (hne : v (P.coeff j * y ^ j) ≠ 0)
    (hlt : ∀ i, i < n → i ≠ j → v (P.coeff i * y ^ i) < v (P.coeff j * y ^ j)) : False := by
  have hsum : ∑ i ∈ Finset.range n, P.coeff i * y ^ i = 0 := by
    rw [← eval_eq_sum_range' hdeg y]
    exact hy.eq_zero
  exact not_dominant v hsum (Finset.mem_range.2 hj) hne (fun i hi hij => hlt i (Finset.mem_range.1 hi) hij)

private theorem pos_of_ne_zero {a : Γ₀} (ha : a ≠ 0) : 0 < a := lt_of_le_of_ne zero_le' ha.symm

private theorem le_one_of_root {P : K[X]} {n : ℕ} (hdeg : P.natDegree ≤ n) (htop : P.coeff n = 1)
    (hcoeff : ∀ i, i < n → v (P.coeff i) ≤ 1) {y : K} (hy : P.IsRoot y) : v y ≤ 1 := by
  by_contra hle
  have hlt : 1 < v y := not_le.1 hle
  have hy0 : v y ≠ 0 := (zero_lt_one.trans hlt).ne'
  refine no_dominant_term v (Nat.lt_succ_of_le hdeg) hy (Nat.lt_succ_self n) ?_ ?_
  · rw [htop, one_mul, v.map_pow]
    exact pow_ne_zero _ hy0
  · intro i hi hij
    have hi' : i < n := lt_of_le_of_ne (Nat.lt_succ_iff.1 hi) hij
    rw [htop, one_mul, v.map_mul, v.map_pow, v.map_pow]
    calc v (P.coeff i) * v y ^ i ≤ 1 * v y ^ i :=
          mul_le_mul_of_nonneg_right (hcoeff i hi') zero_le'
      _ = v y ^ i := one_mul _
      _ < v y ^ n := pow_lt_pow_right₀ hlt hi'

private theorem root_size_eq_or_pow_eq {q : ℕ} (hq : 1 < q) {γ : Γ₀} (hγ : 1 < γ) {P : K[X]}
    (hdeg : P.natDegree ≤ q + 1) (htop : P.coeff (q + 1) = 1) (hcq : v (P.coeff q) = γ ^ q)
    (hc0 : v (P.coeff 0) = γ ^ (q + 1)) (hmid : ∀ i, 1 ≤ i → i ≤ q - 1 → v (P.coeff i) < γ ^ q)
    {y : K} (hy : P.IsRoot y) : v y = γ ^ q ∨ v y ^ q = γ := by
  have hγ0 : γ ≠ 0 := (zero_lt_one.trans hγ).ne'
  have hγq : 1 < γ ^ q := one_lt_pow₀ hγ (by omega)

  have hy0 : v y ≠ 0 := by
    intro h0
    rw [v.zero_iff] at h0
    subst h0
    have h := hy.eq_zero
    rw [← coeff_zero_eq_eval_zero] at h
    rw [h, v.map_zero] at hc0
    exact (pow_ne_zero _ hγ0) hc0.symm
  have hδq : v y ^ q ≠ 0 := pow_ne_zero _ hy0
  have hterm : ∀ i, v (P.coeff i * y ^ i) = v (P.coeff i) * v y ^ i := fun i => by
    rw [v.map_mul, v.map_pow]
  have htopterm : v (P.coeff (q + 1) * y ^ (q + 1)) = v y ^ q * v y := by
    rw [hterm, htop, v.map_one, one_mul, pow_succ]
  have hqterm : v (P.coeff q * y ^ q) = γ ^ q * v y ^ q := by rw [hterm, hcq]
  have h0term : v (P.coeff 0 * y ^ 0) = γ ^ q * γ := by rw [hterm, hc0, pow_zero, mul_one, pow_succ]

  have hmidterm : ∀ i, 1 ≤ i → i ≤ q - 1 → v (P.coeff i * y ^ i) < γ ^ q * v y ^ i := fun i h1 h2 => by
    rw [hterm]
    exact mul_lt_mul_of_pos_right (hmid i h1 h2) (pos_of_ne_zero (pow_ne_zero _ hy0))

  have hmid_big : 1 ≤ v y → ∀ i, 1 ≤ i → i ≤ q - 1 → v (P.coeff i * y ^ i) < γ ^ q * v y ^ q :=
    fun hδ1 i h1 h2 => (hmidterm i h1 h2).trans_le
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hδ1 (by omega)) zero_le')
  have hlt_deg : P.natDegree < q + 2 := by omega
  rcases lt_trichotomy (γ ^ q) (v y) with hA | hC | hB
  ·
    exfalso
    have hδ1 : 1 ≤ v y := (hγq.trans hA).le
    have hq_lt_top : v (P.coeff q * y ^ q) < v (P.coeff (q + 1) * y ^ (q + 1)) := by
      rw [hqterm, htopterm, mul_comm (γ ^ q)]
      exact mul_lt_mul_of_pos_left hA (pos_of_ne_zero hδq)
    refine no_dominant_term v hlt_deg hy (j := q + 1) (by omega) ?_ ?_
    · rw [htopterm]
      exact mul_ne_zero hδq hy0
    · intro i hi hij
      rcases Nat.lt_or_ge i 1 with hi0 | hi1
      ·
        have hi0' : i = 0 := by omega
        rw [hi0']
        refine lt_trans ?_ hq_lt_top
        rw [h0term, hqterm]
        refine mul_lt_mul_of_pos_left ?_ (pos_of_ne_zero (pow_ne_zero _ hγ0))
        calc γ < γ ^ q := by
                calc γ = γ ^ 1 := (pow_one γ).symm
                  _ < γ ^ q := pow_lt_pow_right₀ hγ hq
          _ < v y := hA
          _ ≤ v y ^ q := by
                calc v y = v y ^ 1 := (pow_one _).symm
                  _ ≤ v y ^ q := pow_le_pow_right₀ hδ1 (by omega)
      · rcases Nat.lt_or_ge i q with hiq | hiq
        ·
          refine lt_trans ?_ hq_lt_top
          rw [hqterm]
          exact hmid_big hδ1 i hi1 (by omega)
        ·
          have hiq' : i = q := by omega
          rw [hiq']
          exact hq_lt_top
  · exact Or.inl hC.symm
  ·
    rcases lt_trichotomy (v y ^ q) γ with hB2 | hB3 | hB1
    ·
      exfalso
      refine no_dominant_term v hlt_deg hy (j := 0) (by omega) ?_ ?_
      · rw [h0term]
        exact mul_ne_zero (pow_ne_zero _ hγ0) hγ0
      · have hq_lt_0 : v (P.coeff q * y ^ q) < v (P.coeff 0 * y ^ 0) := by
          rw [hqterm, h0term]
          exact mul_lt_mul_of_pos_left hB2 (pos_of_ne_zero (pow_ne_zero _ hγ0))
        intro i hi hij
        rcases Nat.lt_or_ge i q with hiq | hiq
        ·
          have hi1 : 1 ≤ i := by omega
          rcases le_or_gt 1 (v y) with hδ1 | hδ1
          · refine lt_trans ?_ hq_lt_0
            rw [hqterm]
            exact hmid_big hδ1 i hi1 (by omega)
          ·
            rw [h0term]
            calc v (P.coeff i * y ^ i) = v (P.coeff i) * v y ^ i := hterm i
              _ ≤ v (P.coeff i) * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ zero_le' hδ1.le) zero_le'
              _ = v (P.coeff i) := mul_one _
              _ < γ ^ q := hmid i hi1 (by omega)
              _ = γ ^ q * 1 := (mul_one _).symm
              _ < γ ^ q * γ := mul_lt_mul_of_pos_left hγ (pos_of_ne_zero (pow_ne_zero _ hγ0))
        · rcases Nat.lt_or_ge i (q + 1) with hiq1 | hiq1
          · have hiq' : i = q := by omega
            rw [hiq']
            exact hq_lt_0
          ·
            have hi' : i = q + 1 := by omega
            rw [hi', htopterm, h0term]
            calc v y ^ q * v y = v y * v y ^ q := mul_comm _ _
              _ < γ ^ q * v y ^ q := mul_lt_mul_of_pos_right hB (pos_of_ne_zero hδq)
              _ < γ ^ q * γ := mul_lt_mul_of_pos_left hB2 (pos_of_ne_zero (pow_ne_zero _ hγ0))
    · exact Or.inr hB3
    ·
      exfalso
      have hδ1 : 1 ≤ v y := by
        by_contra h
        exact (not_le.2 (hγ.trans hB1)) (pow_le_one₀ zero_le' (not_le.1 h).le)
      refine no_dominant_term v hlt_deg hy (j := q) (by omega) ?_ ?_
      · rw [hqterm]
        exact mul_ne_zero (pow_ne_zero _ hγ0) hδq
      · intro i hi hij
        rcases Nat.lt_or_ge i 1 with hi0 | hi1
        · have hi0' : i = 0 := by omega
          rw [hi0', h0term, hqterm]
          exact mul_lt_mul_of_pos_left hB1 (pos_of_ne_zero (pow_ne_zero _ hγ0))
        · rcases Nat.lt_or_ge i q with hiq | hiq
          · rw [hqterm]
            exact hmid_big hδ1 i hi1 (by omega)
          · have hi' : i = q + 1 := by omega
            rw [hi', htopterm, hqterm, mul_comm (v y ^ q) (v y)]
            exact mul_lt_mul_of_pos_right hB (pos_of_ne_zero hδq)

end generic
end NewtonSizes

section modular_glue
open Polynomial

private noncomputable def fibrePoly (Φ : Polynomial (Polynomial ℤ)) (J : AlgebraicClosure ℚ) :
    Polynomial (AlgebraicClosure ℚ) :=
  Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (AlgebraicClosure ℚ)) J)

private theorem fibrePoly_coeff (Φ : Polynomial (Polynomial ℤ)) (J : AlgebraicClosure ℚ) (i : ℕ) :
    (fibrePoly Φ J).coeff i = (Φ.coeff i).eval₂ (Int.castRingHom _) J := by
  simp [fibrePoly, coeff_map]

private theorem eval_fibrePoly (Φ : Polynomial (Polynomial ℤ)) (J y : AlgebraicClosure ℚ) :
    (fibrePoly Φ J).eval y = evalModularPair J y Φ := by
  unfold evalModularPair
  simp [fibrePoly, eval_map]

private theorem isRoot_fibrePoly {Φ : Polynomial (Polynomial ℤ)} {J y : AlgebraicClosure ℚ}
    (heq : evalModularPair J y Φ = 0) : (fibrePoly Φ J).IsRoot y := by
  rw [IsRoot, eval_fibrePoly]
  exact heq

private theorem fibrePoly_root_size {q : ℕ} [hq : Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (data : ModularPolynomialData q) {J : AlgebraicClosure ℚ} {γ : A.ValueGroup} (hγ : 1 < γ)
    (hψ : data.Φ.natDegree = q + 1)
    (hc : A.valuation ((data.Φ.coeff 0).eval₂ (Int.castRingHom _) J) = γ ^ (q + 1) ∧
      A.valuation ((data.Φ.coeff q).eval₂ (Int.castRingHom _) J) = γ ^ q ∧
      (∀ i, 1 ≤ i → i ≤ q - 1 → A.valuation ((data.Φ.coeff i).eval₂ (Int.castRingHom _) J) < γ ^ q) ∧
      data.Φ.coeff (q + 1) = 1) :
    ∀ y, (fibrePoly data.Φ J).IsRoot y → A.valuation y = γ ^ q ∨ A.valuation y ^ q = γ := by
  obtain ⟨hc0, hcq, hmid, htop⟩ := hc
  intro y hy
  refine NewtonSizes.root_size_eq_or_pow_eq A.valuation hq.out.one_lt hγ (P := fibrePoly data.Φ J)
    (natDegree_map_le.trans hψ.le) ?_ ?_ ?_ ?_ hy
  · rw [fibrePoly_coeff, htop, eval₂_one]
  · rw [fibrePoly_coeff, hcq]
  · rw [fibrePoly_coeff, hc0]
  · intro i h1 h2
    rw [fibrePoly_coeff]
    exact hmid i h1 h2

private theorem root_size_dichotomy {q : ℕ} [hq : Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (data : ModularPolynomialData q) {J J' : AlgebraicClosure ℚ} {γ γ' : A.ValueGroup}
    (hJ : A.valuation J = γ) (hJ' : A.valuation J' = γ') (hγ : 1 < γ) (hψ : data.Φ.natDegree = q + 1)
    (hc : A.valuation ((data.Φ.coeff 0).eval₂ (Int.castRingHom _) J) = γ ^ (q + 1) ∧
      A.valuation ((data.Φ.coeff q).eval₂ (Int.castRingHom _) J) = γ ^ q ∧
      (∀ i, 1 ≤ i → i ≤ q - 1 → A.valuation ((data.Φ.coeff i).eval₂ (Int.castRingHom _) J) < γ ^ q) ∧
      data.Φ.coeff (q + 1) = 1)
    (heq : evalModularPair J J' data.Φ = 0) : γ' = γ ^ q ∨ γ = γ' ^ q := by
  have _ := hJ
  have h := fibrePoly_root_size A data hγ hψ hc J' (isRoot_fibrePoly heq)
  rw [hJ'] at h
  exact h.imp id Eq.symm

private theorem one_lt_of_root {q : ℕ} [hq : Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (data : ModularPolynomialData q) {J J' : AlgebraicClosure ℚ} {γ γ' : A.ValueGroup}
    (hJ : A.valuation J = γ) (hJ' : A.valuation J' = γ') (hγ' : 1 < γ')
    (heq : evalModularPair J J' data.Φ = 0) : 1 < γ := by
  by_contra hγ
  have hγ1 : γ ≤ 1 := not_lt.1 hγ
  have hJA : J ∈ A := A.mem_of_valuation_le_one J (hJ ▸ hγ1)
  have hle : A.valuation J' ≤ 1 :=
    NewtonSizes.le_one_of_root A.valuation (P := fibrePoly data.Φ J) natDegree_map_le
      (by rw [fibrePoly_coeff, data.monic.coeff_natDegree, eval₂_one])
      (fun i _ => by
        rw [fibrePoly_coeff]
        have h1 := (data.Φ.coeff i).hom_eval₂ (Int.castRingHom A) A.subtype (⟨J, hJA⟩ : A)
        rw [RingHom.ext_int (A.subtype.comp (Int.castRingHom A)) (Int.castRingHom _)] at h1
        simp only [ValuationSubring.subtype_apply] at h1
        rw [← h1]
        exact A.valuation_le_one _)
      (isRoot_fibrePoly heq)
  rw [hJ'] at hle
  exact absurd hle (not_le.2 hγ')

end modular_glue

end A1SolDev

open A1SolDev in
open ModularCurve.PlaceSpecialization.ProlongationTuple in

theorem solution
    {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hqA : A.valuation (q : AlgebraicClosure ℚ) < 1)
    {N : ℕ} [NeZero N] {data : ModularPolynomialData q} (hKr : KroneckerCongruence q data)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    {γ γ' : A.ValueGroup} (hγ' : 1 < γ')
    (hj : W.HasValuation A (jFun N q) γ) (hjq : W.HasValuation A (jQFun N q) γ') :
    γ' = γ ^ q ∨ γ = γ' ^ q := by
  obtain ⟨J, hJv, hJγ⟩ := hj
  obtain ⟨J', hJ'v, hJ'γ⟩ := hjq
  have heq := evalModularPair_value_eq_zero data W hJv hJ'v
  have hγ : 1 < γ := one_lt_of_root A data hJγ hJ'γ hγ' heq
  exact root_size_dichotomy A data hJγ hJ'γ hγ (natDegree_Φ data) (coeff_sizes A hqA data hKr hJγ hγ) heq

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValuation_jQFun_eq_pow_or_eq_pow_of_kroneckerCongruence
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValuation_jQFun_eq_pow_or_eq_pow_of_kroneckerCongruence (solution)
