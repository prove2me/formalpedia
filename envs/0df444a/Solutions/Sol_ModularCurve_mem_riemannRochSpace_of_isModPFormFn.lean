-- Prove2me | solution 1 for ModularCurve.mem_riemannRochSpace_of_isModPFormFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/d9df4822-8189-569b-80bf-3836fea3a3ca

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_ModPFormFn
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_riemannRochSpace_of_isModPFormFn

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace DictC1

section Ord

variable {K : Type*} {FF : Type*} [Field K] [Field FF] [Algebra K FF] (w : Place K FF)

theorem mem_iff_le_one {f : FF} : f ∈ w.toValuationSubring ↔ w.adicValuation f ≤ 1 :=
  Place.mem_iff_adicValuation_le_one w

theorem ord_nonneg_iff {f : FF} (hf : f ≠ 0) : 0 ≤ w.ord f ↔ w.adicValuation f ≤ 1 := by
  rw [Place.ord, neg_nonneg, WithZero.log_le_iff_le_exp (w.adicValuation_ne_zero hf), WithZero.exp_zero]

theorem ord_pos_iff {f : FF} (hf : f ≠ 0) : 0 < w.ord f ↔ w.adicValuation f < 1 := by
  rw [Place.ord, neg_pos, ← WithZero.log_one,
    WithZero.log_lt_log (w.adicValuation_ne_zero hf) one_ne_zero]

theorem ord_neg_iff {f : FF} (hf : f ≠ 0) : w.ord f < 0 ↔ 1 < w.adicValuation f := by
  rw [Place.ord, neg_lt_zero, ← WithZero.log_one,
    WithZero.log_lt_log one_ne_zero (w.adicValuation_ne_zero hf)]

theorem ord_nonneg_of_mem {f : FF} (h : f ∈ w.toValuationSubring) : 0 ≤ w.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [Place.ord_zero]
  · exact (ord_nonneg_iff w hf).2 ((mem_iff_le_one w).1 h)

theorem mem_of_ord_nonneg {f : FF} (h : 0 ≤ w.ord f) : f ∈ w.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact zero_mem _
  · exact (mem_iff_le_one w).2 ((ord_nonneg_iff w hf).1 h)

theorem ord_pow (f : FF) (n : ℕ) : w.ord (f ^ n) = n * w.ord f := by
  rw [← zpow_natCast, Place.ord_zpow]

theorem adicValuation_algebraMap {c : K} (hc : c ≠ 0) : w.adicValuation (algebraMap K FF c) = 1 := by
  apply le_antisymm (w.adicValuation_algebraMap_le_one c)
  have h1 : w.adicValuation (algebraMap K FF c) * w.adicValuation (algebraMap K FF c⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one]
  have h2 := w.adicValuation_algebraMap_le_one c⁻¹
  by_contra h
  rw [not_le] at h
  have : w.adicValuation (algebraMap K FF c) * w.adicValuation (algebraMap K FF c⁻¹) < 1 * 1 :=
    mul_lt_mul_of_lt_of_le_of_nonneg_of_pos h h2 zero_le' zero_lt_one
  rw [h1, one_mul] at this
  exact lt_irrefl _ this

theorem ord_algebraMap {c : K} (hc : c ≠ 0) : w.ord (algebraMap K FF c) = 0 := by
  rw [Place.ord, adicValuation_algebraMap w hc, WithZero.log_one, neg_zero]

theorem ord_sub_algebraMap_eq_zero_of_ord_pos {t : FF} (ht : t ≠ 0) {c : K} (hc : c ≠ 0) (h : 0 < w.ord t) :
    w.ord (t - algebraMap K FF c) = 0 := by
  have hv : w.adicValuation t < w.adicValuation (algebraMap K FF c) := by
    rw [adicValuation_algebraMap w hc]; exact (ord_pos_iff w ht).1 h
  rw [Place.ord, Valuation.map_sub_swap, Valuation.map_sub_eq_of_lt_left _ hv, adicValuation_algebraMap w hc,
    WithZero.log_one, neg_zero]

theorem ord_sub_algebraMap_eq_of_ord_neg {t : FF} (ht : t ≠ 0) (c : K) (h : w.ord t < 0) :
    w.ord (t - algebraMap K FF c) = w.ord t := by
  have hv : w.adicValuation (algebraMap K FF c) < w.adicValuation t :=
    lt_of_le_of_lt (w.adicValuation_algebraMap_le_one c) ((ord_neg_iff w ht).1 h)
  rw [Place.ord, Place.ord, Valuation.map_sub_eq_of_lt_left _ hv]

theorem ord_eq_zero_of_ord_sub_algebraMap_pos {t : FF} {c : K} (hc : c ≠ 0) (htc : t - algebraMap K FF c ≠ 0)
    (h : 0 < w.ord (t - algebraMap K FF c)) : w.ord t = 0 := by
  have hv : w.adicValuation (t - algebraMap K FF c) < w.adicValuation (algebraMap K FF c) := by
    rw [adicValuation_algebraMap w hc]; exact (ord_pos_iff w htc).1 h
  have : t = (t - algebraMap K FF c) + algebraMap K FF c := by ring
  rw [Place.ord, this, Valuation.map_add_eq_of_lt_right _ hv, adicValuation_algebraMap w hc, WithZero.log_one, neg_zero]

end Ord

theorem mem_of_isIntegral_adjoin {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L] {E : IntermediateField K L}
    (w : Place K ↥E) {t : ↥E} (ht : t ∈ w.toValuationSubring) (y : ↥E)
    (hy : IsIntegral (Algebra.adjoin K ({(t : L)} : Set L)) (y : L)) :
    y ∈ w.toValuationSubring := by
  classical
  set A := Algebra.adjoin K ({(t : L)} : Set L) with hA
  obtain ⟨P, hPm, hP0⟩ := hy

  have hcoef : ∀ i, ∃ c : Polynomial K, Polynomial.aeval (t : L) c = (P.coeff i : L) := by
    intro i
    have hm : (P.coeff i : L) ∈ (Polynomial.aeval (R := K) (t : L)).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (P.coeff i).2
    exact (AlgHom.mem_range _).1 hm
  choose c hc using hcoef

  let O : Subalgebra K ↥E :=
    { carrier := w.toValuationSubring
      mul_mem' := fun ha hb => w.toValuationSubring.mul_mem _ _ ha hb
      add_mem' := fun ha hb => w.toValuationSubring.add_mem _ _ ha hb
      algebraMap_mem' := fun a => w.algebraMap_mem' a }
  have hbO : ∀ i, Polynomial.aeval t (c i) ∈ w.toValuationSubring := fun i => by
    have h1 : Polynomial.aeval t (c i) = O.val (Polynomial.aeval (⟨t, ht⟩ : O) (c i)) :=
      Polynomial.aeval_algHom_apply O.val (⟨t, ht⟩ : O) (c i)
    rw [h1]
    exact (Polynomial.aeval (⟨t, ht⟩ : O) (c i)).2

  set n := P.natDegree with hn
  have hrelLS : (y : L) ^ n +
      ∑ i ∈ Finset.range n, (P.coeff i : L) * (y : L) ^ i = 0 := by
    have h := hP0
    rw [hPm.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at h
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at h
    exact h
  have hrel : y ^ n + ∑ i ∈ Finset.range n, Polynomial.aeval t (c i) * y ^ i = 0 := by
    apply Subtype.val_injective
    push_cast
    rw [← hrelLS]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hc i]
    congr 1
    exact (Polynomial.aeval_algHom_apply E.val t (c i)).symm

  let Q : Polynomial ↥(w.toValuationSubring) :=
    Polynomial.X ^ n + ∑ i ∈ Finset.range n,
      Polynomial.C (⟨Polynomial.aeval t (c i), hbO i⟩ : ↥(w.toValuationSubring)) * Polynomial.X ^ i
  have hQm : Q.Monic := by
    apply Polynomial.monic_X_pow_add
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).2 fun i hi => ?_
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le i _) ?_
    exact WithBot.coe_lt_coe.2 (Finset.mem_range.1 hi)
  have hQ0 : Polynomial.eval₂ (algebraMap ↥(w.toValuationSubring) ↥E) y Q = 0 := by
    simp only [Q, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
      Polynomial.eval₂_C]
    exact hrel
  have hint : IsIntegral ↥(w.toValuationSubring) y := ⟨Q, hQm, hQ0⟩
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥(w.toValuationSubring)) (K := ↥E)).1 hint
  rw [← hz]
  exact z.2

end DictC1

set_option maxHeartbeats 3200000 in
open DictC1 in
theorem solution
    (K : Type) [Field K] (h1728 : (1728 : K) ≠ 0) (N : ℕ) [NeZero N] (m : ℕ)
    (D : Divisor K ↥(modularFunctionFieldFullC K N))
    (hD : ∀ w : Place K ↥(modularFunctionFieldFullC K N),
      D w = (if 0 < w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N))
               then (2 * (m : ℤ) * w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N))) / 3 else 0)
          + (if 0 < w.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) - algebraMap K _ 1728)
               then ((m : ℤ) * w.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) - algebraMap K _ 1728)) / 2 else 0)
          + (if w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) < 0
               then (m : ℤ) * w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) else 0))
    (G : ↥(modularFunctionFieldFullC K N)) (hG : IsModPFormFn K m (G : LaurentSeries K)) :
    G ∈ riemannRochSpace D := by
  classical
  set j : ↥(modularFunctionFieldFullC K N) := ⟨jqModC K, jqModC_mem_full K N⟩ with hjdef
  have hjcoe : (j : LaurentSeries K) = jqModC K := rfl

  have hj0 : j ≠ 0 := by
    intro h
    have : (j : LaurentSeries K) = 0 := by rw [h]; rfl
    rw [hjcoe] at this
    exact (transcendental_jqModC K) (this ▸ isAlgebraic_zero)
  have hc0 : algebraMap K ↥(modularFunctionFieldFullC K N) 1728 ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap K _).injective]; exact h1728
  have hjc : j - algebraMap K ↥(modularFunctionFieldFullC K N) 1728 ≠ 0 := by
    intro h
    have h' : (j : LaurentSeries K) = algebraMap K (LaurentSeries K) 1728 := by
      rw [sub_eq_zero] at h; rw [h]; rfl
    rw [hjcoe] at h'
    exact (transcendental_jqModC K) (h' ▸ isAlgebraic_algebraMap (1728 : K))
  rw [mem_riemannRochSpace_iff]
  intro w
  rcases eq_or_ne G 0 with hG0 | hG0
  · exact Or.inl hG0
  right
  rw [hD w]

  obtain ⟨hint1, hint2⟩ := hG
  have hcoe1 : ((G ^ 6 * j ^ (4 * m) * (j - algebraMap K _ 1728) ^ (3 * m) : ↥(modularFunctionFieldFullC K N)) :
      LaurentSeries K) = (G : LaurentSeries K) ^ 6 * jqModC K ^ (4 * m) *
        (jqModC K - algebraMap K (LaurentSeries K) 1728) ^ (3 * m) := by
    push_cast; rfl
  have hcoe2 : ((G ^ 2 * j ^ m * (j - algebraMap K _ 1728) ^ m : ↥(modularFunctionFieldFullC K N)) :
      LaurentSeries K) = (G : LaurentSeries K) ^ 2 * jqModC K ^ m *
        (jqModC K - algebraMap K (LaurentSeries K) 1728) ^ m := by
    push_cast; rfl
  rw [← hcoe1] at hint1
  rw [← hcoe2] at hint2

  have hord1 : w.ord (G ^ 6 * j ^ (4 * m) * (j - algebraMap K _ 1728) ^ (3 * m)) =
      6 * w.ord G + (4 * m : ℕ) * w.ord j + (3 * m : ℕ) * w.ord (j - algebraMap K _ 1728) := by
    rw [w.ord_mul (mul_ne_zero (pow_ne_zero _ hG0) (pow_ne_zero _ hj0)) (pow_ne_zero _ hjc),
      w.ord_mul (pow_ne_zero _ hG0) (pow_ne_zero _ hj0), ord_pow, ord_pow, ord_pow]
    push_cast; ring
  have hord2 : w.ord (G ^ 2 * j ^ m * (j - algebraMap K _ 1728) ^ m) =
      2 * w.ord G + (m : ℤ) * w.ord j + (m : ℤ) * w.ord (j - algebraMap K _ 1728) := by
    rw [w.ord_mul (mul_ne_zero (pow_ne_zero _ hG0) (pow_ne_zero _ hj0)) (pow_ne_zero _ hjc),
      w.ord_mul (pow_ne_zero _ hG0) (pow_ne_zero _ hj0), ord_pow, ord_pow, ord_pow]
    push_cast; ring

  rcases lt_trichotomy (w.ord j) 0 with hneg | hzero | hpos
  ·
    have hinv : j⁻¹ ∈ w.toValuationSubring := mem_of_ord_nonneg w (by rw [Place.ord_inv]; omega)
    have hjinvcoe : ((j⁻¹ : ↥(modularFunctionFieldFullC K N)) : LaurentSeries K) = (jqModC K)⁻¹ := by push_cast; rfl
    rw [← hjinvcoe] at hint2
    have hmem := mem_of_isIntegral_adjoin w hinv _ hint2
    have h0 := ord_nonneg_of_mem w hmem
    rw [hord2, ord_sub_algebraMap_eq_of_ord_neg w hj0 1728 hneg] at h0
    have hsub : ¬ 0 < w.ord (j - algebraMap K _ 1728) := by
      rw [ord_sub_algebraMap_eq_of_ord_neg w hj0 1728 hneg]; omega
    rw [if_neg (show ¬ 0 < w.ord j from by omega), if_neg hsub, if_pos hneg]
    simp only [zero_add]
    linarith
  ·
    have hjm : j ∈ w.toValuationSubring := mem_of_ord_nonneg w hzero.ge
    have hmem := mem_of_isIntegral_adjoin w hjm _ hint1
    have h0 := ord_nonneg_of_mem w hmem
    rw [hord1, hzero] at h0
    rw [if_neg (show ¬ 0 < w.ord j from by omega), if_neg (show ¬ w.ord j < 0 from by omega)]
    by_cases hsub : 0 < w.ord (j - algebraMap K _ 1728)
    · rw [if_pos hsub]
      simp only [zero_add, add_zero]

      have h2 : (0 : ℤ) < 2 := by norm_num
      rw [neg_le, Int.le_ediv_iff_mul_le h2]
      push_cast at h0
      nlinarith
    · rw [if_neg hsub]
      simp only [add_zero, neg_zero]
      have hsub0 : 0 ≤ w.ord (j - algebraMap K _ 1728) :=
        ord_nonneg_of_mem w (w.toValuationSubring.sub_mem hjm (w.algebraMap_mem' _))
      have : w.ord (j - algebraMap K _ 1728) = 0 := le_antisymm (not_lt.1 hsub) hsub0
      rw [this] at h0
      push_cast at h0
      omega
  ·
    have hjm : j ∈ w.toValuationSubring := mem_of_ord_nonneg w hpos.le
    have hmem := mem_of_isIntegral_adjoin w hjm _ hint1
    have h0 := ord_nonneg_of_mem w hmem
    have hsub : w.ord (j - algebraMap K _ 1728) = 0 := ord_sub_algebraMap_eq_zero_of_ord_pos w hj0 h1728 hpos
    rw [hord1, hsub] at h0
    rw [if_pos hpos, if_neg (show ¬ 0 < w.ord (j - algebraMap K _ 1728) from by rw [hsub]; exact lt_irrefl 0),
      if_neg (show ¬ w.ord j < 0 from by omega)]
    simp only [add_zero]
    have h3 : (0 : ℤ) < 3 := by norm_num
    rw [neg_le, Int.le_ediv_iff_mul_le h3]
    push_cast at h0
    nlinarith

end S_ModularCurve_mem_riemannRochSpace_of_isModPFormFn
end P2MW
export P2MW.S_ModularCurve_mem_riemannRochSpace_of_isModPFormFn (solution)
