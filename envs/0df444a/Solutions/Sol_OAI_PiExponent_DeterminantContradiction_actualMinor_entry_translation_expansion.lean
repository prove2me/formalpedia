-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actualMinor_entry_translation_expansion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:06:17.388074+00:00
-- url     : https://prove2.me/submissions/938fc80f-2595-4eb0-b551-e3181f479871

import Definitions.Def_OAI_PiExponent_MinorTranslationData
import Mathlib

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open scoped BigOperators

namespace S106TE

open MvPolynomial in
lemma coeff_prod {R : Type*} [CommRing R] {m : ℕ} (a : Fin m → ℕ) (A : Fin m →₀ ℕ) (α : Fin m → R) :
    MvPolynomial.coeff A (∏ i : Fin m, (MvPolynomial.C (α i) + MvPolynomial.X i) ^ a i :
        MvPolynomial (Fin m) R) =
      ∏ i, (((a i).choose (A i) : ℕ) : R) * α i ^ (a i - A i) := by
  classical
  set g : Fin m → ℕ → R := fun i k => α i ^ (a i - k) * ((a i).choose k : R)
  have h1 : ∀ i, (C (α i) + X i : MvPolynomial (Fin m) R) ^ (a i) =
      ∑ k ∈ Finset.range (a i + 1), monomial (Finsupp.single i k) (g i k) := by
    intro i
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [g, X_pow_eq_monomial, ← C_pow, C_mul_monomial]
    rw [← map_natCast (C : R →+* MvPolynomial (Fin m) R)]
    rw [mul_assoc, ← map_mul, mul_comm, C_mul_monomial, mul_one]
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_univ_sum]
  simp_rw [← monomial_sum_prod, coeff_sum, coeff_monomial]
  have hfs : ∀ κ : Fin m → ℕ, (∑ i, Finsupp.single i (κ i) = A) ↔ κ = ⇑A := by
    intro κ
    constructor
    · rintro h; funext i; rw [← h]; simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
    · rintro rfl; ext j; simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
  simp_rw [hfs]
  rw [Finset.sum_ite_eq']
  split_ifs with hA
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp only [g]; ring
  · have : ∃ i, a i < A i := by
      by_contra h; push Not at h
      exact hA (Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 (Nat.lt_succ_of_le (h i)))
    obtain ⟨i, hi⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [Nat.choose_eq_zero_of_lt hi]; simp)]

/-- convolution against a `Fin (s+1)` index -/
lemma conv (s : ℕ) (X Y : PowerSeries ℂ) (z : ℂ) :
    ∑ e : Fin (s + 1), (z * PowerSeries.coeff (e : ℕ) X) * PowerSeries.coeff (s - e) Y =
      PowerSeries.coeff s (PowerSeries.C z * X * Y) := by
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => PowerSeries.coeff i X *
      PowerSeries.coeff j Y), Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun e _ => by ring

/-- per-variable binomial identity -/
lemma binom (a b : ℕ) (L V : PowerSeries ℂ) :
    ∑ x ∈ Finset.range (a + 1), (((a.choose x * x.choose b : ℕ) : PowerSeries ℂ)) *
        L ^ (a - x) * V ^ (x - b) =
      ((a.choose b : ℕ) : PowerSeries ℂ) * (L + V) ^ (a - b) := by
  rcases lt_or_ge a b with hab | hab
  · rw [Nat.choose_eq_zero_of_lt hab]
    simp only [Nat.cast_zero, zero_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    have : x < b := lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)) hab
    rw [Nat.choose_eq_zero_of_lt this]; simp
  · have hsplit : a + 1 = b + (a - b + 1) := by omega
    rw [hsplit, Finset.sum_range_add]
    have h0 : ∑ x ∈ Finset.range b, (((a.choose x * x.choose b : ℕ) : PowerSeries ℂ)) *
        L ^ (a - x) * V ^ (x - b) = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hx)]; simp
    rw [h0, zero_add, add_comm L V, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    have hy' : y ≤ a - b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hy)
    rw [Nat.choose_mul (by omega : b ≤ b + y)]
    have e1 : a - (b + y) = a - b - y := by omega
    have e2 : b + y - b = y := by omega
    rw [e1, e2]
    push_cast
    ring

lemma lw_pos {nu : ℝ} (d : FixedData nu) (i : Fin d.m) : 0 < fixedWeights d i := by
  simp only [fixedWeights, MatrixArithmetic.logWeights, finiteDenominators]
  have hq : (2 : ℝ) ≤ (d.q i.val : ℝ) := by exact_mod_cast (d.approximations i.val).1
  have hlog : 0 < Real.log (d.q i.val : ℝ) := Real.log_pos (by linarith)
  exact_mod_cast Nat.ceil_pos.mpr hlog

lemma box {R : Type*} [CommRing R] {nu : ℝ} (d : FixedData nu) {H : ℝ} (cc : Column d H)
    (φ : Fin d.m → ℕ → R) (hφ : ∀ i x, cc.1 i.succ < x → φ i x = 0) :
    ∑ A : Transverse d H, ∏ i, φ i (A.1 i) =
      ∏ i, ∑ x ∈ Finset.range (cc.1 i.succ + 1), φ i x := by
  classical
  rw [Finset.prod_univ_sum, Finset.sum_coe_sort (transverseIndices (fixedWeights d) H)
    (fun A => ∏ i, φ i (A i)), transverseIndices, Finset.sum_map]
  simp only [Equiv.coe_toEmbedding, Finsupp.coe_equivFunOnFinite_symm]
  symm
  apply Finset.sum_subset
  · intro A hA
    rw [Fintype.mem_piFinset] at hA
    have hcol := cc.2
    simp only [realWeightedSimplex, Finset.mem_filter] at hcol ⊢
    have hsum := hcol.2
    rw [Fin.sum_univ_succ] at hsum
    simp only [InterpolationMatrix.columnWeights, Fin.cases_zero, Fin.cases_succ] at hsum
    have h0 : 0 ≤ (d.w0 : ℝ) * (cc.1 0 : ℝ) := mul_nonneg d.w0_pos.le (Nat.cast_nonneg _)
    have hle : ∑ i, fixedWeights d i * (A i : ℝ) ≤ H := by
      refine le_trans (Finset.sum_le_sum fun i _ => ?_) (by linarith)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp (hA i)))
        (lw_pos d i).le
    refine ⟨Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor ?_)), hle⟩
    rw [le_div_iff₀ (lw_pos d i), mul_comm]
    refine le_trans ?_ hle
    exact Finset.single_le_sum (f := fun i => fixedWeights d i * (A i : ℝ))
      (fun i _ => mul_nonneg (lw_pos d i).le (Nat.cast_nonneg _)) (Finset.mem_univ i)
  · intro A _ hA
    rw [Fintype.mem_piFinset] at hA
    push Not at hA
    obtain ⟨i, hi⟩ := hA
    rw [Finset.mem_range, not_lt] at hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hφ i _ (by omega))

end S106TE

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (selection : Row d H → Column d H) (f0 : ChoiceFamily d H)
    (r c : Row d H) :
    (actualMinor d H selection) r c =
      ∑ t : RowChoice d H r,
        choiceScalar d r t *
          (choiceMatrix d selection (Function.update f0 r t)) r c := by
  classical
  set j : ℕ := r.1.val with hj
  set s : ℕ := r.2.1 0 with hs
  set b := beta d r with hb
  set h : ℕ := (selection c).1 0 with hh
  set a : Fin d.m → ℕ := fun i => (selection c).1 i.succ with ha
  set T := MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 with hT
  set U : Fin d.m → ℂ := fun i => (j : ℂ) *
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i - period) with hU
  set L : PowerSeries ℂ := PowerSeries.C ((j : ℂ) * period) + PowerSeries.log ℂ with hL
  set V : Fin d.m → PowerSeries ℂ := fun i => PowerSeries.C (U i) + tail (T i) with hV
  -- left side
  have hLHS : (actualMinor d H selection) r c = PowerSeries.coeff s
      ((1 + PowerSeries.X) ^ h * ∏ i, (((a i).choose (b i) : ℕ) : PowerSeries ℂ) *
        (L + V i) ^ (a i - b i)) := by
    simp only [actualMinor, MatrixArithmetic.selectedMinor, Matrix.submatrix_apply, id,
      InterpolationMatrix.truncatedLogMatrix, InterpolationMatrix.matrix, InterpolationMatrix.entry,
      InterpolationMatrix.monomialImage]
    rw [MvPolynomial.coeff_C_mul, S106TE.coeff_prod, ← Polynomial.coeff_coe]
    congr 1
    simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one,
      Polynomial.coe_X, Polynomial.coeff_coe]
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    simp only [Polynomial.coeToPowerSeries.ringHom_apply]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Polynomial.coeToPowerSeries.ringHom_apply]
    simp only [map_mul, map_pow, map_natCast, map_add, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_C]
    congr 2
    simp only [hL, hV, hU, tail, InterpolationMatrix.truncatedLog]
    have : ((r.1.val : ℕ) : PowerSeries ℂ) * PowerSeries.C (MatrixArithmetic.rationalCenters
        (finiteNumerators d) (finiteDenominators d) i) = PowerSeries.C ((j : ℂ) * period) +
        PowerSeries.C ((j : ℂ) * (MatrixArithmetic.rationalCenters (finiteNumerators d)
          (finiteDenominators d) i - period)) := by
      rw [← map_natCast PowerSeries.C, ← map_mul, ← map_add]; congr 1; ring
    rw [this]; ring
  rw [hLHS]
  have hY : ∀ A : Transverse d H, (periodMonomial j h a).coeff A.1 = (1 + PowerSeries.X) ^ h *
      ∏ i, (((a i).choose (A.1 i) : ℕ) : PowerSeries ℂ) * L ^ (a i - A.1 i) := by
    intro A
    simp only [periodMonomial]
    rw [MvPolynomial.coeff_C_mul, S106TE.coeff_prod]
  have hk : ∀ (A : Transverse d H) (k : ∀ i, Fin (A.1 i - beta d r i + 1)),
      ∑ e : Fin (r.2.1 0 + 1), choiceScalar d r ⟨A, (k, e)⟩ *
        choiceMatrix d selection (Function.update f0 r ⟨A, (k, e)⟩) r c =
      PowerSeries.coeff s (PowerSeries.C
        ((((∏ i, (A.1 i).choose (b i) * (A.1 i - b i).choose (k i) : ℕ)) : ℂ) *
          ∏ i, U i ^ (A.1 i - b i - k i)) *
        (∏ i, tail (T i) ^ (k i : ℕ)) * (periodMonomial j h a).coeff A.1) := by
    intro A k
    refine (Finset.sum_congr rfl fun e _ => ?_).trans (S106TE.conv s
      (∏ i, tail (T i) ^ (k i : ℕ)) ((periodMonomial j h a).coeff A.1) _)
    simp only [choiceScalar, choiceMatrix]
    rw [Function.update_self]
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun k _ => hk A k]
  rw [Finset.sum_congr rfl fun A _ => (map_sum (PowerSeries.coeff s) _ _).symm, ← map_sum]
  congr 1
  rw [Finset.sum_congr rfl fun A _ => (Finset.sum_mul _ _ _).symm]
  have hK : ∀ A : Transverse d H, ∑ k : (∀ i, Fin (A.1 i - beta d r i + 1)), PowerSeries.C
        ((((∏ i, (A.1 i).choose (b i) * (A.1 i - b i).choose (k i) : ℕ)) : ℂ) *
          ∏ i, U i ^ (A.1 i - b i - k i)) * (∏ i, tail (T i) ^ (k i : ℕ)) =
      ∏ i, (((A.1 i).choose (b i) : ℕ) : PowerSeries ℂ) * V i ^ (A.1 i - b i) := by
    intro A
    have e1 : ∀ k : (∀ i, Fin (A.1 i - beta d r i + 1)), PowerSeries.C
        ((((∏ i, (A.1 i).choose (b i) * (A.1 i - b i).choose (k i) : ℕ)) : ℂ) *
          ∏ i, U i ^ (A.1 i - b i - k i)) * (∏ i, tail (T i) ^ (k i : ℕ)) =
        ∏ i, ((((A.1 i).choose (b i) * (A.1 i - b i).choose (k i) : ℕ) : PowerSeries ℂ) *
          PowerSeries.C (U i) ^ (A.1 i - b i - k i) * tail (T i) ^ (k i : ℕ)) := by
      intro k
      rw [map_mul, Nat.cast_prod, map_prod, map_prod, ← Finset.prod_mul_distrib,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_natCast, map_pow]
    rw [Finset.sum_congr rfl fun k _ => e1 k]
    symm
    calc ∏ i, (((A.1 i).choose (b i) : ℕ) : PowerSeries ℂ) * V i ^ (A.1 i - b i)
        = ∏ i, ∑ x : Fin (A.1 i - beta d r i + 1),
            ((((A.1 i).choose (b i) * (A.1 i - b i).choose x : ℕ) : PowerSeries ℂ) *
              PowerSeries.C (U i) ^ (A.1 i - b i - x) * tail (T i) ^ (x : ℕ)) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [Fin.sum_univ_eq_sum_range (fun x => ((((A.1 i).choose (b i) * (A.1 i - b i).choose x : ℕ) :
            PowerSeries ℂ) * PowerSeries.C (U i) ^ (A.1 i - b i - x) * tail (T i) ^ x)) (A.1 i - b i + 1)]
          simp only [hV]
          rw [add_comm (PowerSeries.C (U i)), add_pow, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          push_cast
          ring
      _ = _ := by rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [Finset.sum_congr rfl fun A _ => by rw [hK A, hY A]]
  have e2 : ∀ A : Transverse d H, (∏ i, (((A.1 i).choose (b i) : ℕ) : PowerSeries ℂ) *
      V i ^ (A.1 i - b i)) * ((1 + PowerSeries.X) ^ h *
      ∏ i, (((a i).choose (A.1 i) : ℕ) : PowerSeries ℂ) * L ^ (a i - A.1 i)) =
      (1 + PowerSeries.X) ^ h * ∏ i, ((((a i).choose (A.1 i) * (A.1 i).choose (b i) : ℕ) :
        PowerSeries ℂ) * L ^ (a i - A.1 i) * V i ^ (A.1 i - b i)) := by
    intro A
    rw [mul_left_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    push_cast
    ring
  rw [Finset.sum_congr rfl fun A _ => e2 A, ← Finset.mul_sum]
  congr 1
  rw [S106TE.box d (selection c) (fun i x => ((((a i).choose x * x.choose (b i) : ℕ) :
      PowerSeries ℂ) * L ^ (a i - x) * V i ^ (x - b i))) (by
        intro i x hx
        rw [Nat.choose_eq_zero_of_lt hx]; simp)]
  exact Finset.prod_congr rfl fun i _ => (S106TE.binom _ _ _ _).symm
