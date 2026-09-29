-- Prove2me | solution 1 for ModularCurve.exists_polynomial_mul_aeval_eq_aeval_of_coeffMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/013cf4f4-8965-5344-871b-e42987314b34

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_polynomial_mul_aeval_eq_aeval_of_coeffMap
set_option autoImplicit false
set_option linter.unusedSectionVars false

open ModularCurve Polynomial

namespace QDescent

variable {K₀ k : Type*} [Field K₀] [Field k] (ι : K₀ →+* k)

theorem linearIndependent_coeffMap {I : Type*} [Fintype I] (v : I → LaurentSeries K₀) (hv : LinearIndependent K₀ v) :
    LinearIndependent k (fun i => coeffMap ι (v i)) := by
  classical
  letI : Algebra K₀ k := ι.toAlgebra
  rw [Fintype.linearIndependent_iff]
  intro c hc i₀
  let B := Module.Free.chooseBasis K₀ k
  suffices h : ∀ l, B.repr (c i₀) l = 0 by
    have : B.repr (c i₀) = 0 := Finsupp.ext h
    simpa using this
  intro l
  have hrel : ∑ i, (B.repr (c i) l) • v i = 0 := by
    ext n
    have hn := congrArg (fun f : LaurentSeries k => B.repr (f.coeff n) l) hc
    simp only [HahnSeries.coeff_sum, HahnSeries.coeff_smul, coeffMap_coeff, smul_eq_mul, map_sum,
      HahnSeries.coeff_zero, map_zero, Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_finset_sum,
      Finset.sum_apply] at hn
    rw [HahnSeries.coeff_sum]
    simp only [HahnSeries.coeff_smul, smul_eq_mul, HahnSeries.coeff_zero]
    rw [← hn]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : c i * ι ((v i).coeff n) = ((v i).coeff n) • c i := by
      rw [Algebra.smul_def, mul_comm]; rfl
    rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  exact (Fintype.linearIndependent_iff.mp hv) (fun i => B.repr (c i) l) hrel i₀

theorem exists_rel_of_rel_coeffMap {I : Type*} [Fintype I] (v : I → LaurentSeries K₀) (c : I → k)
    (hc : ∑ i, c i • coeffMap ι (v i) = 0) (hc0 : c ≠ 0) :
    ∃ d : I → K₀, d ≠ 0 ∧ ∑ i, d i • v i = 0 := by
  classical
  by_contra h
  push Not at h
  have hv : LinearIndependent K₀ v := by
    rw [Fintype.linearIndependent_iff]
    intro d hd
    by_contra hne
    push Not at hne
    obtain ⟨i, hi⟩ := hne
    exact (h d (fun h0 => hi (by rw [h0]; rfl))) hd
  have := (Fintype.linearIndependent_iff.mp (linearIndependent_coeffMap ι v hv)) c hc
  exact hc0 (funext this)

theorem coeff_sum_monomial {R : Type*} [Semiring R] (n : ℕ) (e : Fin (n + 1) → R) (j : Fin (n + 1)) :
    (∑ i : Fin (n + 1), monomial (i : ℕ) (e i)).coeff (j : ℕ) = e j := by
  rw [finsetSum_coeff, Finset.sum_eq_single j]
  · rw [coeff_monomial, if_pos rfl]
  · intro i _ hij
    rw [coeff_monomial, if_neg (fun h => hij (Fin.ext h))]
  · intro h; exact absurd (Finset.mem_univ j) h

variable {K : Type*} [Field K] in
theorem aeval_eq_sum_single (x : LaurentSeries K) (P : Polynomial K) {n : ℕ} (hn : P.natDegree < n + 1) :
    aeval x P = ∑ i : Fin (n + 1), HahnSeries.C (P.coeff i) * x ^ (i : ℕ) := by
  rw [aeval_def, eval₂_eq_sum_range' _ hn, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply]

variable {K : Type*} [Field K] in
theorem aeval_sum_monomial (n : ℕ) (e : Fin (n + 1) → K) (x : LaurentSeries K) :
    aeval x (∑ i : Fin (n + 1), monomial (i : ℕ) (e i)) = ∑ i : Fin (n + 1), HahnSeries.C (e i) * x ^ (i : ℕ) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [aeval_monomial, algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply]

variable {K : Type*} [Field K] in
theorem smul_eq_single_mul (a : K) (x : LaurentSeries K) : a • x = HahnSeries.C a * x := by
  rw [← HahnSeries.C_mul_eq_smul]

theorem exists_polynomial_mul_aeval_eq_aeval (t r : LaurentSeries K₀) (ht : Transcendental K₀ t)
    (hr : ∃ P Q : Polynomial k, aeval (coeffMap ι t) Q ≠ 0 ∧
      coeffMap ι r * aeval (coeffMap ι t) Q = aeval (coeffMap ι t) P) :
    ∃ P Q : Polynomial K₀, Q ≠ 0 ∧ r * aeval t Q = aeval t P := by
  classical
  obtain ⟨P, Q, hQ, hPQ⟩ := hr
  have hQ0 : Q ≠ 0 := by rintro rfl; simp at hQ
  set n : ℕ := max P.natDegree Q.natDegree with hn
  set t' := coeffMap ι t with ht'
  set r' := coeffMap ι r with hr'
  let v : Fin (n + 1) ⊕ Fin (n + 1) → LaurentSeries K₀ :=
    fun s => Sum.elim (fun i : Fin (n + 1) => r * t ^ (i : ℕ)) (fun i : Fin (n + 1) => t ^ (i : ℕ)) s
  let c : Fin (n + 1) ⊕ Fin (n + 1) → k :=
    fun s => Sum.elim (fun i : Fin (n + 1) => Q.coeff i) (fun i : Fin (n + 1) => -P.coeff i) s
  have hP' := aeval_eq_sum_single t' P (show P.natDegree < n + 1 by omega)
  have hQ' := aeval_eq_sum_single t' Q (show Q.natDegree < n + 1 by omega)
  have hc : ∑ s, c s • coeffMap ι (v s) = 0 := by
    simp only [smul_eq_single_mul]
    rw [Fintype.sum_sum_type]
    simp only [v, c, Sum.elim_inl, Sum.elim_inr, map_mul, map_pow]
    rw [← ht', ← hr']
    have h1 : ∑ i : Fin (n + 1), HahnSeries.C (Q.coeff ↑i) * (r' * t' ^ (i : ℕ)) = r' * aeval t' Q := by
      rw [hQ', Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have h2 : ∑ i : Fin (n + 1), HahnSeries.C (-P.coeff ↑i) * t' ^ (i : ℕ) = -aeval t' P := by
      rw [hP', ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_neg]; ring
    rw [h1, h2, hPQ, add_neg_cancel]
  have hc0 : c ≠ 0 := by
    intro h0
    have hlead : Q.coeff Q.natDegree ≠ 0 := by
      rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hQ0
    have := congrFun h0 (Sum.inl ⟨Q.natDegree, by omega⟩)
    simp only [c, Sum.elim_inl, Pi.zero_apply] at this
    exact hlead this
  obtain ⟨d, hd0, hd⟩ := exists_rel_of_rel_coeffMap ι v c hc hc0
  let Qb : Polynomial K₀ := ∑ i : Fin (n + 1), monomial (i : ℕ) (d (Sum.inl i))
  let Pb : Polynomial K₀ := ∑ i : Fin (n + 1), monomial (i : ℕ) (-d (Sum.inr i))
  have hrel : r * aeval t Qb = aeval t Pb := by
    simp only [smul_eq_single_mul] at hd
    rw [Fintype.sum_sum_type] at hd
    simp only [v, Sum.elim_inl, Sum.elim_inr] at hd
    rw [aeval_sum_monomial, aeval_sum_monomial, Finset.mul_sum]
    have h2 : ∑ i : Fin (n + 1), HahnSeries.C (-d (Sum.inr i)) * t ^ (i : ℕ)
        = -∑ i : Fin (n + 1), HahnSeries.C (d (Sum.inr i)) * t ^ (i : ℕ) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_neg]; ring
    rw [h2, eq_neg_iff_add_eq_zero, ← hd]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  refine ⟨Pb, Qb, ?_, hrel⟩
  intro hQb
  have hPb : aeval t Pb = 0 := by rw [← hrel, hQb, map_zero, mul_zero]
  have hPb0 : Pb ≠ 0 := by
    intro hPb0
    apply hd0
    funext s
    rcases s with i | i
    · have := congrArg (fun P : Polynomial K₀ => P.coeff (i : ℕ)) hQb
      simp only [Qb, coeff_sum_monomial, coeff_zero] at this
      exact this
    · have := congrArg (fun P : Polynomial K₀ => P.coeff (i : ℕ)) hPb0
      simp only [Pb, coeff_sum_monomial, coeff_zero, neg_eq_zero] at this
      exact this
  exact ht ⟨Pb, hPb0, hPb⟩

end QDescent

theorem solution
    {K₀ k : Type*} [Field K₀] [Field k] (ι : K₀ →+* k)
    (t r : LaurentSeries K₀) (ht : Transcendental K₀ t)
    (hr : ∃ P Q : Polynomial k, Polynomial.aeval (coeffMap ι t) Q ≠ 0 ∧
      coeffMap ι r * Polynomial.aeval (coeffMap ι t) Q = Polynomial.aeval (coeffMap ι t) P) :
    ∃ P Q : Polynomial K₀, Q ≠ 0 ∧ r * Polynomial.aeval t Q = Polynomial.aeval t P :=
  QDescent.exists_polynomial_mul_aeval_eq_aeval ι t r ht hr

end S_ModularCurve_exists_polynomial_mul_aeval_eq_aeval_of_coeffMap
end P2MW
export P2MW.S_ModularCurve_exists_polynomial_mul_aeval_eq_aeval_of_coeffMap (solution)
