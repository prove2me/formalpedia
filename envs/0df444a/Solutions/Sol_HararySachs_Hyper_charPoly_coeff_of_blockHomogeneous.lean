-- Prove2me | solution 1 for HararySachs.Hyper.charPoly_coeff_of_blockHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-12T18:51:36.93847+00:00
-- url     : https://prove2.me/submissions/a7f9c8ca-2572-45aa-be2d-bf37819976b7

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly

open HararySachs.Hyper Finset

namespace CoeffTopAux

open Polynomial in
/-- top coefficient of a product of polynomials of bounded degrees -/
lemma coeff_prod_pow {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) (d : ι → ℕ)
    (hf : ∀ i ∈ s, (f i).natDegree ≤ 1) :
    (∏ i ∈ s, f i ^ d i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff 1 ^ d i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, prod_insert ha]
    have h1 : (f a ^ d a).natDegree ≤ d a := by
      have := natDegree_pow_le (p := f a) (n := d a)
      have h := hf a (mem_insert_self a s)
      nlinarith
    have h2 : (∏ i ∈ s, f i ^ d i).natDegree ≤ ∑ i ∈ s, d i := by
      refine (natDegree_prod_le _ _).trans (sum_le_sum fun i hi => ?_)
      have := natDegree_pow_le (p := f i) (n := d i)
      have h := hf i (mem_insert_of_mem hi)
      nlinarith
    rw [coeff_mul_add_eq_of_natDegree_le h1 h2, ih fun i hi => hf i (mem_insert_of_mem hi)]
    congr 1
    have := coeff_pow_of_natDegree_le (p := f a) (n := 1) (m := d a) (hf a (mem_insert_self a s))
    rwa [mul_one] at this

/-- generic top-coefficient lemma -/
lemma coeff_eval₂_of_homogeneous {σ : Type*} (R : MvPolynomial σ ℤ) (N : ℕ)
    (hR : ∀ m ∈ R.support, ∑ v ∈ m.support, m v = N)
    (f : σ → Polynomial ℚ) (hf : ∀ v, (f v).natDegree ≤ 1) :
    (MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ)) f R).coeff N =
      MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun v => (f v).coeff 1) R := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Polynomial.finsetSum_coeff]
  refine sum_congr rfl fun m hm => ?_
  rw [eq_intCast, eq_intCast, ← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul, ← hR m hm,
    coeff_prod_pow _ _ _ fun v _ => hf v]

variable {n k : ℕ}

lemma coord_coeff (E : Finset (Finset (Fin n))) (j : Fin n) (α : Fin n →₀ ℕ) :
    MvPolynomial.coeff α (coord (k := k) E j) =
      Polynomial.C (if Finsupp.single j (k - 1) = α then (1 : ℚ) else 0) * Polynomial.X +
        Polynomial.C (-(∑ t : Fin (k - 1) → Fin n,
          if (∑ a : Fin (k - 1), Finsupp.single (t a) 1) = α then
            adjEntry E (Fin.cons j t : Fin (k - 1 + 1) → Fin n) else 0)) := by
  unfold coord
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [map_neg, map_sum]
  simp only [apply_ite Polynomial.C, map_zero]
  split_ifs <;> simp [sub_eq_add_neg]

lemma coord_coeff_natDegree (E : Finset (Finset (Fin n))) (j : Fin n) (α : Fin n →₀ ℕ) :
    (MvPolynomial.coeff α (coord (k := k) E j)).natDegree ≤ 1 := by
  rw [coord_coeff]; exact Polynomial.natDegree_linear_le

lemma coord_coeff_one (E : Finset (Finset (Fin n))) (j : Fin n) (α : Fin n →₀ ℕ) :
    (MvPolynomial.coeff α (coord (k := k) E j)).coeff 1 =
      if Finsupp.single j (k - 1) = α then (1 : ℚ) else 0 := by
  rw [coord_coeff]
  split_ifs <;> simp

end CoeffTopAux

open CoeffTopAux in
theorem solution (n k : ℕ) (E : Finset (Finset (Fin n)))
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ) (δ : ℕ)
    (hδ : ∀ i : Fin n, res.IsWeightedHomogeneous
      (fun v : ResVar n (fun _ => k - 1) => if v.1 = i then 1 else 0) δ)
    (hnorm : MvPolynomial.aeval (fun v : ResVar n (fun _ => k - 1) =>
      if v.2.1 = Finsupp.single v.1 (k - 1) then (1 : ℤ) else 0) res = 1) :
    (charPoly (k := k) E res).coeff (n * δ) = 1 := by
  set c : ResVar n (fun _ => k - 1) → Polynomial ℚ :=
    fun v => MvPolynomial.coeff v.2.1 (coord (k := k) E v.1) with hc
  -- every monomial of `res` has total degree `n * δ`
  have hR : ∀ m ∈ res.support, ∑ v ∈ m.support, m v = n * δ := by
    intro m hm
    have hw : ∀ i : Fin n, ∑ v ∈ m.support, m v * (if v.1 = i then 1 else 0) = δ := by
      intro i
      have := hδ i (MvPolynomial.mem_support_iff.mp hm)
      rw [Finsupp.weight_apply, Finsupp.sum] at this
      simpa [smul_eq_mul] using this
    calc ∑ v ∈ m.support, m v
        = ∑ v ∈ m.support, ∑ i : Fin n, m v * (if v.1 = i then 1 else 0) := by
          refine sum_congr rfl fun v _ => ?_
          rw [← mul_sum, sum_ite_eq]; simp
      _ = ∑ i : Fin n, δ := by rw [sum_comm]; exact sum_congr rfl fun i _ => hw i
      _ = n * δ := by simp
  -- rewrite `charPoly` as an `eval₂` over `ℤ`
  have hcp : charPoly (k := k) E res =
      MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ)) c res := by
    unfold charPoly
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    congr 1
  rw [hcp, coeff_eval₂_of_homogeneous res (n * δ) hR c
    (fun v => coord_coeff_natDegree E v.1 v.2.1)]
  have he : (fun v : ResVar n (fun _ => k - 1) => (c v).coeff 1) =
      fun v => ((Int.castRingHom ℚ)
        (if v.2.1 = Finsupp.single v.1 (k - 1) then (1 : ℤ) else 0)) := by
    funext v
    simp only [hc, coord_coeff_one]
    by_cases h : (v.2 : Fin n →₀ ℕ) = Finsupp.single v.1 (k - 1)
    · rw [if_pos h.symm, if_pos h, map_one]
    · rw [if_neg (fun h' => h h'.symm), if_neg h, map_zero]
  rw [he]
  have := MvPolynomial.eval₂_comp_left (Int.castRingHom ℚ) (RingHom.id ℤ)
    (fun v : ResVar n (fun _ => k - 1) =>
      if v.2.1 = Finsupp.single v.1 (k - 1) then (1 : ℤ) else 0) res
  rw [RingHom.comp_id] at this
  have h2 : MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun v : ResVar n (fun _ => k - 1) =>
      (Int.castRingHom ℚ) (if v.2.1 = Finsupp.single v.1 (k - 1) then (1 : ℤ) else 0)) res =
      (Int.castRingHom ℚ) (MvPolynomial.eval₂ (RingHom.id ℤ) (fun v : ResVar n (fun _ => k - 1) =>
        if v.2.1 = Finsupp.single v.1 (k - 1) then (1 : ℤ) else 0) res) := this.symm
  rw [h2]
  rw [MvPolynomial.aeval_def, Algebra.algebraMap_self] at hnorm
  rw [hnorm, map_one]
