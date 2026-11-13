-- Prove2me | solution 1 for MvResultant.blockDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-12T19:08:38.841194+00:00
-- url     : https://prove2.me/submissions/adf46bb5-4522-4601-9f96-70cb69b069b1

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Theorems.Thm_MvResultant_dvd_of_vanishing
import Theorems.Thm_MvResultant_exists_macaulay

open HararySachs.Hyper MvPolynomial Finset

theorem solution {n : ℕ} {D : Fin n → ℕ} (hD : ∀ j, 1 ≤ D j)
    (res : MvPolynomial (ResVar n D) ℤ) (hres : IsResultant n D res) (i : Fin n) (δ : ℕ)
    (hδ : res.IsWeightedHomogeneous (fun v : ResVar n D => if v.1 = i then 1 else 0) δ) :
    δ ≤ ∏ j ∈ Finset.univ.erase i, D j := by
  classical
  obtain ⟨Q, hQ, M, hM, hQline⟩ := MvResultant.exists_macaulay hD i
  set P := MvPolynomial.map (Int.castRingHom ℂ) res with hP
  obtain ⟨h, hh⟩ := MvResultant.dvd_of_vanishing res hres Q hQ
  -- the diagonal line `t ↦ (x_1^{D_1}, …, t x_i^{D_i}, …, x_n^{D_n})`
  set e : ResVar n D → ℤ := fun v => if v.2.1 = Finsupp.single v.1 (D v.1) then 1 else 0 with he
  set line : ResVar n D → Polynomial ℂ := fun v =>
    if v.2.1 = Finsupp.single v.1 (D v.1) then
      (if v.1 = i then (Polynomial.X : Polynomial ℂ) else 1) else 0 with hline
  have hline' : ∀ v, line v = Polynomial.C ((e v : ℤ) : ℂ) *
      Polynomial.X ^ (if v.1 = i then 1 else 0) := by
    intro v
    simp only [hline, he]
    split_ifs <;> simp
  -- on the line, the resultant is `t ^ δ`
  have hPline : aeval line P = Polynomial.X ^ δ := by
    rw [hP, aeval_def, eval₂_map, eval₂_eq]
    have hterm : ∀ m ∈ res.support,
        ((algebraMap ℂ (Polynomial ℂ)).comp (Int.castRingHom ℂ)) (coeff m res) *
          ∏ v ∈ m.support, line v ^ m v =
        Polynomial.C (((coeff m res * ∏ v ∈ m.support, e v ^ m v : ℤ)) : ℂ) *
          Polynomial.X ^ δ := by
      intro m hm
      have hw := hδ (mem_support_iff.mp hm)
      rw [Finsupp.weight_apply, Finsupp.sum] at hw
      simp only [smul_eq_mul] at hw
      simp only [hline', mul_pow, prod_mul_distrib, ← pow_mul, prod_pow_eq_pow_sum, hw,
        RingHom.comp_apply, Polynomial.algebraMap_eq, eq_intCast]
      push_cast
      rw [← Polynomial.C_eq_intCast]
      have hw' : ∑ x ∈ m.support, (if x.1 = i then 1 else 0) * m x = δ := by
        rw [← hw]; exact sum_congr rfl fun x _ => mul_comm _ _
      rw [hw', map_mul, map_prod]
      simp only [map_pow]
      ring
    rw [sum_congr rfl hterm, ← sum_mul, ← map_sum]
    have hnorm := hres.2.1
    rw [aeval_def, Algebra.algebraMap_self, eval₂_eq] at hnorm
    simp only [RingHom.id_apply] at hnorm
    have hnorm' : ∑ m ∈ res.support, coeff m res * ∏ v ∈ m.support, e v ^ m v = 1 := by
      simpa [he] using hnorm
    have : (∑ m ∈ res.support, (((coeff m res * ∏ v ∈ m.support, e v ^ m v : ℤ)) : ℂ)) = 1 := by
      rw [← Int.cast_sum, hnorm', Int.cast_one]
    rw [this, map_one, one_mul]
  -- compare degrees along the line
  have key := congrArg (aeval line) hh
  rw [map_mul, hPline, hQline] at key
  have hX : (Polynomial.X : Polynomial ℂ) ^ δ ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  have hg : aeval line h ≠ 0 := by
    intro h0; rw [h0, mul_zero] at key; exact (pow_ne_zero M Polynomial.X_ne_zero) key
  have := congrArg Polynomial.natDegree key
  rw [Polynomial.natDegree_mul hX hg, Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow]
    at this
  omega
