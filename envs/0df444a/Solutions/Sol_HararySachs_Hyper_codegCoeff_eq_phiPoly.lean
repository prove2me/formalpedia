-- Prove2me | solution 1 for HararySachs.Hyper.codegCoeff_eq_phiPoly
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-13T03:45:34.62901+00:00
-- url     : https://prove2.me/submissions/3dea2f3e-5308-4e91-ab09-858e0a6a6048

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_TensorPhi
import Theorems.Thm_MvResultant_isWeightedHomogeneous_block
import Theorems.Thm_MvResultant_blockDegree_le
import Theorems.Thm_MvResultant_blockDegree_ge

open HararySachs.Hyper Finset

namespace RevAux

open Polynomial

/-- reflection of a sum -/
lemma reflect_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) (N : ℕ) :
    reflect N (∑ i ∈ s, f i) = ∑ i ∈ s, reflect N (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, reflect_add, ih]

/-- reflection of a power of a polynomial of degree `≤ 1` -/
lemma reflect_pow (p : ℚ[X]) (hp : p.natDegree ≤ 1) (e : ℕ) :
    reflect e (p ^ e) = (reflect 1 p) ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h1 : (p ^ e).natDegree ≤ e := by
      have := natDegree_pow_le (p := p) (n := e); nlinarith
    rw [pow_succ, reflect_mul _ _ h1 hp, ih, pow_succ]

/-- reflection of a product -/
lemma reflect_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) (d : ι → ℕ)
    (hf : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    reflect (∑ i ∈ s, d i) (∏ i ∈ s, f i) = ∏ i ∈ s, reflect (d i) (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha, prod_insert ha]
    have h2 : (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, d i :=
      (natDegree_prod_le _ _).trans (sum_le_sum fun i hi => hf i (mem_insert_of_mem hi))
    rw [reflect_mul _ _ (hf a (mem_insert_self a s)) h2,
      ih fun i hi => hf i (mem_insert_of_mem hi)]

/-- reflecting a homogeneous resultant evaluation -/
lemma reflect_eval₂ {σ : Type*} (R : MvPolynomial σ ℤ) (N : ℕ)
    (hR : ∀ m ∈ R.support, ∑ v ∈ m.support, m v = N)
    (f : σ → ℚ[X]) (hf : ∀ v, (f v).natDegree ≤ 1) :
    reflect N (MvPolynomial.eval₂ (Int.castRingHom ℚ[X]) f R) =
      MvPolynomial.eval₂ (Int.castRingHom ℚ[X]) (fun v => reflect 1 (f v)) R := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, reflect_sum]
  refine sum_congr rfl fun m hm => ?_
  rw [← hR m hm, eq_intCast, ← C_eq_intCast, reflect_C_mul]
  congr 1
  have := reflect_prod m.support (fun v => f v ^ m v) (fun v => m v) fun v _ => by
    have := natDegree_pow_le (p := f v) (n := m v)
    have h := hf v
    nlinarith
  rw [this]
  exact prod_congr rfl fun v _ => reflect_pow _ (hf v) _

end RevAux

namespace CodegAux

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

lemma zcoord_coeff (E : Finset (Finset (Fin n))) (j : Fin n) (α : Fin n →₀ ℕ) :
    MvPolynomial.coeff α (zcoord (R := ℚ) (k := k) (fun i t => adjEntry E (Fin.cons i t)) j) =
      Polynomial.C (if Finsupp.single j (k - 1) = α then (1 : ℚ) else 0) +
        Polynomial.C (-(∑ t : Fin (k - 1) → Fin n,
          if (∑ a : Fin (k - 1), Finsupp.single (t a) 1) = α then
            adjEntry E (Fin.cons j t : Fin (k - 1 + 1) → Fin n) else 0)) * Polynomial.X := by
  unfold zcoord
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [map_neg, map_sum, neg_mul, sum_mul]
  simp only [apply_ite Polynomial.C, map_zero, ite_mul, zero_mul]
  split_ifs <;> simp [sub_eq_add_neg]

lemma reflect_linear (e a : ℚ) :
    Polynomial.reflect 1 (Polynomial.C e * Polynomial.X + Polynomial.C a) =
      Polynomial.C e + Polynomial.C a * Polynomial.X := by
  rw [Polynomial.reflect_add, show Polynomial.C e * Polynomial.X =
      Polynomial.C e * Polynomial.X ^ 1 by rw [pow_one], Polynomial.reflect_C_mul_X_pow,
    Polynomial.reflect_C, Polynomial.revAt_le (le_refl 1)]
  simp

end CodegAux

open CodegAux RevAux in
theorem solution (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (E : Finset (Finset (Fin n)))
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res)
    (d : ℕ) (hd : d ≤ n * (k - 1) ^ (n - 1)) :
    codegCoeff (k := k) E res d =
      (phiPoly (R := ℚ) (k := k) (fun i t => adjEntry E (Fin.cons i t)) res).coeff d := by
  set δ := (k - 1) ^ (n - 1) with hδdef
  have hD : ∀ j : Fin n, 1 ≤ (fun _ : Fin n => k - 1) j := fun _ => by simp only; omega
  -- block homogeneity of exact degree `δ`
  have hδ : ∀ i : Fin n, res.IsWeightedHomogeneous
      (fun v : ResVar n (fun _ => k - 1) => if v.1 = i then 1 else 0) δ := by
    intro i
    obtain ⟨δ', h⟩ := MvResultant.isWeightedHomogeneous_block res hres i
    have h1 := MvResultant.blockDegree_le hD res hres i δ' h
    have h2 := MvResultant.blockDegree_ge hD res hres i δ' h
    have hp : ∏ j ∈ Finset.univ.erase i, (fun _ : Fin n => k - 1) j = δ := by
      rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
    rw [hp] at h1 h2
    rwa [show δ' = δ by omega] at h
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
  -- both polynomials as `eval₂` over `ℤ`
  set c : ResVar n (fun _ => k - 1) → Polynomial ℚ :=
    fun v => MvPolynomial.coeff v.2.1 (coord (k := k) E v.1) with hc
  have hcp : charPoly (k := k) E res =
      MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ)) c res := by
    unfold charPoly
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    congr 1
  have hphi : phiPoly (R := ℚ) (k := k) (fun i t => adjEntry E (Fin.cons i t)) res =
      MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ))
        (fun v => Polynomial.reflect 1 (c v)) res := by
    unfold phiPoly
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    congr 1
    funext v
    simp only [hc]
    rw [coord_coeff, zcoord_coeff, reflect_linear]
  have hnat : ∀ v, (c v).natDegree ≤ 1 := fun v => by
    simp only [hc]; rw [coord_coeff]; exact Polynomial.natDegree_linear_le
  rw [hphi, ← reflect_eval₂ res (n * δ) hR c hnat, ← hcp, Polynomial.coeff_reflect,
    Polynomial.revAt_le hd]
  rfl
