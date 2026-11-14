-- Prove2me | solution 1 for HararySachs.Hyper.phiPoly_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-13T22:10:33.883656+00:00
-- url     : https://prove2.me/submissions/242fbf9d-ba63-4dac-a10b-d35549790d29

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_TensorPhi
import Theorems.Thm_MvResultant_isWeightedHomogeneous_block
import Theorems.Thm_MvResultant_blockDegree_le
import Theorems.Thm_MvResultant_blockDegree_ge

open HararySachs.Hyper Finset

theorem solution (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res)
    {R : Type*} [CommRing R] (A : Fin n → (Fin (k - 1) → Fin n) → R) :
    (phiPoly (k := k) A res).natDegree ≤ n * (k - 1) ^ (n - 1) := by
  classical
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
  -- `Φ_A` as an `eval₂` over `ℤ`
  set c : ResVar n (fun _ => k - 1) → Polynomial R :=
    fun v => MvPolynomial.coeff v.2.1 (zcoord (k := k) A v.1) with hc
  have hphi : phiPoly (k := k) A res = MvPolynomial.eval₂ (Int.castRingHom (Polynomial R)) c res := by
    unfold phiPoly
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    congr 1
  -- every coefficient of the system has degree `≤ 1` in `z`
  have hc1 : ∀ v, (c v).natDegree ≤ 1 := by
    intro v
    simp only [hc]
    unfold zcoord
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, MvPolynomial.coeff_sum]
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · split_ifs <;> simp
    · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun t _ => ?_
      rw [MvPolynomial.coeff_monomial]
      split_ifs
      · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
      · simp
  -- bound term by term
  rw [hphi, MvPolynomial.eval₂_eq]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  refine (Polynomial.natDegree_mul_le).trans ?_
  rw [eq_intCast, Polynomial.natDegree_intCast, zero_add]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc ∑ v ∈ m.support, (c v ^ m v).natDegree
      ≤ ∑ v ∈ m.support, m v := sum_le_sum fun v _ =>
        (Polynomial.natDegree_pow_le).trans (by nlinarith [hc1 v])
    _ = n * δ := hR m hm
