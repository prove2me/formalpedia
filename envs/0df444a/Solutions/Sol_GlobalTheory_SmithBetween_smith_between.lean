-- Prove2me | solution 1 for GlobalTheory.SmithBetween.smith_between
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:38:51.103158+00:00
-- url     : https://prove2.me/submissions/c02ce7fd-c9e5-44e9-ae17-2ad93225e165

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsMulEqMulDiagonal
import Theorems.Thm_GlobalTheory_SmithBetween_exists_mul_eq_mul_diagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.SmithBetween
open Matrix
open IsDedekindDomain NumberField
open Matrix
namespace GlobalTheory.SmithBetween
namespace _root_.GlobalTheory.SmithBetween
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R)
    (hϖ : Irreducible ϖ) (n k : ℕ) (hk : k ≤ n) (M M' : Matrix (Fin n) (Fin n) R)
    (hMM : M * M' = ϖ • (1 : Matrix (Fin n) (Fin n) R)) (hdet : Associated M.det (ϖ ^ k)) :
    ∃ P Q : Matrix (Fin n) (Fin n) R, IsUnit P.det ∧ IsUnit Q.det ∧
      M * Q = P * Matrix.diagonal (fun i : Fin n => if i.1 < n - k then (1 : R) else ϖ) := by
  classical
  have hM0 : M.det ≠ 0 := by
    rw [hdet.ne_zero_iff]; exact pow_ne_zero _ hϖ.ne_zero
  obtain ⟨P, Q, hP, hQ, c, hMQ⟩ := _root_.GlobalTheory.SmithBetween.exists_mul_eq_mul_diagonal M hM0
  have hdvd : ∀ j, c j ∣ ϖ := by
    intro j
    have hD : Matrix.diagonal c = P⁻¹ * M * Q := by
      rw [Matrix.mul_assoc, hMQ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]
    have hX : Matrix.diagonal c * (Q⁻¹ * M' * P) = ϖ • (1 : Matrix (Fin n) (Fin n) R) := by
      rw [hD]
      calc P⁻¹ * M * Q * (Q⁻¹ * M' * P) = P⁻¹ * (M * (Q * Q⁻¹) * M') * P := by
            simp only [Matrix.mul_assoc]
        _ = ϖ • (1 : Matrix (Fin n) (Fin n) R) := by
            rw [Matrix.mul_nonsing_inv _ hQ, Matrix.mul_one, hMM, Matrix.mul_smul, Matrix.mul_one,
              Matrix.smul_mul, Matrix.nonsing_inv_mul _ hP]
    have := congrFun (congrFun hX j) j
    simp only [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one] at this
    exact ⟨_, this.symm⟩
  let d : Fin n → R := fun j => if IsUnit (c j) then 1 else ϖ
  have hu : ∀ j, ∃ u : Rˣ, c j = d j * u := by
    intro j
    by_cases h : IsUnit (c j)
    · exact ⟨h.unit, by simp [d, h]⟩
    · obtain ⟨b, hb⟩ := hdvd j
      rcases hϖ.isUnit_or_isUnit hb with h' | h'
      · exact absurd h' h
      · refine ⟨h'.unit⁻¹, ?_⟩
        simp only [d, h, if_false, hb]
        rw [mul_assoc, IsUnit.mul_val_inv, mul_one]
  choose u hu using hu

  set s := (Finset.univ.filter fun j => ¬IsUnit (c j)).card with hs
  have hprod : ∏ j, d j = ϖ ^ s := by
    simp only [d]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  have hsk : s = k := by
    have h1 : M.det * Q.det = P.det * ∏ j, c j := by
      rw [← Matrix.det_mul, hMQ, Matrix.det_mul, Matrix.det_diagonal]
    have h2 : ∏ j, c j = ϖ ^ s * ∏ j, (u j : R) := by
      rw [← hprod, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun j _ => hu j
    have h3 : Associated (ϖ ^ s) M.det := by
      have hA : Associated (M.det * Q.det) M.det := (associated_mul_isUnit_left_iff hQ).2 (Associated.refl _)
      have hv : IsUnit (P.det * ∏ j, (u j : R)) :=
        hP.mul (by rw [← Units.coe_prod]; exact Units.isUnit _)
      have hB : Associated (ϖ ^ s) (P.det * ∏ j, c j) := by
        rw [h2, mul_left_comm]
        exact associated_mul_unit_right _ _ hv
      rw [← h1] at hB
      exact hB.trans hA
    have h4 : Associated (ϖ ^ s) (ϖ ^ k) := h3.trans hdet
    exact le_antisymm ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h4.dvd)
      ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h4.symm.dvd)
  let P' := P * Matrix.diagonal fun j => (u j : R)
  have hP' : IsUnit P'.det := by
    simp only [P', Matrix.det_mul, Matrix.det_diagonal]
    exact hP.mul (by rw [← Units.coe_prod]; exact Units.isUnit _)
  have hMQ' : M * Q = P' * Matrix.diagonal d := by
    rw [hMQ, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    congr 2
    funext j
    rw [hu j, mul_comm]

  have hcard1 : Fintype.card {j // ¬IsUnit (c j)} = Fintype.card {i : Fin n // ¬i.1 < n - k} := by
    rw [Fintype.card_subtype, ← hs, hsk, Fintype.card_subtype_compl, Fintype.card_subtype,
      Fin.card_filter_val_lt, Fintype.card_fin]
    omega
  have hcard0 : Fintype.card {j // IsUnit (c j)} = Fintype.card {i : Fin n // i.1 < n - k} := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (p := fun j => IsUnit (c j))
    rw [Fintype.card_subtype, Fintype.card_subtype, Fin.card_filter_val_lt]
    rw [← hs, hsk, Finset.card_univ, Fintype.card_fin] at h
    omega
  let τ : Equiv.Perm (Fin n) :=
    Equiv.subtypeCongr (Fintype.equivOfCardEq hcard0) (Fintype.equivOfCardEq hcard1)
  have hτ : ∀ j, (τ j).1 < n - k ↔ IsUnit (c j) := by
    intro j
    by_cases h : IsUnit (c j)
    · have e1 : (Equiv.sumCompl fun x => IsUnit (c x)).symm j = Sum.inl ⟨j, h⟩ :=
        Equiv.sumCompl_symm_apply_of_pos (p := fun x => IsUnit (c x)) (a := j) h
      simp only [τ, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCongr_apply, e1, Sum.map_inl,
        Equiv.sumCompl_apply_inl, h, iff_true]
      exact (Fintype.equivOfCardEq hcard0 ⟨j, h⟩).2
    · have e1 : (Equiv.sumCompl fun x => IsUnit (c x)).symm j = Sum.inr ⟨j, h⟩ :=
        Equiv.sumCompl_symm_apply_of_neg (p := fun x => IsUnit (c x)) (a := j) h
      simp only [τ, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCongr_apply, e1, Sum.map_inr,
        Equiv.sumCompl_apply_inr, h, iff_false]
      exact (Fintype.equivOfCardEq hcard1 ⟨j, h⟩).2
  have hsign : ∀ A : Matrix (Fin n) (Fin n) R, IsUnit A.det → IsUnit (A.submatrix id τ.symm).det := by
    intro A hA
    rw [Matrix.det_permute']
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ.symm) with h | h <;> simp [h, hA]
  refine ⟨P'.submatrix id τ.symm, Q.submatrix id τ.symm, hsign P' hP', hsign Q hQ, ?_⟩
  have h1 : M * Q.submatrix id τ.symm = (M * Q).submatrix id τ.symm := by
    ext i j; simp [Matrix.mul_apply]
  rw [h1, hMQ', ← Matrix.submatrix_mul_equiv P' (Matrix.diagonal d) id τ.symm τ.symm,
    Matrix.submatrix_diagonal_equiv]
  congr 2
  funext i
  have := hτ (τ.symm i)
  rw [Equiv.apply_symm_apply] at this
  simp only [Function.comp_apply, d]
  by_cases hi : i.1 < n - k
  · simp [hi, this.1 hi]
  · simp [hi, mt this.2 hi]
end _root_.GlobalTheory.SmithBetween
end GlobalTheory.SmithBetween
