-- Prove2me | solution 1 for KingDiagonal.eq_12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:55:47.1607+00:00
-- url     : https://prove2.me/submissions/2d0fb659-bfb1-4547-b8c8-3b6c6afc637c

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_KingDiagonal_weightMatrix
import Definitions.Def_KingDiagonal_tau

open QAlgorithms
open scoped Matrix Kronecker

namespace Aux_King_eq12
open Matrix ComplexOrder

lemma psd_row_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (hA : A.PosSemidef)
    (p q : ι) (hp : A p p = 0) : A p q = 0 := by
  by_cases hpq : p = q
  · subst hpq; exact hp
  have hsub := hA.submatrix ![p, q]
  have hdet := hsub.det_nonneg
  rw [Matrix.det_fin_two] at hdet
  simp only [submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hdet
  rw [hp, zero_mul, zero_sub] at hdet
  have hherm : A q p = star (A p q) := (hA.1.apply q p).symm
  rw [hherm] at hdet
  have h2 : A p q * star (A p q) = ((Complex.normSq (A p q) : ℝ) : ℂ) := Complex.mul_conj _
  rw [h2] at hdet
  have h3 : (Complex.normSq (A p q) : ℝ) ≤ 0 := by
    have h5 := (Complex.nonneg_iff.1 hdet).1
    have h6 : (-((Complex.normSq (A p q) : ℝ) : ℂ)).re = -Complex.normSq (A p q) := by simp
    rw [h6] at h5
    linarith
  have h4 : Complex.normSq (A p q) = 0 := le_antisymm h3 (Complex.normSq_nonneg _)
  exact Complex.normSq_eq_zero.1 h4

end Aux_King_eq12

open KingDiagonal Aux_King_eq12 ComplexOrder Matrix in
theorem solution {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    (ρ : Matrix (n × k) (n × k) ℂ) (hρ : IsDensityMatrix ρ) :
    ρ = (weightMatrix ρ ⊗ₖ (Matrix.of fun _ _ => (1 : ℂ) : Matrix k k ℂ)) ⊙ tau ρ := by
  have hpsd := hρ.1
  have hdiag : ∀ p, 0 ≤ (ρ p p).re ∧ (ρ p p).im = 0 := by
    intro p
    have := hpsd.diag_nonneg (i := p)
    exact ⟨(Complex.nonneg_iff.1 this).1, (Complex.nonneg_iff.1 this).2.symm⟩
  have halpha : ∀ i, 0 ≤ alpha ρ i := by
    intro i; unfold alpha
    rw [Complex.re_sum]
    exact Finset.sum_nonneg (fun a _ => (hdiag (i, a)).1)
  have hzero : ∀ i, alpha ρ i = 0 → ∀ a q, ρ (i, a) q = 0 := by
    intro i hi a q
    apply psd_row_zero ρ hpsd
    unfold alpha at hi
    rw [Complex.re_sum] at hi
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => (hdiag (i, a)).1)).1 hi a
      (Finset.mem_univ a)
    exact Complex.ext h (hdiag (i, a)).2
  have hzero' : ∀ j, alpha ρ j = 0 → ∀ b p, ρ p (j, b) = 0 := by
    intro j hj b p
    have h1 := hzero j hj b p
    have := hpsd.1.apply p (j, b)
    rw [← this, h1, star_zero]
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [hadamard_apply, kroneckerMap_apply, weightMatrix, tau, of_apply, mul_one]
  by_cases hs : Real.sqrt (alpha ρ i * alpha ρ j) = 0
  · rw [hs]
    have : alpha ρ i * alpha ρ j = 0 := by
      have h0 := mul_nonneg (halpha i) (halpha j)
      rw [Real.sqrt_eq_zero h0] at hs; exact hs
    rcases mul_eq_zero.1 this with h | h
    · rw [hzero i h a (j, b)]; simp
    · rw [hzero' j h b (i, a)]; simp
  · rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hs, Complex.ofReal_one, one_mul]
