-- Prove2me | solution 1 for NechitaRDM.MP.eq_24
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T19:58:50.674771+00:00
-- url     : https://prove2.me/submissions/a714d6e4-12d3-4ed0-bb17-63ec17c00c20

import Mathlib
import Definitions.Def_NechitaRDM_MP_Basic

open NechitaRDM.MP Polynomial

theorem charpoly_smul_aux {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (hc : c ≠ 0) :
    (c • A).charpoly = A.charpoly.scaleRoots c := by
  apply Polynomial.funext
  intro y
  have hy : y = c * (c⁻¹ * y) := by field_simp
  rw [hy, Polynomial.scaleRoots_eval_mul, Matrix.eval_charpoly, Matrix.eval_charpoly,
    Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have : Matrix.scalar (Fin n) (c * (c⁻¹ * y)) - c • A =
      c • (Matrix.scalar (Fin n) (c⁻¹ * y) - A) := by
    rw [smul_sub]; congr 1
    ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply]
  rw [this, Matrix.det_smul, Fintype.card_fin]

theorem solution {n k : ℕ} (X : Matrix (Fin n) (Fin k) ℂ) :
    eigs ((wishart X).trace⁻¹ • wishart X) =
      (eigs (wishart X)).map (fun x => x / (eigs (wishart X)).sum) := by
  set W := wishart X with hW
  set t : ℝ := ∑ p : Fin n × Fin k, ‖X p.1 p.2‖ ^ 2 with ht
  have htr : (t : ℂ) = W.trace := by
    simp only [ht, hW, wishart, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    rw [Fintype.sum_prod_type]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  have hre : ∀ s : Multiset ℂ, (s.map Complex.re).sum = (s.sum).re := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih => simp [ih]
  have hsum : (eigs W).sum = t := by
    simp only [eigs]
    rw [hre, ← Matrix.trace_eq_sum_roots_charpoly, ← htr, Complex.ofReal_re]
  by_cases h0 : t = 0
  · have hc : W.trace⁻¹ = 0 := by rw [← htr, h0]; simp
    rw [hc, zero_smul, hsum, h0]
    simp only [div_zero, Multiset.map_const']
    simp only [eigs, Matrix.charpoly_zero, Polynomial.roots_X_pow, Fintype.card_fin,
      Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim,
      Multiset.nsmul_singleton, Multiset.map_replicate, Complex.zero_re]
  · have hc : W.trace⁻¹ = ((t⁻¹ : ℝ) : ℂ) := by rw [← htr]; push_cast; rfl
    have hc0 : ((t⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast inv_ne_zero h0
    rw [hc, hsum]
    simp only [eigs]
    rw [charpoly_smul_aux _ _ hc0, Polynomial.roots_scaleRoots _ (isUnit_iff_ne_zero.mpr hc0),
      Multiset.map_map, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro z _
    simp only [Function.comp, Complex.re_ofReal_mul]
    rw [div_eq_inv_mul]
