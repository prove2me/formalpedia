-- Prove2me | solution 1 for NonuniformKuramoto.CondII.eq_39
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:06:44.021332+00:00
-- url     : https://prove2.me/submissions/dbf86be6-6994-471e-9559-4d107a12db39

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondII_Graph
import Definitions.Def_NonuniformKuramoto_CondII_Model
import Definitions.Def_NonuniformKuramoto_CondII_Constants
set_option autoImplicit false
open Matrix NonuniformKuramoto.CondII

theorem solution {n : ℕ} (D : Fin n → ℝ) (hn : 2 ≤ n) (hD : ∀ i, 0 < D i) (θ : Fin n → ℝ) :
    minDD D * normH θ ^ 2 ≤ 2 * W D θ ∧ 2 * W D θ ≤ maxDD D * normH θ ^ 2 := by
  have hvp : ∀ p : Pairs n, (incH n *ᵥ θ) p = θ p.1.2 - θ p.1.1 := by
    intro p
    have hne : p.1.1 ≠ p.1.2 := ne_of_lt p.2
    have h1 : ∀ k, incH n p k * θ k = (if k = p.1.2 then θ k else 0) - (if k = p.1.1 then θ k else 0) := by
      intro k
      unfold incH
      by_cases h2 : k = p.1.2
      · subst h2; simp [hne.symm]
      · by_cases h3 : k = p.1.1
        · subst h3; simp [h2]
        · simp [h2, h3]
    simp only [Matrix.mulVec, dotProduct, h1, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hT : normH θ ^ 2 = ∑ p : Pairs n, (θ p.1.2 - θ p.1.1) ^ 2 := by
    unfold normH euclNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    simp only [hvp]
  have hW : 2 * W D θ = ∑ p : Pairs n, D p.1.1 * D p.1.2 * (θ p.1.2 - θ p.1.1) ^ 2 := by
    unfold W
    simp only [Matrix.mulVec_diagonal, dotProduct, pairDD, hvp]
    rw [show ∀ s : ℝ, 2 * (1/2 * s) = s from fun s => by ring]
    apply Finset.sum_congr rfl; intro p _; ring
  have hlo : ∀ p : Pairs n, minDD D ≤ D p.1.1 * D p.1.2 := by
    intro p
    unfold minDD
    exact ciInf_le (f := fun q : {p : Fin n × Fin n // p.1 ≠ p.2} => D q.1.1 * D q.1.2) (Set.finite_range _).bddBelow (⟨p.1, ne_of_lt p.2⟩ : {p : Fin n × Fin n // p.1 ≠ p.2})
  have hhi : ∀ p : Pairs n, D p.1.1 * D p.1.2 ≤ maxDD D := by
    intro p
    unfold maxDD
    exact le_ciSup (f := fun q : {p : Fin n × Fin n // p.1 ≠ p.2} => D q.1.1 * D q.1.2) (Set.finite_range _).bddAbove (⟨p.1, ne_of_lt p.2⟩ : {p : Fin n × Fin n // p.1 ≠ p.2})
  rw [hT, hW, Finset.mul_sum, Finset.mul_sum]
  constructor
  · apply Finset.sum_le_sum; intro p _
    exact mul_le_mul_of_nonneg_right (hlo p) (sq_nonneg _)
  · apply Finset.sum_le_sum; intro p _
    exact mul_le_mul_of_nonneg_right (hhi p) (sq_nonneg _)
