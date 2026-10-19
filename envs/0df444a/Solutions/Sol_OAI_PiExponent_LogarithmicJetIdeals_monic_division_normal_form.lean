-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.monic_division_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:44:10.32399+00:00
-- url     : https://prove2.me/submissions/4a3d41a9-6ccf-490a-a828-f1c1227d2dcb

import Mathlib
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Real.Basic

open scoped BigOperators


theorem solution
    {ι : Type*} [Fintype ι] {𝕜 : Type*} [Field 𝕜]
    (o : MonomialOrder ι)
    (S : Finset (MvPolynomial ι 𝕜))
    (P : MvPolynomial ι 𝕜)
    (hmonic : ∀ g ∈ S, o.leadingCoeff g = 1) :
    ∃ Q : MvPolynomial ι 𝕜,
      (∀ u ∈ Q.support, ∀ g ∈ S, ¬ (o.degree g ≤ u)) ∧
      P - Q ∈ Ideal.span (↑S : Set (MvPolynomial ι 𝕜)) := by
  classical
  obtain ⟨g, r, hfr, -, hr⟩ := o.div_set (B := (↑S : Set (MvPolynomial ι 𝕜)))
    (fun b hb => by rw [hmonic b hb]; exact isUnit_one) P
  refine ⟨r, fun u hu g' hg' => hr u hu g' hg', ?_⟩
  have : P - r = Finsupp.linearCombination _ (fun (b : (↑S : Set (MvPolynomial ι 𝕜))) ↦
      (b : MvPolynomial ι 𝕜)) g := by
    rw [hfr]; ring
  rw [this, Finsupp.linearCombination_apply]
  apply Ideal.sum_mem
  intro q _
  show g q • (q : MvPolynomial ι 𝕜) ∈ _
  rw [smul_eq_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span q.2)

