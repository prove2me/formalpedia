-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.pure_leading_powers_of_bounded_representatives
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T23:03:59.134783+00:00
-- url     : https://prove2.me/submissions/dd94fdce-6970-42cc-aa85-8de20865997f

import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_rounded_positive_exponent
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_dominating_monomialOrder
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_extract_pure_leading_relations

open scoped BigOperators

theorem solution
    (m : ℕ) (w : Fin (m + 1) → ℝ) (hw : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) ℂ))
    (D : ℝ) (hD : 0 ≤ D)
    (hrep : ∀ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∃ Q : MvPolynomial (Fin (m + 1)) ℂ,
        P - Q ∈ I ∧
        ∀ b ∈ Q.support, ∑ i, w i * (b i : ℝ) ≤ D) :
    ∃ (N : Fin (m + 1) → ℕ)
      (o : MonomialOrder (Fin (m + 1)))
      (f : Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ),
      (∀ i, 0 < N i) ∧
      (∀ i, f i ∈ I) ∧
      (∀ i, o.leadingCoeff (f i) = 1) ∧
      (∀ i, o.degree (f i) = Finsupp.single i (N i)) ∧
      (∀ i, (N i : ℝ) * w i ≤ D + w i) := by
  have hround :=
    OAI.PiExponent.LogarithmicJetIdeals.rounded_positive_exponent m w hw D hD
  let N : Fin (m + 1) → ℕ := fun i => Classical.choose (hround i)
  have hNpos : ∀ i, 0 < N i := by
    intro i
    exact (Classical.choose_spec (hround i)).1
  have hNgt : ∀ i, D < (N i : ℝ) * w i := by
    intro i
    exact (Classical.choose_spec (hround i)).2.1
  have hNle : ∀ i, (N i : ℝ) * w i ≤ D + w i := by
    intro i
    exact (Classical.choose_spec (hround i)).2.2
  obtain ⟨o, ho⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.weighted_dominating_monomialOrder
      m w hw D N hNgt
  obtain ⟨f, hfI, hcoeff, hdegree⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.extract_pure_leading_relations
      m w D I N o hNgt ho hrep
  exact ⟨N, o, f, hNpos, hfI, hcoeff, hdegree, hNle⟩
