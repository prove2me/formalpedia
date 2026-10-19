-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.affine_normal_forms_of_initial_powers
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T22:24:47.886779+00:00
-- url     : https://prove2.me/submissions/81b51471-d396-4e16-8768-1cabf2dddcff

import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Real.Basic
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_initial_power_normal_form_floor_cost
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_bound_of_floor_cost

open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι] {𝕜 : Type*} [Field 𝕜]
    (I : Ideal (MvPolynomial ι 𝕜))
    (w : ι → ℝ) (ρ : ℝ) (o : MonomialOrder ι)
    (a N : ι → ℕ) (f : ι → MvPolynomial ι 𝕜)
    (hw : ∀ i, 0 ≤ w i) (hρ : 0 ≤ ρ)
    (ha : ∀ i, 0 < a i) (hN : ∀ i, 0 < N i)
    (hmem : ∀ i, f i ∈ I ^ a i)
    (hlc : ∀ i, o.leadingCoeff (f i) = 1)
    (hdeg : ∀ i, o.degree (f i) = Finsupp.single i (N i))
    (hbudget : ∀ i, (N i : ℝ) * w i ≤ (a i : ℝ) * ρ) :
    ∀ k : ℕ, ∀ P : MvPolynomial ι 𝕜,
      ∃ Q : MvPolynomial ι 𝕜,
        (∀ u ∈ Q.support,
          (∑ i, w i * (u i : ℝ)) ≤
            (k : ℝ) * ρ + ∑ i, w i * ((N i - 1 : ℕ) : ℝ)) ∧
        P - Q ∈ I ^ k := by
  intro k P
  obtain ⟨Q, hstair, hmod⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.initial_power_normal_form_floor_cost
      I o a N f ha hN hmem hlc hdeg k P
  refine ⟨Q, ?_, hmod⟩
  intro u hu
  exact OAI.PiExponent.LogarithmicJetIdeals.weighted_bound_of_floor_cost
    w ρ a N hw hρ ha hN hbudget k u (hstair u hu)