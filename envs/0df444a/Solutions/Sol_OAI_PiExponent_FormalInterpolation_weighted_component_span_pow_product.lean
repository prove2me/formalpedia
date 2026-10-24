-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_component_span_pow_product
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:44:05.854517+00:00
-- url     : https://prove2.me/submissions/34b7feed-d64c-4b4f-8435-8eedf8b2798e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_component_product_eq_component
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_support_product_le
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_ideal_pow_product_mem
open scoped BigOperators

theorem solution {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex)) (w : Fin d → Rat) (s m : Nat) (q D : Rat) (hs : 0 < s) (hD : q * (m : Rat) = D) (u : Fin m → {g : MvPolynomial (Fin d) Complex // g ∈ I ^ s ∧ ∀ a ∈ g.support, ∑ j, (w j : Real) * (a j : Real) ≤ (q : Real)}) :
    (∏ i, MvPolynomial.weightedHomogeneousComponent (fun j => (w j : ℚ)) q (u i).1) ∈ Ideal.span {h : MvPolynomial (Fin d) Complex | ∃ g : MvPolynomial (Fin d) Complex, g ∈ I ^ (s * m) ∧ (∀ a ∈ g.support, ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧ h = MvPolynomial.weightedHomogeneousComponent (fun k => (w k : ℚ)) D g} := by
  classical
  let g : MvPolynomial (Fin d) Complex := ∏ i, (u i).1
  have hgI : g ∈ I ^ (s * m) := by
    apply OAI.PiExponent.FormalInterpolation.ideal_pow_product_mem I s m (fun i => (u i).1)
    intro i
    exact (u i).2.1
  have hgSupport : ∀ a ∈ g.support, ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real) := by
    have hbound := OAI.PiExponent.FormalInterpolation.weighted_support_product_le w q m (fun i => (u i).1) (by
      intro i a ha
      exact (u i).2.2 a ha)
    simpa [g, hD] using hbound
  have hcomponent :
      (∏ i, MvPolynomial.weightedHomogeneousComponent (fun j => (w j : ℚ)) q (u i).1) =
        MvPolynomial.weightedHomogeneousComponent (fun j => (w j : ℚ)) D g := by
    simpa [g] using OAI.PiExponent.FormalInterpolation.weighted_component_product_eq_component w q D m hD (fun i => (u i).1)
  rw [hcomponent]
  apply Ideal.subset_span
  exact ⟨g, hgI, hgSupport, rfl⟩