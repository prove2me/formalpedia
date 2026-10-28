-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.scaledProduct_coordinate_generation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T18:17:20.285834+00:00
-- url     : https://prove2.me/submissions/a7d87f5d-f73b-4f00-9f69-3c91f0376905

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_scaledProduct_component_identity
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_ideal_power_products
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → Rat) (D : Real) (k : Nat) (hk : 0 < k)
    (n : Nat) (f : Fin n → MvPolynomial (Fin d) Complex)
    (hweight : ∀ j, ∀ a ∈ (f j).support,
      ∑ l, (w l : Real) * (a l : Real) ≤ D)
    (hgen : ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
      MvPolynomial.X i ^ e ∈ Ideal.span (Set.range (fun j =>
        MvPolynomial.weightedHomogeneousComponent
          (fun l => (w l : Real)) D (f j))))
    (N : Nat) (eFin : Fin N ≃ (Fin k → Fin n)) :
    ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
      MvPolynomial.X i ^ e ∈ Ideal.span (Set.range (fun j : Fin N =>
        MvPolynomial.weightedHomogeneousComponent
          (fun l => (w l : Real)) ((k : Real) * D)
          (∏ t : Fin k, f (eFin j t)))) := by
  intro i
  rcases hgen i with ⟨e, he, hmem⟩
  let g : Fin n → MvPolynomial (Fin d) Complex := fun j =>
    MvPolynomial.weightedHomogeneousComponent (fun l => (w l : Real)) D (f j)
  let p : Fin N → MvPolynomial (Fin d) Complex := fun j =>
    MvPolynomial.weightedHomogeneousComponent (fun l => (w l : Real)) ((k : Real) * D)
      (∏ t : Fin k, f (eFin j t))
  have hcomponents : ∀ j : Fin N, p j = ∏ t : Fin k, g (eFin j t) := by
    intro j
    exact OAI.PiExponent.FormalInterpolation.scaledProduct_component_identity
      w D k n f hweight N eFin j
  have hpow := OAI.PiExponent.FormalInterpolation.ideal_power_products
    g p e k (MvPolynomial.X i) hmem eFin hcomponents
  refine ⟨e * k, Nat.mul_pos he hk, ?_⟩
  change MvPolynomial.X i ^ (e * k) ∈ Ideal.span (Set.range p)
  exact hpow