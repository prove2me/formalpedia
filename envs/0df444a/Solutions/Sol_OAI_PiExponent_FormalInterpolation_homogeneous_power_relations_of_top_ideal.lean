-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.homogeneous_power_relations_of_top_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:13:54.502541+00:00
-- url     : https://prove2.me/submissions/2e8484c2-4a22-4b18-9f43-47c1fa6001cc

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_isWeightedHomogeneous_X_pow
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_homogeneous_span_representation

open scoped BigOperators

theorem solution
    {d k : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (D : Real) (hD : 0 < D)
    (f : Fin k → MvPolynomial (Fin d) Complex)
    (hweight : ∀ j, ∀ a ∈ (f j).support,
      ∑ i, (w i : Real) * (a i : Real) ≤ D)
    (htop : ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
      MvPolynomial.X i ^ e ∈
        Ideal.span (Set.range fun j : Fin k =>
          MvPolynomial.weightedHomogeneousComponent
            (fun i => (w i : Real)) D (f j))) :
    ∃ e : Fin d → Nat, ∀ i, 0 < e i ∧
      ∃ q : Fin k → MvPolynomial (Fin d) Complex,
        (MvPolynomial.X i : MvPolynomial (Fin d) Complex) ^ (e i) =
          ∑ j : Fin k, q j *
            MvPolynomial.weightedHomogeneousComponent
              (fun i => (w i : Real)) D (f j) ∧
        ∀ j, MvPolynomial.IsWeightedHomogeneous
          (fun i => (w i : Real)) (q j) ((e i : Real) * (w i : Real) - D) := by
  classical
  let v : Fin d → Real := fun i => (w i : Real)
  choose e he hmem using htop
  refine ⟨e, ?_⟩
  intro i
  refine ⟨he i, ?_⟩
  let g : Fin k → MvPolynomial (Fin d) Complex := fun j =>
    MvPolynomial.weightedHomogeneousComponent v D (f j)
  have hg : ∀ j, MvPolynomial.IsWeightedHomogeneous v (g j) D := by
    intro j
    exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous D (f j)
  have hp : MvPolynomial.IsWeightedHomogeneous v
      ((MvPolynomial.X i : MvPolynomial (Fin d) Complex) ^ e i)
      ((e i : Real) * v i) := by
    exact OAI.PiExponent.FormalInterpolation.isWeightedHomogeneous_X_pow w i (e i)
  obtain ⟨q, hq, hqhom⟩ :=
    OAI.PiExponent.FormalInterpolation.homogeneous_span_representation
      v D ((e i : Real) * v i) g hg
      ((MvPolynomial.X i : MvPolynomial (Fin d) Complex) ^ e i) hp (hmem i)
  exact ⟨q, hq, hqhom⟩