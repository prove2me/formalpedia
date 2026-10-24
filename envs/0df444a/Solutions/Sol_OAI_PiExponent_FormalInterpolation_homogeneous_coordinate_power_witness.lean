-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.homogeneous_coordinate_power_witness
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:00:42.69438+00:00
-- url     : https://prove2.me/submissions/0f379574-36d4-476c-9b08-d825543d8165

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_homogeneous_mem_span_coefficients

open scoped BigOperators

theorem solution
    {d k : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (D : Real) (hD : 0 < D) (g : Fin k → MvPolynomial (Fin d) Complex)
    (hhom : ∀ j, (g j).IsWeightedHomogeneous (fun i => (w i : Real)) D)
    (J : Ideal (MvPolynomial (Fin d) Complex))
    (hspan : Ideal.span (Set.range g) = J)
    (hpowers : ∀ i, ∃ n : Nat, 0 < n ∧
      (MvPolynomial.X i : MvPolynomial (Fin d) Complex) ^ n ∈ J) :
    ∃ n : Fin d → Nat, (∀ i, 0 < n i) ∧
      ∃ c : Fin d → Fin k → MvPolynomial (Fin d) Complex,
        (∀ i, (MvPolynomial.X i : MvPolynomial (Fin d) Complex) ^ n i =
          ∑ j : Fin k, c i j * g j) ∧
        (∀ i j, (c i j).IsWeightedHomogeneous (fun l => (w l : Real))
          ((n i : Real) * (w i : Real) - D)) := by
  classical
  choose n hn hmem using hpowers
  refine ⟨n, hn, ?_⟩
  choose c hrepr hcoeff using fun i =>
    OAI.PiExponent.FormalInterpolation.homogeneous_mem_span_coefficients
      w hw D hD g hhom J hspan i (n i) (hn i) (hmem i)
  refine ⟨c, ?_, ?_⟩
  · intro i
    exact hrepr i
  · intro i j
    exact hcoeff i j