-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46RegenerativePhysicalTailTransferV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:27:24.235744+00:00
-- url     : https://prove2.me/submissions/03a1ed64-0da6-40c5-957f-22189812cac8

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46RegenerativeCountTransferV1
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false
theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (S : Omega → Set NNReal)
    (D : Set Omega) (hD : MeasurableSet D)
    (Y Z : Omega → E) (hY : Measurable Y)
    (hZ : AEMeasurable Z (P.restrict D))
    (C : E → ENNReal) (hC : Measurable C)
    (q : Real) (hq : (P D).toReal = q)
    (hLaw : (P.restrict D).map Z = P D • P.map Y)
    (hCard : ∀ᵐ w ∂P, C (Y w) = ((S w).encard : ENNReal))
    (hSplit : ∀ᵐ w ∂P,
      (w ∈ D → C (Y w) = 1 + C (Z w)) ∧
      (w ∉ D → C (Y w) = 1)) :
    ∀ k : Nat,
      (P {w | ((k+1+1 : Nat) : ENat) ≤ (S w).encard}).toReal =
      q * (P {w | ((k+1 : Nat) : ENat) ≤ (S w).encard}).toReal := by
  have ht := Kyprianou.Ch04.exercise46RegenerativeCountTransferV1
    P D hD Y Z hY hZ C hC hLaw hSplit
  have he (n : Nat) :
      {w | (n : ENNReal) ≤ C (Y w)} =ᵐ[P]
        {w | (n : ENat) ≤ (S w).encard} := by
    filter_upwards [hCard] with w hw
    change ((n : ENNReal) ≤ C (Y w)) = ((n : ENat) ≤ (S w).encard)
    rw [hw]
    change (((n : ENat) : ENNReal) ≤ ((S w).encard : ENNReal)) = _
    rw [ENat.toENNReal_le]
  intro k
  have hk := ht k
  rw [measure_congr (he (k+1+1)), measure_congr (he (k+1)), hq] at hk
  exact hk
