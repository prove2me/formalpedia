-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46RestrictedFutureProductLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:34:02.905108+00:00
-- url     : https://prove2.me/submissions/302832eb-d4be-498e-990a-31216d429238

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega E H : Type} [MeasurableSpace Omega] [MeasurableSpace E] [MeasurableSpace H]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (J : Omega → H) (Z Y : Omega → E)
    (hJ : Measurable J) (hZ : AEMeasurable Z P) (hY : Measurable Y)
    (hLaw : ∀ S : Set H, MeasurableSet S →
      (P.restrict (J ⁻¹' S)).map Z = P (J ⁻¹' S) • P.map Y) :
    P.map (fun w => (J w,Z w)) = (P.map J).prod (P.map Y) := by
  symm
  apply Measure.prod_eq
  intro S T hS hT
  rw [Measure.map_apply_of_aemeasurable (hJ.aemeasurable.prodMk hZ) (hS.prod hT),
    Measure.map_apply hJ hS]
  have h := congrArg (fun m : Measure E => m T) (hLaw S hS)
  rw [Measure.map_apply_of_aemeasurable (hZ.mono_measure Measure.restrict_le_self) hT,
    Measure.restrict_apply' (hS.preimage hJ), Measure.smul_apply, smul_eq_mul] at h
  rw [← h, inter_comm]
  rfl
