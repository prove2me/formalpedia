-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46IndependentPairFromRestrictedLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:27:50.822868+00:00
-- url     : https://prove2.me/submissions/decaf28c-8fc4-4847-98e8-231b68d2c305

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega E F : Type} [MeasurableSpace Omega] [MeasurableSpace E] [MeasurableSpace F]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (J : Omega → E) (Z Y : Omega → F)
    (hJ : Measurable J) (hZ : AEMeasurable Z P) (hY : Measurable Y)
    (hLaw : ∀ B : Set E, MeasurableSet B →
      (P.restrict (J ⁻¹' B)).map Z = P (J ⁻¹' B) • P.map Y) :
    P.map (fun w => (J w, Z w)) = (P.map J).prod (P.map Y) := by
  letI : IsProbabilityMeasure (P.map J) :=
    Measure.isProbabilityMeasure_map hJ.aemeasurable
  letI : IsProbabilityMeasure (P.map Y) :=
    Measure.isProbabilityMeasure_map hY.aemeasurable
  symm
  apply Measure.prod_eq
  intro B C hB hC
  rw [Measure.map_apply_of_aemeasurable (hJ.aemeasurable.prodMk hZ) (hB.prod hC)]
  change P (J ⁻¹' B ∩ Z ⁻¹' C) = _
  rw [inter_comm, ← Measure.restrict_apply₀' (hJ hB).nullMeasurableSet,
    ← Measure.map_apply_of_aemeasurable (hZ.mono_measure Measure.restrict_le_self) hC,
    hLaw B hB, Measure.smul_apply, smul_eq_mul, Measure.map_apply hJ hB]
