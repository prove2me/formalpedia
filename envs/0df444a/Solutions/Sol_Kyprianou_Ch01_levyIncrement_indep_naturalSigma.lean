-- Prove2me | solution 1 for Kyprianou.Ch01.levyIncrement_indep_naturalSigma
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:22:10.163883+00:00
-- url     : https://prove2.me/submissions/6dc4a818-eaaf-4bd7-b3df-ae51d349e3bc

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_ProbabilityTheory_HasIndependentIncrements_indep_naturalFiltration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hmeas : ∀ t : ℝ≥0, Measurable (X t))
    (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap
        (fun ω : Ω => X t ω - X s ω) inferInstance)
      (naturalSigma X s) P := by
  have hs : ∀ u : ℝ≥0, StronglyMeasurable (X u) :=
    fun u => (hmeas u).stronglyMeasurable
  have hind := hX.indep_increments.indep_naturalFiltration
    hs hX.start_zero (fun _ => zero_le) hst
  exact hind
