-- Prove2me | solution 1 for Kyprianou.Ch02.finiteRegionPRMFiniteSupportAllNaturalWindowsV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T10:42:38.96329+00:00
-- url     : https://prove2.me/submissions/8814cb88-dac7-481d-b62a-490907b9a111

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_integerValuedFiniteSupportV1
import Theorems.Thm_Kyprianou_Ch02_finiteRegionPRMIntegerValuedAllNaturalWindowsV2
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ s : Finset (ℝ × ℝ),
      N.N ω ((Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) \ (s : Set (ℝ × ℝ))) = 0 := by
  filter_upwards
    [Kyprianou.Ch02.finiteRegionPRMIntegerValuedAllNaturalWindowsV2
      P ν N B hB hfinite] with ω hω
  intro T
  let R : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B
  obtain ⟨s, hs⟩ :=
    Kyprianou.Ch02.integerValuedFiniteSupportV1
      ((N.N ω).restrict R) (hω T)
  refine ⟨s, ?_⟩
  have hz : (N.N ω).restrict R (s : Set (ℝ × ℝ))ᶜ = 0 :=
    MeasureTheory.ae_iff.mp hs
  rw [Measure.restrict_apply (s.measurableSet.compl)] at hz
  have hset :
      R \ (s : Set (ℝ × ℝ)) =
        (s : Set (ℝ × ℝ))ᶜ ∩ R := by
    ext p
    simp [Set.diff_eq, Set.inter_comm]
  change N.N ω (R \ (s : Set (ℝ × ℝ))) = 0
  rw [hset]
  exact hz
