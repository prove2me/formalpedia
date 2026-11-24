-- Prove2me | solution 1 for Kyprianou.Ch02.bvLevySubordinatorEqJumpSumPlusDriftV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T22:37:52.270365+00:00
-- url     : https://prove2.me/submissions/43ad55ad-712e-4626-a093-0a39e161fb44
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch02_bvLevySubordinatorResidualContinuousLevyV1
import Theorems.Thm_Kyprianou_Ch02_continuousMonotoneLevyIsLinearDriftV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false
set_option linter.unusedVariables false

/-!
Lévy subordinator = jump sum + drift: residual `C = Y - J` is continuous monotone
Lévy (open child), hence linear (open child).
-/

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : ℝ≥0 → Ω → ℝ)
    (hY : ProbabilityTheory.IsLevyProcess Y P)
    (hMono : ∀ᵐ ω ∂P, Monotone (fun t => Y t ω)) :
    ∃ d : ℝ, 0 ≤ d ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Y t ω =
          d * (t : ℝ) +
            ∑' s : Set.Ioc (0 : ℝ≥0) t,
              max (Y s.1 ω -
                Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => Y u ω)) 0 := by
  let J : ℝ≥0 → Ω → ℝ := fun t ω =>
    ∑' s : Set.Ioc (0 : ℝ≥0) t,
      max (Y s.1 ω -
        Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => Y u ω)) 0
  let C : ℝ≥0 → Ω → ℝ := fun t ω => Y t ω - J t ω
  obtain ⟨hClevy, hCcont, hCmono, hYeq⟩ :=
    Kyprianou.Ch02.bvLevySubordinatorResidualContinuousLevyV1 P Y hY hMono
  refine Exists.elim
    (Kyprianou.Ch02.continuousMonotoneLevyIsLinearDriftV1 P C hClevy hCmono hCcont)
    fun d hd => ?_
  rcases hd with ⟨hd0, hlin⟩
  refine ⟨d, hd0, ?_⟩
  filter_upwards [hlin, hYeq] with ω hlinω hYω
  intro t
  have h1 := hYω t
  have h2 := hlinω t
  -- h1 : Y = C + J; h2 : C = d·t
  calc
    Y t ω = C t ω + J t ω := h1
    _ = d * (t : ℝ) + J t ω := by rw [h2]
