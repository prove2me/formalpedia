-- Prove2me | solution 1 for Kyprianou.Ch02.levyActualFiniteVariationSignedJumpSeriesV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:04:27.038803+00:00
-- url     : https://prove2.me/submissions/3a3c78df-f62a-41d1-80ad-d2b399b2636f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch02_levyActualCompactJumpAbsoluteSummabilityV1
import Theorems.Thm_Kyprianou_Ch02_levyActualResidualLinearDriftAfterJumpsV1
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Reconstruct the physical signed jump series of the original Levy process
    from absolute jump summability and elimination of the jump-free residual. -/
theorem solution
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) :
    (σ = 0 ∧ Integrable (fun x : ℝ => min (1 : ℝ) |x|) levyMeasure) →
    ∃ (drift : ℝ),
      ∀ᵐ ω ∂P, ∃ (g : ℝ≥0 → ℝ),
        (∀ T : ℝ≥0, Summable (fun s : Set.Ioc (0 : ℝ≥0) T => |g s|)) ∧
        ∀ T : ℝ≥0,
          X T ω = drift * (T : ℝ) +
            ∑' s : Set.Ioc (0 : ℝ≥0) T, g s := by
  intro hfin
  have hsum :=
    Kyprianou.Ch02.levyActualCompactJumpAbsoluteSummabilityV1
      a σ levyMeasure hlevyMeasure P X hX hchar hfin.2
  obtain ⟨drift, hres⟩ :=
    Kyprianou.Ch02.levyActualResidualLinearDriftAfterJumpsV1
      a σ levyMeasure hlevyMeasure P X hX hchar hfin hsum
  refine ⟨drift, ?_⟩
  filter_upwards [hsum, hres] with ω hsω hrω
  let g : ℝ≥0 → ℝ := fun t => X t ω - leftLim (fun s : ℝ≥0 => X s ω) t
  refine ⟨g, ?_, ?_⟩
  · exact hsω
  · exact hrω
