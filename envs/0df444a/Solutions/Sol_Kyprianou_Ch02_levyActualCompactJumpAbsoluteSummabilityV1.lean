-- Prove2me | solution 1 for Kyprianou.Ch02.levyActualCompactJumpAbsoluteSummabilityV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:11:40.075444+00:00
-- url     : https://prove2.me/submissions/a1db202e-bdaa-4ad5-b7c3-5c2fa97cc415
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch02_levyActualSmallJumpAbsoluteSummabilityV1
import Theorems.Thm_Kyprianou_Ch02_levyActualLargeJumpAbsoluteSummabilityV1
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The full physical absolute jump sum is the disjoint sum of small and
large jumps. Finite-horizon large jumps need no first-moment condition. -/
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
    Integrable (fun x : ℝ => min (1 : ℝ) |x|) levyMeasure →
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Summable (fun s : Set.Ioc (0 : ℝ≥0) T =>
        |X (s : ℝ≥0) ω - leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|) := by
  intro hfirst
  have hsmall :=
    Kyprianou.Ch02.levyActualSmallJumpAbsoluteSummabilityV1
      a σ levyMeasure hlevyMeasure P X hX hchar hfirst
  have hlarge :=
    Kyprianou.Ch02.levyActualLargeJumpAbsoluteSummabilityV1
      a σ levyMeasure hlevyMeasure P X hX hchar
  filter_upwards [hsmall, hlarge] with ω hsω hlω
  intro T
  let v : Set.Ioc (0 : ℝ≥0) T → ℝ := fun s =>
    |X (s : ℝ≥0) ω - Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|
  have hsm : Summable (fun s : Set.Ioc (0 : ℝ≥0) T =>
      if v s ≤ (1 : ℝ) then v s else 0) := hsω T
  have hlg : Summable (fun s : Set.Ioc (0 : ℝ≥0) T =>
      if (1 : ℝ) < v s then v s else 0) := hlω T
  have heq : (fun s : Set.Ioc (0 : ℝ≥0) T => v s) =
      (fun s => (if v s ≤ (1 : ℝ) then v s else 0) +
        (if (1 : ℝ) < v s then v s else 0)) := by
    funext s
    by_cases hv : v s ≤ (1 : ℝ)
    · simp [hv, not_lt.mpr hv]
    · have hv' : (1 : ℝ) < v s := lt_of_not_ge hv
      simp [hv, hv']
  change Summable (fun s : Set.Ioc (0 : ℝ≥0) T => v s)
  rw [heq]
  exact hsm.add hlg
