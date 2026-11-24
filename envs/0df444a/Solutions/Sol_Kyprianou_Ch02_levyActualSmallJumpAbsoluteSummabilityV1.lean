-- Prove2me | solution 1 for Kyprianou.Ch02.levyActualSmallJumpAbsoluteSummabilityV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:03:37.178005+00:00
-- url     : https://prove2.me/submissions/9e4b0a9f-f6d0-4959-83c0-19efcd1ea4ce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch02_levyActualIntegerSmallJumpMassFiniteV1
import Theorems.Thm_Kyprianou_Ch02_aeSummableFiniteClockOfIntegerJumpMassV1
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false

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
        if |X (s : ℝ≥0) ω - Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| ≤ (1 : ℝ) then |X (s : ℝ≥0) ω - Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| else 0) := by
  intro hfirst
  let w : ℝ≥0 → Ω → ℝ := fun t ω =>
    if |X t ω - Function.leftLim (fun u : ℝ≥0 => X u ω) t| ≤ (1 : ℝ)
      then |X t ω - Function.leftLim (fun u : ℝ≥0 => X u ω) t|
      else 0
  have hw : ∀ t ω, 0 ≤ w t ω := by
    intro t ω
    dsimp [w]
    split_ifs <;> positivity
  have hm (n : ℕ) :
      AEMeasurable (fun ω => ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
        ENNReal.ofReal (w (s : ℝ≥0) ω)) P ∧
      (∫⁻ ω, ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
        ENNReal.ofReal (w (s : ℝ≥0) ω) ∂P) < ⊤ := by
    simpa only [w] using
      (Kyprianou.Ch02.levyActualIntegerSmallJumpMassFiniteV1
        a σ levyMeasure hlevyMeasure P X hX hchar hfirst n)
  change ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
    Summable (fun s : Set.Ioc (0 : ℝ≥0) T => w (s : ℝ≥0) ω)
  exact Kyprianou.Ch02.aeSummableFiniteClockOfIntegerJumpMassV1 P w hw hm
