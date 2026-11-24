-- Prove2me | solution 1 for Kyprianou.Ch02.levyActualIntegerSmallJumpMassFiniteV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:59:01.274923+00:00
-- url     : https://prove2.me/submissions/5ebca959-563b-4693-bc7f-ef46fc5b1121
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch02_levyPhysicalSmallJumpCampbellBoundV1
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
    ∀ n : ℕ,
      AEMeasurable (fun ω => ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
           ENNReal.ofReal (if |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|
           else 0)) P ∧
      (∫⁻ ω, ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
        ENNReal.ofReal (if |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|
           else 0) ∂P) < ⊤ := by
  intro hfirst n
  have hphysical := Kyprianou.Ch02.levyPhysicalSmallJumpCampbellBoundV1
    a σ levyMeasure hlevyMeasure P X hX hchar n
  refine ⟨hphysical.1, lt_of_le_of_lt hphysical.2 ?_⟩
  have hpos (x : ℝ) : 0 ≤ min (1 : ℝ) |x| :=
    le_min (by norm_num) (abs_nonneg x)
  have hmass :
      (∫⁻ x, ENNReal.ofReal (min (1 : ℝ) |x|) ∂levyMeasure) < ⊤ := by
    simpa only [Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (hpos _)] using hfirst.lintegral_lt_top
  exact ENNReal.mul_lt_top (by simp) hmass
