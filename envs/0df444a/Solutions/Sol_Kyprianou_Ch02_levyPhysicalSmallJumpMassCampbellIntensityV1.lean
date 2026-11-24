-- Prove2me | solution 1 for Kyprianou.Ch02.levyPhysicalSmallJumpMassCampbellIntensityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:53:32.201153+00:00
-- url     : https://prove2.me/submissions/a456c5c7-01dd-4553-8ed8-cee226df2385

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_levyCanonicalSmallJumpMassModelV1
import Theorems.Thm_Kyprianou_Ch02_levyWholePathLawEqOfCharFunV1
import Theorems.Thm_Kyprianou_Ch02_levySmallJumpMassLIntegralEqOfPathLawV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false


/-- Source-faithful Chapter 2 proof. -/
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
    ∀ n : ℕ,
      (∫⁻ ω, ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
        ENNReal.ofReal
          (if |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|
           else 0) ∂P) ≤
          (n : ℝ≥0∞) * (∫⁻ x, ENNReal.ofReal (min (1 : ℝ) |x|) ∂levyMeasure) := by
  obtain ⟨Λ, mΛ, Q, Y, hQ, hY, hcharY, hbound⟩ :=
    Kyprianou.Ch02.levyCanonicalSmallJumpMassModelV1 a σ levyMeasure hlevyMeasure
  letI : MeasurableSpace Λ := mΛ
  letI : IsProbabilityMeasure Q := hQ
  have hpath := Kyprianou.Ch02.levyWholePathLawEqOfCharFunV1 P Q X Y hX hY
    (fun t ξ => (hchar t ξ).trans (hcharY t ξ).symm)
  intro n
  rw [Kyprianou.Ch02.levySmallJumpMassLIntegralEqOfPathLawV1 P Q X Y hX hY
    hpath (n : ℝ≥0)]
  exact hbound n
