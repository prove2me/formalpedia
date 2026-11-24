-- Prove2me | solution 1 for Kyprianou.Ch02.levyPoissonPathSmallJumpMassMeanBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:11:58.521029+00:00
-- url     : https://prove2.me/submissions/0c320fce-13ab-4d5a-9dd6-6f4c09bc1194

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_Ch02_poissonTruncatedMarkMassMeanV1
import Theorems.Thm_Kyprianou_Ch02_levyPoissonPathActualMassLeRawTruncatedV1
open MeasureTheory ProbabilityTheory Complex Function Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod ν) P)
    (hν : IsLevyMeasure ν) (b : ℝ) :
    ∀ n : ℕ,
      (∫⁻ ω, ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
        ENNReal.ofReal
          (if |(levyJumpPath hd hν b) (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => (levyJumpPath hd hν b) u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |(levyJumpPath hd hν b) (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => (levyJumpPath hd hν b) u ω) (s : ℝ≥0)|
           else 0) ∂P) ≤
        (n : ℝ≥0∞) * (∫⁻ x, ENNReal.ofReal (min (1 : ℝ) |x|) ∂ν) := by
  intro n
  by_cases hfinite : (∫⁻ x, ENNReal.ofReal (min (1 : ℝ) |x|) ∂ν) < ⊤
  · have he := Kyprianou.Ch02.levyPoissonPathActualMassLeRawTruncatedV1
      P ν K Z hd hν b hfinite
    rw [← Kyprianou.Ch02.poissonTruncatedMarkMassMeanV1 P ν K Z hd n]
    apply lintegral_mono_ae
    filter_upwards [he] with ω hω
    exact hω n
  · have htop : (∫⁻ x, ENNReal.ofReal (min (1 : ℝ) |x|) ∂ν) = ⊤ :=
      top_unique (le_of_not_gt hfinite)
    cases n with
    | zero => simp
    | succ n =>
      rw [htop, ENNReal.mul_top]
      · exact le_top
      · exact_mod_cast Nat.succ_ne_zero n
