-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49AdmissibleUniformModelV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:15:51.155818+00:00
-- url     : https://prove2.me/submissions/b43363b2-a3e6-4174-86b2-a33433154f2c

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49UniformDriverCountBoundV5
import Theorems.Thm_Kyprianou_Ch04_exercise49GatedDriftModelV5
import Theorems.Thm_Kyprianou_Ch04_exercise49UniformTripletDataV5
import Theorems.Thm_Kyprianou_Ch04_exercise49RawCompoundDownJumpV5
import Theorems.Thm_Kyprianou_Ch04_exercise49RawCompoundGrowthV5
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_driver_on_real_sequence_product
import Theorems.Thm_levy_foundations_compoundPoissonCharFun
import Definitions.Def_Kyprianou_Ch04_Exercise4_9Certification
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_compoundPoissonTripleGivenLevyMeasure
import Definitions.Def_levy_foundations_exponent
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch04 AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) (X : NNReal → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
      (T : ProbabilityTheory.LevyKhintchineTriple) (b : ℝ),
      IsProbabilityMeasure P ∧ IsLevyProcess X P ∧
      (∀ t : NNReal, ∀ ξ : ℝ, charFun (P.map (X t)) ξ =
        Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent T ξ)) ∧
      (T.gaussianVariance = 0 ∧
        (∫⁻ y in Ioo (-1 : ℝ) 1, ENNReal.ofReal |y| ∂T.levyMeasure) < ⊤) ∧
      b = T.drift - ∫ y in Ioo (-1 : ℝ) 1, y ∂T.levyMeasure ∧
      0 < b ∧ ¬ (∀ᵐ w ∂P, Monotone (fun t : NNReal => X t w)) ∧
      ∀ᵐ w ∂P, Tendsto (fun t : NNReal => X t w) atTop atTop := by
  obtain ⟨P,τ,Y,hP,h⟩ := avram_a06_uniform_driver_on_real_sequence_product
  letI : IsProbabilityMeasure P := hP
  obtain ⟨c,hc,hCount⟩ := exercise49UniformDriverCountBoundV5 P τ Y h
  let b : ℝ := 1 + 1/c
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨X,hX,hEq⟩ := exercise49GatedDriftModelV5 P τ Y h b
  obtain ⟨T,hBV,hDrift,hExp⟩ := exercise49UniformTripletDataV5 b
  refine ⟨P,X,T,b,hP,hX,?_,hBV,hDrift,hb,?_,?_⟩
  · intro t ξ
    rw [Measure.map_congr (hEq.mono fun w hw => hw t),hExp]
    simpa using (levy_foundations_compoundPoissonCharFun h (by norm_num) b t ξ)
  · intro hm
    have hFalse : ∀ᵐ w ∂P, False := by
      filter_upwards [hm,hEq,exercise49RawCompoundDownJumpV5 P τ Y h b hb] with w hw he hn
      apply hn
      intro s t hst
      change LevyFoundations.compoundPoisson b τ Y (s : ℝ) w ≤ LevyFoundations.compoundPoisson b τ Y (t : ℝ) w
      rw [← he s,← he t]
      exact hw hst
    have hz : P = 0 := by simpa using hFalse
    have hU := congrArg (fun M : Measure ((ℕ → ℝ) × (ℕ → ℝ)) => M Set.univ) hz
    simpa using hU
  · filter_upwards [hEq,exercise49RawCompoundGrowthV5 P τ Y h c hc hCount] with w he hg
    have eq : (fun t : NNReal => X t w) =
      (fun t : NNReal => LevyFoundations.compoundPoisson b τ Y (t : ℝ) w) := funext he
    rw [eq]
    exact hg
