-- Prove2me | solution 1 for Kyprianou.Ch01.levyKhintchineLawTargetedBridgeV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T19:27:43.441831+00:00
-- url     : https://prove2.me/submissions/a193d7a1-807b-47a1-a24e-52dc55b76421

import Definitions.Def_Kyprianou_Ch01_LevyTripletExponentTargeted
import Theorems.Thm_levy_foundations_characterisation
import Theorems.Thm_levy_foundations_isInfinitelyDivisible_iff_leanlevy
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem solution
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ProbabilityTheory.IsInfinitelyDivisible μ ↔
      ∃ T : ProbabilityTheory.LevyKhintchineTriple,
        ∀ (ξ : ℝ), charFun μ ξ =
          Complex.exp (Kyprianou.Ch01.levyTripleExponent T ξ) := by
  let toFoundations (T : ProbabilityTheory.LevyKhintchineTriple) :
      LevyFoundations.LevyKhintchineTriple :=
    ⟨T.drift, T.gaussianVariance, T.levyMeasure,
      T.levyMeasure_isLevyMeasure⟩
  let toLeanLevy (T : LevyFoundations.LevyKhintchineTriple) :
      ProbabilityTheory.LevyKhintchineTriple :=
    ⟨T.drift, T.gaussianVariance, T.levyMeasure,
      T.levyMeasure_condition⟩
  have h_exp (T : ProbabilityTheory.LevyKhintchineTriple) (ξ : ℝ) :
      LevyFoundations.exponent (toFoundations T) ξ =
        Kyprianou.Ch01.levyTripleExponent T ξ := by
    have h_int :
        (∫ x, LevyFoundations.compensatedIntegrand ξ x ∂T.levyMeasure) =
          (∫ x, ProbabilityTheory.levyCompensatedIntegrand ξ x ∂T.levyMeasure) := by
      rfl
    simp only [toFoundations, LevyFoundations.exponent,
      Kyprianou.Ch01.levyTripleExponent, h_int]
    push_cast <;> ring
  constructor
  · intro h
    have hf : LevyFoundations.isInfinitelyDivisible μ :=
      (levy_foundations_isInfinitelyDivisible_iff_leanlevy μ).mpr h
    obtain ⟨T, hT⟩ := (levy_foundations_characterisation (μ := μ)).mp hf
    refine ⟨toLeanLevy T, ?_⟩
    intro ξ
    have hTF : toFoundations (toLeanLevy T) = T := by
      cases T
      rfl
    simpa only [← h_exp (toLeanLevy T) ξ, hTF] using hT ξ
  · rintro ⟨T, hT⟩
    apply (levy_foundations_isInfinitelyDivisible_iff_leanlevy μ).mp
    apply (levy_foundations_characterisation (μ := μ)).mpr
    refine ⟨toFoundations T, ?_⟩
    intro ξ
    simpa only [h_exp T ξ] using hT ξ
