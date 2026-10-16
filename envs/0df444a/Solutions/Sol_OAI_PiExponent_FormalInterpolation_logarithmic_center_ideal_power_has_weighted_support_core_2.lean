-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.logarithmic_center_ideal_power_has_weighted_support_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T05:42:58.863513+00:00
-- url     : https://prove2.me/submissions/4fc9116f-c0d2-4a17-90d6-f0fb03ef58f2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_WeightedSupport
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_formalJet_logarithmic_center_generator_has_weighted_support
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_formalJet_has_nonnegative_weighted_support
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_ideal_power_has_weighted_support_of_generators_nonnegative

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (v : Fin (m + 1) → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℝ) * v 0)
    (R : ℝ) (he : ∀ i, R ≤ (e i : ℝ) * v i)
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ FormalInterpolation.logarithmicCenterIdeal c T e ^ n) :
    FormalInterpolation.hasWeightedSupport v ((n : ℝ) * R)
      (FormalInterpolation.formalJet c P) := by
  apply OAI.PiExponent.FormalInterpolation.ideal_power_has_weighted_support_of_generators_nonnegative
    v hv R n (FormalInterpolation.formalJet c)
    (fun i => FormalInterpolation.logarithmicCoordinate c T i ^ e i)
  · intro Q
    exact OAI.PiExponent.FormalInterpolation.formalJet_has_nonnegative_weighted_support
      c T v hv hT Q
  · intro i
    exact OAI.PiExponent.FormalInterpolation.formalJet_logarithmic_center_generator_has_weighted_support
      c T e v hv hT R he i
  · simpa [FormalInterpolation.logarithmicCenterIdeal] using hP