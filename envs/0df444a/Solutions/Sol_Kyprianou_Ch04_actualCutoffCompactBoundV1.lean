-- Prove2me | solution 1 for Kyprianou.Ch04.actualCutoffCompactBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:44:25.902177+00:00
-- url     : https://prove2.me/submissions/faf51ece-d327-4b76-bed4-48fcb0091803

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_Kyprianou_Ch04_actualCutoffAffineStepsV1
import Theorems.Thm_Kyprianou_Ch04_twoAffineStepsBoundedV1
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Actual cutoff paths are bounded on each compact horizon. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (hν : IsLevyMeasure ν) (N : PoissonRandomMeasure.{0,0,0} P ν)
    (X Xleft X2 Y : NNReal → Ω → ℝ) (b ε : ℝ) (hε : 0 < ε)
    (hN : ∀ᵐ w ∂P, N.N w = Kyprianou.Ch04.pathJumpMeasure X Xleft w)
    (h2 : ∀ t w, X2 t w = b * (t : ℝ) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂(N.N w))
    (hY : ∀ t w, Y t w = X2 t w +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | ε < |x| ∧ |x| < 1},
        z.2 ∂(N.N w)) - (t : ℝ) *
      (∫ x in {x : ℝ | ε < |x| ∧ |x| < 1}, x ∂ν)) :
    ∀ᵐ w ∂P, ∀ T : NNReal, ∃ C : ℝ, ∀ t ≤ T, |Y t w| ≤ C := by
  filter_upwards [Kyprianou.Ch04.actualCutoffAffineStepsV1
    P ν hν N X Xleft X2 Y b ε hε hN h2 hY] with w hw
  intro T
  obtain ⟨n,hn⟩ := exists_nat_ge T
  obtain ⟨L,S,a,c,h⟩ := hw n
  let d := b - ∫ x in {x : ℝ | ε < |x| ∧ |x| < 1}, x ∂ν
  exact ⟨_,fun t ht => Kyprianou.Ch04.twoAffineStepsBoundedV1 L S
    a Prod.fst c Prod.fst d (n : NNReal) (fun t => Y t w)
    (fun t ht => (h t ht).2) t (ht.trans hn)⟩
