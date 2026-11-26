-- Prove2me | solution 1 for Kyprianou.Ch04.weightedRawIntegralRightV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:35:07.977157+00:00
-- url     : https://prove2.me/submissions/55b741d2-a1c9-453e-80c1-dba8023922f7

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_integerValuedFiniteDiracV1
import Theorems.Thm_Kyprianou_Ch04_klsWindowIntegerValuedV1
import Theorems.Thm_Kyprianou_Ch04_weightedFiniteStepsV1
import Theorems.Thm_Kyprianou_Ch04_finiteStepRightV1
import Theorems.Thm_Kyprianou_Ch04_zeroTimeRestrictionIccIocV1
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Right continuity of the actual closed-window weighted raw Poisson integral. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) (B : Set ℝ)
    (hB : MeasurableSet B) (hfin : ν B < ⊤)
    (g : ℝ × ℝ → Ω → ℝ)
    (hz : ∀ᵐ ω ∂P, N.N ω (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0) :
    ∀ᵐ ω ∂P, ∀ t : NNReal,
      Tendsto (fun s : NNReal =>
        ∫ z in Icc (0 : ℝ) (s : ℝ) ×ˢ B, g z ω ∂(N.N ω))
        (𝓝[>] t) (𝓝 (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ B, g z ω ∂(N.N ω))) := by
  have hD : ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ s : Finset (ℝ × ℝ),
      (N.N ω).restrict (Ioc (0 : ℝ) (T : ℝ) ×ˢ B) =
        ∑ p ∈ s, ((N.N ω).restrict (Ioc (0 : ℝ) (T : ℝ) ×ˢ B)) {p} • Measure.dirac p := by
    filter_upwards [Kyprianou.Ch04.klsWindowIntegerValuedV1 P ν N B hB hfin] with ω hω
    intro T
    exact Kyprianou.Ch02.integerValuedFiniteDiracV1 _ (hω T)
  filter_upwards [Kyprianou.Ch04.weightedFiniteStepsV1 P ν N B hB hfin g hD, hz] with ω hs hzero
  apply Kyprianou.Ch04.finiteStepRightV1
  intro n
  obtain ⟨S,a,hS⟩ := hs n
  refine ⟨S,Prod.fst,a,?_⟩
  intro t ht
  rw [Kyprianou.Ch04.zeroTimeRestrictionIccIocV1 _ hzero]
  exact hS t ht
