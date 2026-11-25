-- Prove2me | solution 1 for Kyprianou.Ch04.actualCutoffAffineStepsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:20:32.579166+00:00
-- url     : https://prove2.me/submissions/5eda2beb-b95a-4f02-961b-66d4af1c0e04

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_Kyprianou_Ch04_finiteCutoffWindowStepsV1
import Theorems.Thm_Kyprianou_Ch04_pathJumpMeasureZeroTimeV1
import Theorems.Thm_Kyprianou_Ch04_zeroTimeRestrictionIccIocV1
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Actual closed-window finite-cutoff paths are affine plus finite steps. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (hν : IsLevyMeasure ν) (N : PoissonRandomMeasure.{0,0,0} P ν)
    (X Xleft X2 Y : NNReal → Ω → ℝ) (b ε : ℝ) (hε : 0 < ε)
    (hN : ∀ᵐ ω ∂P, N.N ω = Kyprianou.Ch04.pathJumpMeasure X Xleft ω)
    (h2 : ∀ t ω, X2 t ω = b * (t : ℝ) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂(N.N ω))
    (hY : ∀ t ω, Y t ω = X2 t ω +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | ε < |x| ∧ |x| < 1},
        z.2 ∂(N.N ω)) -
      (t : ℝ) * (∫ x in {x : ℝ | ε < |x| ∧ |x| < 1}, x ∂ν)) :
    ∀ᵐ ω ∂P, ∀ T : ℕ,
      ∃ (L S : Finset (ℝ × ℝ)) (a c : ℝ × ℝ → ℝ),
        ∀ t : NNReal, t ≤ (T : NNReal) →
          X2 t ω = b * (t : ℝ) + (∑ p ∈ L, if p.1 ≤ (t : ℝ) then a p else 0) ∧
          Y t ω = (b - ∫ x in {x : ℝ | ε < |x| ∧ |x| < 1}, x ∂ν) * (t : ℝ) +
            (∑ p ∈ L, if p.1 ≤ (t : ℝ) then a p else 0) +
            (∑ p ∈ S, if p.1 ≤ (t : ℝ) then c p else 0) := by
  filter_upwards [hN, Kyprianou.Ch04.finiteCutoffWindowStepsV1 P ν hν N ε hε] with ω hω hs
  have hz : N.N ω (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
    rw [hω]
    exact Kyprianou.Ch04.pathJumpMeasureZeroTimeV1 X Xleft ω
  intro T
  obtain ⟨L,S,a,c,hLS⟩ := hs T
  refine ⟨L,S,a,c,?_⟩
  intro t ht
  obtain ⟨hL,hS⟩ := hLS t ht
  have hL' : (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
      z.2 ∂(N.N ω)) = ∑ p ∈ L, if p.1 ≤ (t : ℝ) then a p else 0 := by
    rw [Kyprianou.Ch04.zeroTimeRestrictionIccIocV1 _ hz]
    exact hL
  have hS' : (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | ε < |x| ∧ |x| < 1},
      z.2 ∂(N.N ω)) = ∑ p ∈ S, if p.1 ≤ (t : ℝ) then c p else 0 := by
    rw [Kyprianou.Ch04.zeroTimeRestrictionIccIocV1 _ hz]
    exact hS
  constructor
  · rw [h2, hL']
  · rw [hY, h2, hL', hS']
    ring
