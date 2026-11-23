-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.shifted_two_sided_upcrossing_eq_original
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:21:18.42181+00:00
-- url     : https://prove2.me/submissions/8aee5d34-d77b-49fe-997f-31d4eb479962

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (q l d : ℝ) :
    upBeforeDownExpectation P X q l (l + d) =
      ∫ ω, (if tauPlus X d ω < tauMinus X (-l) ω
        then discountedAt q (tauPlus X d ω) else 0) ∂P := by
  have hplus (ω : Ω) :
      tauPlus (shifted X l) (l + d) ω = tauPlus X d ω := by
    unfold tauPlus
    congr 1
    ext t
    simp only [Set.mem_setOf_eq, shifted]
    constructor
    · rintro ⟨u, hu0, hu, hcross⟩
      exact ⟨u, hu0, hu, by linarith⟩
    · rintro ⟨u, hu0, hu, hcross⟩
      exact ⟨u, hu0, hu, by linarith⟩
  have hminus (ω : Ω) :
      tauMinus (shifted X l) 0 ω = tauMinus X (-l) ω := by
    unfold tauMinus
    congr 1
    ext t
    simp only [Set.mem_setOf_eq, shifted]
    constructor
    · rintro ⟨u, hu0, hu, hcross⟩
      exact ⟨u, hu0, hu, by linarith⟩
    · rintro ⟨u, hu0, hu, hcross⟩
      exact ⟨u, hu0, hu, by linarith⟩
  unfold upBeforeDownExpectation
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall (fun ω => by
      change (if tauPlus (shifted X l) (l + d) ω < tauMinus (shifted X l) 0 ω then
          discountedAt q (tauPlus (shifted X l) (l + d) ω) else 0) =
        (if tauPlus X d ω < tauMinus X (-l) ω then
          discountedAt q (tauPlus X d ω) else 0)
      rw [hplus ω, hminus ω]))
