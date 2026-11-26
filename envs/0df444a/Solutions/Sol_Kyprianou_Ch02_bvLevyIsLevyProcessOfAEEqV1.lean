-- Prove2me | solution 1 for Kyprianou.Ch02.bvLevyIsLevyProcessOfAEEqV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:40:00.995418+00:00
-- url     : https://prove2.me/submissions/1aa6e29f-e6a1-4bc4-afdd-5187d6e4dd81

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
/-- An indistinguishable process with exact zero start is still a Lévy process. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Y Z : ℝ≥0 → Ω → ℝ)
    (hY : ProbabilityTheory.IsLevyProcess Y P)
    (hZ0 : Z 0 = fun _ => 0)
    (hae : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Y t ω = Z t ω) :
    ProbabilityTheory.IsLevyProcess Z P := by
  have hEq : ∀ t, Z t =ᵐ[P] Y t := by
    intro t
    filter_upwards [hae] with ω hω
    exact (hω t).symm
  refine ⟨hZ0, ?_, ?_, ?_⟩
  · intro n ts ht
    have heq : ∀ k : Fin n,
        increment Z (ts k.castSucc) (ts k.succ) =ᵐ[P]
          increment Y (ts k.castSucc) (ts k.succ) := by
      intro k
      filter_upwards [hEq (ts k.succ), hEq (ts k.castSucc)] with ω h1 h0
      simp only [increment, h1, h0]
    exact (iIndepFun_congr heq).mpr (hY.indep_increments n ts ht)
  · intro s u
    have h := hY.stationary_increments s u
    have h1 : IdentDistrib (increment Y s (s + u)) (increment Z s (s + u)) P P := by
      apply IdentDistrib.of_ae_eq h.aemeasurable_fst
      filter_upwards [hae] with ω hw
      simp only [increment, hw]
    have h2 : IdentDistrib (increment Y 0 u) (increment Z 0 u) P P := by
      apply IdentDistrib.of_ae_eq h.aemeasurable_snd
      filter_upwards [hae] with ω hw
      simp only [increment, hw]
    exact (h1.symm.trans h).trans h2
  · filter_upwards [hae, hY.cadlag_ae] with ω he hc
    have heq : (fun t => Z t ω) = (fun t => Y t ω) := funext fun t => (he t).symm
    rw [heq]
    exact hc
