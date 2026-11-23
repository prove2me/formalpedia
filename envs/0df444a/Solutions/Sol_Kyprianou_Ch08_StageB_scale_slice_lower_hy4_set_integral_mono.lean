-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.scale_slice_lower_hy4_set_integral_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:00:52.103046+00:00
-- url     : https://prove2.me/submissions/682db6b6-7f94-4218-9f09-2ac6c8f5d2eb

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option autoImplicit false
open MeasureTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
private theorem dnn (q : ℝ) (t : WithTop ℝ≥0) : 0 ≤ discountedAt q t := by
  induction t using WithTop.recTopCoe with
  | top => simp [discountedAt]
  | coe s => simp [discountedAt, Real.exp_nonneg]
private theorem dtop (q : ℝ) : discountedAt q (⊤ : WithTop ℝ≥0) = 0 := by
  simp [discountedAt]
theorem solution {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω)
    (U V : Ω → ℝ≥0∞) (hU : AEMeasurable U μ) (hV : AEMeasurable V μ)
    (q : ℝ) (hdi : Integrable (fun ω => discountedAt q (U ω)) μ)
    (hpi : Integrable (fun ω => if U ω < V ω then discountedAt q (U ω) else 0) μ)
    (s : Set Ω) (hsub : s ≤ᵐ[μ] {ω | U ω < V ω ∨ U ω = ⊤}) :
    (∫ ω in s, discountedAt q (U ω) ∂μ) ≤
      ∫ ω, (if U ω < V ω then discountedAt q (U ω) else 0) ∂μ := by
  let E : Set Ω := {ω | U ω < V ω ∨ U ω = ⊤}
  have hE : NullMeasurableSet E μ := by
    dsimp [E]
    have hltSet : NullMeasurableSet {ω | U ω < V ω} μ :=
      (hU.prodMk hV).nullMeasurableSet_preimage
        (measurableSet_lt measurable_fst measurable_snd)
    have htopSet : NullMeasurableSet {ω | U ω = ⊤} μ :=
      nullMeasurableSet_eq_fun hU aemeasurable_const
    exact hltSet.union htopSet
  calc
    (∫ ω in s, discountedAt q (U ω) ∂μ) ≤ ∫ ω in E, discountedAt q (U ω) ∂μ := by
      exact MeasureTheory.setIntegral_mono_set hdi.integrableOn
        (Eventually.of_forall fun ω => dnn q _) (by simpa [E] using hsub)
    _ = ∫ ω in E, (if U ω < V ω then discountedAt q (U ω) else 0) ∂μ := by
      refine MeasureTheory.setIntegral_congr_ae₀ hE (Eventually.of_forall ?_)
      intro ω hω
      dsimp [E] at hω
      rcases hω with hlt | htop
      · simp [hlt]
      · have hnot : ¬ U ω < V ω := by simp [htop]
        have hdisc0 : discountedAt q (U ω) = 0 := by
          rw [htop]
          exact dtop q
        rw [hdisc0, if_neg hnot]
    _ ≤ ∫ ω, (if U ω < V ω then discountedAt q (U ω) else 0) ∂μ :=
      MeasureTheory.setIntegral_le_integral hpi (Eventually.of_forall fun ω => by
        by_cases hlt : U ω < V ω
        · simpa [hlt] using dnn q (U ω)
        · simp [hlt])
