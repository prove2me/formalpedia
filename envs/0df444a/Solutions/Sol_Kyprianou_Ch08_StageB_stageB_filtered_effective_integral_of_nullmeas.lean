-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.stageB_filtered_effective_integral_of_nullmeas
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T03:34:52.901433+00:00
-- url     : https://prove2.me/submissions/83b26944-eea1-466b-b726-b64e7b42ca71

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (b h c q : ℝ)
    (hN : NullMeasurableSet {ω : Ω | NoDrawdownBeforeUpcrossing X.X b h ω} P) :
    (∫ ω in {ω : Ω | NoDrawdownBeforeUpcrossing X.X b h ω},
      c * discountedAt q (tauPlus X.X b ω) ∂P) =
    (∫ ω in {ω : Ω | tauPlus X.X b ω < ⊤ ∧ NoDrawdownBeforeUpcrossing X.X b h ω},
      c * discountedAt q (tauPlus X.X b ω) ∂P) := by
  let N : Set Ω := {ω | NoDrawdownBeforeUpcrossing X.X b h ω}
  let Et : Set Ω := {ω | tauPlus X.X b ω < ⊤ ∧ NoDrawdownBeforeUpcrossing X.X b h ω}
  have hsub : Et ⊆ N := by
    intro ω hω
    exact hω.2
  have hzero : ∀ᵐ ω ∂P, ω ∈ N \ Et → c * discountedAt q (tauPlus X.X b ω) = 0 := by
    exact Filter.Eventually.of_forall fun ω hω => by
      have htop : tauPlus X.X b ω = ⊤ := top_unique (not_lt.mp (fun ht => hω.2 ⟨ht, hω.1⟩))
      simp [htop, discountedAt]
  simpa [N, Et] using (MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
    (μ := P) (s := Et) (t := N) (f := fun ω => c * discountedAt q (tauPlus X.X b ω))
    (by simpa [N] using hN) hsub hzero)
