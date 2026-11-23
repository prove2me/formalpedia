-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.stageB_filtered_raw_set_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T03:58:11.87579+00:00
-- url     : https://prove2.me/submissions/71577539-b593-40e8-978b-d94853031fb9

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
    {𝓕 : Filtration ℝ≥0 mΩ} (A : SpectrallyNegativeLevy P 𝓕)
    (D : SpectrallyNegativeModel Ω P)
    (hAX : ∀ᵐ ω ∂P, ∀ t, A.X t ω = D.X t ω)
    (b h q c : ℝ) :
    (∫ ω in {ω : Ω | NoDrawdownBeforeUpcrossing A.X b h ω},
      c * discountedAt q (tauPlus A.X b ω) ∂P) =
    (∫ ω in {ω : Ω | NoDrawdownBeforeUpcrossing D.X b h ω},
      c * discountedAt q (tauPlus D.X b ω) ∂P) := by
  let gA : Ω → ℝ := fun ω => c * discountedAt q (tauPlus A.X b ω)
  let gD : Ω → ℝ := fun ω => c * discountedAt q (tauPlus D.X b ω)
  let NA : Set Ω := {ω | NoDrawdownBeforeUpcrossing A.X b h ω}
  let ND : Set Ω := {ω | NoDrawdownBeforeUpcrossing D.X b h ω}
  have hg : gA =ᵐ[P] gD := by
    filter_upwards [hAX] with ω hω
    have ht : tauPlus D.X b ω = tauPlus A.X b ω := by simp [tauPlus, hω]
    simp [gA, gD, ht]
  have hset : NA =ᵐ[P] ND := by
    filter_upwards [hAX] with ω hω
    have ht : tauPlus A.X b ω = tauPlus D.X b ω := by simp [tauPlus, hω]
    have hr (t : ℝ≥0) :
        Kyprianou.Ch08.runningSup A.X t ω = Kyprianou.Ch08.runningSup D.X t ω := by
      unfold Kyprianou.Ch08.runningSup
      congr 1
      ext y
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u, hu, hω u⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u, hu, (hω u).symm⟩
    have href (t : ℝ≥0) : reflectAtSup A.X 0 t ω = reflectAtSup D.X 0 t ω := by
      simp [reflectAtSup, hr t, hω t]
    apply propext
    change (∀ t : ℝ≥0, (t : WithTop ℝ≥0) < tauPlus A.X b ω →
        reflectAtSup A.X 0 t ω < h) ↔
      (∀ t : ℝ≥0, (t : WithTop ℝ≥0) < tauPlus D.X b ω →
        reflectAtSup D.X 0 t ω < h)
    constructor
    · intro hA t htD
      have htA : (t : WithTop ℝ≥0) < tauPlus A.X b ω := by simpa [ht] using htD
      simpa [href t] using hA t htA
    · intro hD t htA
      have htD : (t : WithTop ℝ≥0) < tauPlus D.X b ω := by simpa [ht] using htA
      simpa [href t] using hD t htD
  calc
    (∫ ω in NA, gA ω ∂P) = ∫ ω in NA, gD ω ∂P := by
      apply integral_congr_ae
      exact ae_restrict_of_ae hg
    _ = ∫ ω in ND, gD ω ∂P := by
      rw [Measure.restrict_congr_set hset]
