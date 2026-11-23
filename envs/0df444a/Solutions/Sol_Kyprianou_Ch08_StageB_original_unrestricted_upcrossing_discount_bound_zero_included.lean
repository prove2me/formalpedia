-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.original_unrestricted_upcrossing_discount_bound_zero_included
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T08:18:07.793117+00:00
-- url     : https://prove2.me/submissions/3665a744-e84c-47ce-bd02-31035e26256f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_filtered_avram_upcrossing_discount_real_cap
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    Integrable (fun ω => discountedAt q (tauPlus D.X 1 ω)) P ∧
    (∫ ω, discountedAt q (tauPlus D.X 1 ω) ∂P) ≤
      Real.exp (-(Phi ψ q * 1)) := by
  obtain ⟨F, A, hAX, hAψ⟩ := source_result81_filtered_avram_model Ω P D ψ hψ
  have hmember := ((hW q hq).1).2.1
  have hφ : 0 ≤ Phi ψ q := hmember.1
  have hψφ : ψ (Phi ψ q) = q := hmember.2
  have hAroot : A.ψ (Phi ψ q) = q := by
    rw [hAψ (Phi ψ q) hφ]
    exact hψφ
  obtain ⟨hIntegrable, hEstimate⟩ :=
    Kyprianou.Ch08.StageB.filtered_avram_upcrossing_discount_real_cap
      A q hq (Phi ψ q) hφ hAroot
  have hpath : (fun ω => discountedAt q (tauPlus A.X 1 ω)) =ᵐ[P]
      (fun ω => discountedAt q (tauPlus D.X 1 ω)) := by
    filter_upwards [hAX] with ω hω
    have ht : tauPlus A.X 1 ω = tauPlus D.X 1 ω := by
      simp [tauPlus, hω]
    simp [ht]
  refine ⟨hIntegrable.congr hpath, ?_⟩
  calc
    (∫ ω, discountedAt q (tauPlus D.X 1 ω) ∂P)
        = ∫ ω, discountedAt q (tauPlus A.X 1 ω) ∂P :=
          integral_congr_ae hpath.symm
    _ ≤ _ := hEstimate
