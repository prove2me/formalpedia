-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_technicalQExcursionHeightConstruction_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T23:13:45.23454+00:00
-- url     : https://prove2.me/submissions/a170bd3c-540e-41af-9db2-426e988af982

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_1_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_actual_height_law
set_option autoImplicit false
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

private theorem laplace_eq_nonneg {Ω : Type*} [MeasurableSpace Ω]
    {D : ProcessData Ω} {ψ₀ ψ : ℝ → ℝ}
    (hψ₀ : IsLaplaceExponent D ψ₀) (hψ : IsLaplaceExponent D ψ) :
    ∀ β : ℝ, 0 ≤ β → ψ₀ β = ψ β := by
  intro β hβ
  have ht : (0 : ℝ≥0) < 1 := zero_lt_one
  exact (hψ₀ β 1 hβ ht).2.trans (hψ β 1 hβ ht).2.symm

private theorem scaleFamily_congr_nonneg {ψ₀ ψ : ℝ → ℝ}
    (h : ∀ β : ℝ, 0 ≤ β → ψ₀ β = ψ β)
    {W : ℝ → ℝ → ℝ} (hW : HasSourceScaleFamily ψ₀ W) :
    HasSourceScaleFamily ψ W := by
  intro q hq
  rcases hW q hq with ⟨hroot, hneg, hnon, hcont, hmono, hint⟩
  have hrs : ∀ r : ℝ, RightRootSet ψ₀ r = RightRootSet ψ r := by
    intro r
    ext β
    constructor <;> rintro ⟨hb, hv⟩ <;>
      exact ⟨hb, by simpa [h β hb] using hv⟩
  have hp : ∀ r : ℝ, Phi ψ₀ r = Phi ψ r := by
    intro r
    simp [Phi, hrs r]
  refine ⟨?_, hneg, hnon, hcont, hmono, ?_⟩
  · simpa [PhiIsLargestRoot, hp q, hrs q] using hroot
  · intro β hβ hΦ
    rcases hint β hβ (by simpa [hp q] using hΦ) with ⟨hi, heq⟩
    exact ⟨hi, by simpa [h β hβ] using heq⟩

theorem solution : Kyprianou.Ch08.StageB.technicalQExcursionHeightConstruction := by
  intro Ω _ P _ D ψ hψ q hq
  obtain ⟨ψ₀, W, hψ₀, hW₀, _, _, _, _⟩ := source_result8_1_v2 Ω P D
  have hψeq := laplace_eq_nonneg hψ₀ hψ
  exact source_result8_2_v2_actual_height_law P D ψ W hψ
    (scaleFamily_congr_nonneg hψeq hW₀) q hq
