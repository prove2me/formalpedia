-- Prove2me | solution 1 for GlobalTheory.AffinePoints.volume_range_eq_zero_of_mdifferentiable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:26:17.895211+00:00
-- url     : https://prove2.me/submissions/d8c3ebec-5d4c-47e5-92af-d83516b55969

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AffinePoints_volume_image_eq_zero_of_finrank_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial MeasureTheory Module
open scoped Manifold ContDiff
variable {d : ℕ}
namespace GlobalTheory.AffinePoints
theorem _root_.solution {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [LindelofSpace M]
    (h : finrank ℂ E < d) {f : M → Fin d → ℂ} (hf : MDifferentiable I 𝓘(ℂ, Fin d → ℂ) f) :
    volume (range f) = 0 := by
  obtain ⟨t, htc, ht⟩ := countable_cover_nhds (U := fun x : M => (extChartAt I x).source)
    fun x => extChartAt_source_mem_nhds x
  have : range f ⊆ ⋃ x ∈ t, (f ∘ (extChartAt I x).symm) '' (extChartAt I x).target := by
    rintro _ ⟨m, rfl⟩
    obtain ⟨x, hx, hm⟩ := mem_iUnion₂.1 (ht.symm ▸ mem_univ m)
    exact mem_iUnion₂.2 ⟨x, hx, extChartAt I x m, (extChartAt I x).map_source hm, by
      rw [Function.comp_apply, (extChartAt I x).left_inv hm]⟩
  refine measure_mono_null this ((measure_biUnion_null_iff htc).2 fun x _ => ?_)
  exact volume_image_eq_zero_of_finrank_lt h (mdifferentiableOn_iff_differentiableOn.1
    (hf.comp_mdifferentiableOn mdifferentiableOn_extChartAt_symm))
end GlobalTheory.AffinePoints
