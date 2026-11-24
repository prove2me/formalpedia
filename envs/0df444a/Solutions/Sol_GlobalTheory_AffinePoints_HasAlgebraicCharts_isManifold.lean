-- Prove2me | solution 1 for GlobalTheory.AffinePoints.HasAlgebraicCharts.isManifold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:09:32.331996+00:00
-- url     : https://prove2.me/submissions/611a733c-a118-4c9c-982f-925fbb6a4045

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Theorems.Thm_GlobalTheory_AffinePoints_IsAlgebraicChart_analyticOnNhd_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial
open scoped Manifold ContDiff
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {A : Type*} [CommRing A] [Algebra 𝕜 A] {d : ℕ}
variable [CompleteSpace 𝕜]
namespace GlobalTheory.AffinePoints
namespace HasAlgebraicCharts
theorem _root_.solution (h : HasAlgebraicCharts 𝕜 A d) :
    letI := h.chartedSpace
    IsManifold 𝓘(𝕜, Fin d → 𝕜) ω (A →ₐ[𝕜] 𝕜) := by
  letI := h.chartedSpace
  refine isManifold_of_contDiffOn _ _ _ fun e e' he he' => ?_
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
    Function.id_comp, Function.comp_id, Set.preimage_id, Set.inter_univ]
  exact (IsAlgebraicChart.analyticOnNhd_trans he he').contDiffOn
    (e.symm ≫ₕ e').open_source.uniqueDiffOn
end HasAlgebraicCharts
end GlobalTheory.AffinePoints
