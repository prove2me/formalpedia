-- Prove2me | solution 1 for GlobalTheory.AvgSmooth.clm_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:59:08.720861+00:00
-- url     : https://prove2.me/submissions/7463b964-2417-4be8-b575-e42c78da5a37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ContDiffCompactAverageOfClosedPartials

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.AvgSmooth
variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] {n : ℕ}
namespace GlobalTheory.AvgSmooth
theorem _root_.solution (L : (Fin n → ℝ) →L[ℝ] ℂ) : L = ∑ i, L (Pi.single i 1) • coordC n i := by
  ext1 u
  have e : L u = ∑ i, u i • L (Pi.single i 1) := by
    conv_lhs => rw [← Finset.univ_sum_single u]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_smul]
    congr 1
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [e]
  simp [coordC, ContinuousLinearMap.sum_apply, Complex.real_smul, mul_comm]
end GlobalTheory.AvgSmooth
