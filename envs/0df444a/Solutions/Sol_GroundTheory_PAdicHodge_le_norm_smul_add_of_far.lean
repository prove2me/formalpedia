-- Prove2me | solution 1 for GroundTheory.PAdicHodge.le_norm_smul_add_of_far
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:18:14.692837+00:00
-- url     : https://prove2.me/submissions/f39269d4-7aaf-4ed1-b502-8f921dbf5c87

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_OrthoBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {k E : Type*} [NontriviallyNormedField k] [IsUltrametricDist k]
  [NormedAddCommGroup E] [NormedSpace k E] [IsUltrametricDist E]
omit [IsUltrametricDist k]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {U : Submodule k E} {w : E} {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hw : ∀ u' ∈ U, s * ‖w‖ ≤ ‖w - u'‖) (a : k) {u : E} (hu : u ∈ U) :
    s * ‖a • w‖ ≤ ‖a • w + u‖ ∧ s * ‖u‖ ≤ ‖a • w + u‖ := by
  have h1 : s * ‖a • w‖ ≤ ‖a • w + u‖ := by
    by_cases ha : a = 0
    · simp [ha]
    · have he : a • w + u = a • (w - (-a⁻¹ • u)) := by
        rw [smul_sub, smul_smul, mul_neg, mul_inv_cancel₀ ha, neg_one_smul, sub_neg_eq_add]
      rw [he, norm_smul, norm_smul]
      have := hw (-a⁻¹ • u) (U.smul_mem _ hu)
      nlinarith [norm_nonneg a]
  refine ⟨h1, ?_⟩
  have h2 : ‖u‖ ≤ max ‖a • w + u‖ ‖a • w‖ := by
    have := IsUltrametricDist.norm_add_le_max (a • w + u) (-(a • w))
    have e : a • w + u + -(a • w) = u := by abel
    rwa [e, norm_neg] at this
  rcases le_max_iff.1 h2 with h | h
  · nlinarith [norm_nonneg u]
  · nlinarith [norm_nonneg u]
end GroundTheory.PAdicHodge
