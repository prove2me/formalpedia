-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.support_remSum_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:09:48.876698+00:00
-- url     : https://prove2.me/submissions/17c44c10-e2e9-4c0e-8938-63713bd9ac58

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLine
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_Rs_radii_le
import Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_support___subset_41eb0b1e4540


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
variable {M : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε) {a : ℕ → ℝ} (hg : ∀ j, Good M ε j (a j))
include hε hg
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution : support (remSum (ε := ε) (a := a)) ⊆ Icc 0 (ε / 2) := by
  intro t ht
  by_contra h
  apply ht
  unfold remSum
  refine (tsum_congr fun j => ?_).trans tsum_zero
  by_contra hj
  have h1 := support_ρ_subset (fun j => (hg j).1) (radii_pos hε) j hj
  exact h ⟨h1.1, h1.2.trans (Rs_radii_le hε j)⟩
end GroundTheory.Automorphic.LineKernel
