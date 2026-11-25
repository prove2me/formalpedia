-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.tendsto_fourier_Kc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:09:51.121262+00:00
-- url     : https://prove2.me/submissions/9c00a948-ba9e-4a00-89f3-9d02027709b7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLine
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_norm_fourier_KC_succ_sub_le


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
theorem _root_.solution (ξ : ℝ) : ∃ l : ℂ,
    Tendsto (fun N => 𝓕 (fun t => (Kc a (radii ε) N t : ℂ)) ξ) atTop (𝓝 l) := by
  have ha := fun j => (hg j).1
  have hr := radii_pos hε
  have hd : ∀ N, dist (𝓕 (KC a (radii ε) N) ξ) (𝓕 (KC a (radii ε) N.succ) ξ) ≤
      4 * π * |ξ| * (ε / 16) * (1 / 2) ^ N + (1 / 2) ^ (N + 1) := by
    intro N
    rw [dist_comm, dist_eq_norm]
    refine (norm_fourier_KC_succ_sub_le ha hr N ξ).trans (add_le_add (le_of_eq ?_) ?_)
    · unfold radii; rw [pow_add, pow_add, one_div_pow]; field_simp; ring
    · exact (hg (N + 1)).2.2.2
  have hs : Summable fun N : ℕ => 4 * π * |ξ| * (ε / 16) * (1 / 2 : ℝ) ^ N + (1 / 2) ^ (N + 1) :=
    (summable_geometric_two.mul_left _).add (summable_geometric_two.comp_injective
      (add_left_injective 1))
  exact cauchySeq_tendsto_of_complete (cauchySeq_of_dist_le_of_summable _ hd hs)
end GroundTheory.Automorphic.LineKernel
