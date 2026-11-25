-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.decay_fourier_Kc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:22:34.967941+00:00
-- url     : https://prove2.me/submissions/0503754e-cc0b-48fe-8419-e2efcda70a4a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLine
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_one_add_pow_le
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_abs_pow_mul_norm_fourier_KC_le
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_norm_fourier_KC_le_one


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
theorem _root_.solution (m : ℕ) : ∃ C N₀, ∀ N ≥ N₀, ∀ ξ : ℝ,
    ‖𝓕 (fun t => (Kc a (radii ε) N t : ℂ)) ξ‖ ≤ C * (1 + |ξ|) ^ (-(m : ℝ)) := by
  have ha := fun j => (hg j).1
  have hr := radii_pos hε
  set P := ∏ j ∈ Finset.range m, (a j / π) with hP
  refine ⟨2 ^ m * (1 + P), m, fun N hN ξ => ?_⟩
  have h1 := abs_pow_mul_norm_fourier_KC_le ha hr N m (by omega) ξ
  have h2 := norm_fourier_KC_le_one ha hr N ξ
  have h3 := one_add_pow_le |ξ| (abs_nonneg ξ) m
  have hpos : 0 < (1 + |ξ|) ^ m := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
  change ‖𝓕 (KC a (radii ε) N) ξ‖ * (1 + |ξ|) ^ m ≤ _
  calc ‖𝓕 (KC a (radii ε) N) ξ‖ * (1 + |ξ|) ^ m
      ≤ ‖𝓕 (KC a (radii ε) N) ξ‖ * (2 ^ m * (1 + |ξ| ^ m)) :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = 2 ^ m * (‖𝓕 (KC a (radii ε) N) ξ‖ + |ξ| ^ m * ‖𝓕 (KC a (radii ε) N) ξ‖) := by ring
    _ ≤ 2 ^ m * (1 + P) := by gcongr
end GroundTheory.Automorphic.LineKernel
