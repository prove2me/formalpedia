-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.hasSum_integral_remSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:09:57.095184+00:00
-- url     : https://prove2.me/submissions/f433e0a0-67ff-4781-9511-7f691ba57b0e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLine
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_Rs_radii_le
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_norm_le_of_support
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_summable_majorant
import Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv___le_majorant_072e9cf9daee
import Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_contDiff___70b804dc509f
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
theorem _root_.solution {F : ℝ → ℂ} (hF : Continuous F) {B : ℝ}
    (hB : ∀ t ∈ Icc (-ε) ε, ‖F t‖ ≤ B) :
    HasSum (fun j => ∫ t, F t * ρ a (radii ε) j t) (∫ t, F t * remSum (ε := ε) (a := a) t) := by
  have ha := fun j => (hg j).1
  have hr := radii_pos hε
  have hint : ∀ j, Integrable fun t => F t * ρ a (radii ε) j t := fun j =>
    (hF.mul (contDiff_ρ ha hr j).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_ρ_subset ha hr j)).mul_left
  have hbound : ∀ j, ∫ t, ‖F t * ρ a (radii ε) j t‖ ≤ (B * majorant hε hg 0 j) * (ε / 2) := by
    intro j
    refine integral_norm_le_of_support (hF.mul (contDiff_ρ ha hr j).continuous) (by positivity)
      ?_ ?_
    · intro t ht
      have h1 : t ∈ support (ρ a (radii ε) j) := fun h => ht (by simp [h])
      have h2 := support_ρ_subset ha hr j h1
      exact ⟨h2.1, h2.2.trans (Rs_radii_le hε j)⟩
    · intro t ht
      rw [Pi.mul_apply, norm_mul]
      have h1 := hB t ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have h2 : ‖ρ a (radii ε) j t‖ ≤ majorant hε hg 0 j := by
        simpa using norm_iteratedDeriv_ρ_le_majorant hε hg 0 j t
      exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  have hsum : Summable fun j => ∫ t, ‖F t * ρ a (radii ε) j t‖ :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg fun t => norm_nonneg _) hbound
      (((summable_majorant hε hg 0).mul_left B).mul_right (ε / 2))
  have := hasSum_integral_of_summable_integral_norm hint hsum
  have e : ∫ t, F t * remSum (ε := ε) (a := a) t = ∫ t, ∑' j, F t * ρ a (radii ε) j t := by
    congr 1; funext t; rw [remSum, tsum_mul_left]
  rw [e]; exact this
end GroundTheory.Automorphic.LineKernel
