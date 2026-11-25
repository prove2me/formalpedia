-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.contDiff_remSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:53:32.73936+00:00
-- url     : https://prove2.me/submissions/c0eeff63-4d03-404c-877f-c3c05443af91

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLine
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_summable_majorant
import Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv___le_majorant_072e9cf9daee
import Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_contDiff___70b804dc509f


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
theorem _root_.solution : ContDiff ℝ ∞ (remSum (ε := ε) (a := a)) := by
  have ha := fun j => (hg j).1
  have hr := radii_pos hε
  refine contDiff_tsum (fun j => contDiff_ρ ha hr j) (fun k _ => summable_majorant hε hg k)
    fun k j t _ => ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact norm_iteratedDeriv_ρ_le_majorant hε hg k j t
end GroundTheory.Automorphic.LineKernel
