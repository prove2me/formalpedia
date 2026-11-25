-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.hasCompactSupport_iteratedDeriv_deriv_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:55:28.785326+00:00
-- url     : https://prove2.me/submissions/8a48e63c-750c-4f37-a9cb-c4bb6ab45989

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_iteratedDeriv_deriv_cutoff_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function
open scoped ContDiff FourierTransform
noncomputable section
open GroundTheory.Automorphic.LineKernel
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution {r : ℝ} (hr : 0 < r) (i : ℕ) :
    HasCompactSupport (iteratedDeriv i (deriv (cutoff r))) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc fun t ht => by
    by_contra h; exact ht (iteratedDeriv_deriv_cutoff_eq_zero hr h i)
end GroundTheory.Automorphic.LineKernel
