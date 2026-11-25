-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.kern_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:01:22.88636+00:00
-- url     : https://prove2.me/submissions/5bda1037-5325-4ecc-919f-9bdb510e16cb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_cutoff_nonneg
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_cutoff_le_one

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
theorem _root_.solution {a : ℝ} (ha : 0 ≤ a) (r t : ℝ) : kern a r t ≤ a := by
  unfold kern indicator
  split_ifs with ht
  · have h1 : exp (-a * t) ≤ 1 := exp_le_one_iff.2 (by nlinarith [mem_Ici.1 ht])
    calc a * exp (-a * t) * cutoff r t ≤ a * 1 * 1 := by
          gcongr
          · exact cutoff_nonneg r t
          · exact cutoff_le_one r t
      _ = a := by ring
  · exact ha
end GroundTheory.Automorphic.LineKernel
