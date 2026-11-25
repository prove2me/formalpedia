-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.rectIntegral_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:13:31.149411+00:00
-- url     : https://prove2.me/submissions/fd2cef59-22c0-45e6-a06a-8a75c11110de

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
import Theorems.Thm_GroundTheory_Global_Elliptic_rectIntegral_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Real MeasureTheory Filter Topology intervalIntegral
open scoped Interval
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {z w : ℂ} {f g : ℂ → E}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {f : ℂ → ℂ} (c : ℂ) :
    rectIntegral (fun u ↦ c * f u) z w = c * rectIntegral f z w :=
  rectIntegral_smul (f := f) c
end GroundTheory.Global.Elliptic
