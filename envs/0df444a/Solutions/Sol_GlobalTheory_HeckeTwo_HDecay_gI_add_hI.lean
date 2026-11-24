-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.HDecay.gI_add_hI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:21:51.316713+00:00
-- url     : https://prove2.me/submissions/5d5a7fd2-32bb-41e9-aa3a-cc982cd977cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformRapidDecay
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_add_I_ne
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_sub_I_ne
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_sq_add_sq_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex MeasureTheory
open scoped ContDiff FourierTransform
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.HDecay
variable (σ : ℂ) (y : ℝ)
variable {y}
namespace GlobalTheory.HeckeTwo.HDecay
theorem _root_.solution (hy : y ≠ 0) (t : ℝ) :
    gI y t + hI y t = ((2 * t / (t ^ 2 + y ^ 2) : ℝ) : ℂ) := by
  have h1 := add_I_ne hy t
  have h2 := sub_I_ne hy t
  have h3 : ((t ^ 2 + y ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sq_add_sq_pos hy t).ne'
  have hprod : ((t : ℂ) + (y : ℂ) * I) * ((t : ℂ) - (y : ℂ) * I) = ((t ^ 2 + y ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [I_sq]
    ring
  unfold gI hI
  rw [inv_add_inv h1 h2, hprod]
  push_cast
  ring
end GlobalTheory.HeckeTwo.HDecay
