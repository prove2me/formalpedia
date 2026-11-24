-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.HDecay.hasDerivAt_wF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:03:18.622259+00:00
-- url     : https://prove2.me/submissions/e0de1659-7545-4ee5-bfb4-03fb7942d9f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformRapidDecay
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_hasDerivAt_gI
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_hasDerivAt_hI
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_hasDerivAt_eF

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
theorem _root_.solution (hy : y ≠ 0) (a b : ℕ) (t : ℝ) :
    HasDerivAt (wF σ y a b)
      (-((a : ℂ) + 2 + σ) * wF σ y (a + 1) b t - ((b : ℂ) + σ) * wF σ y a (b + 1) t) t := by
  have hg := (hasDerivAt_gI hy t).pow (a + 2)
  have hh : HasDerivAt (fun s => hI y s ^ b) (-(b : ℂ) * hI y t ^ (b + 1)) t := by
    rcases b with _ | b
    · simpa using hasDerivAt_const t (1 : ℂ)
    · refine ((hasDerivAt_hI hy t).pow (b + 1)).congr_deriv ?_
      simp only [Nat.add_sub_cancel]
      push_cast
      ring
  have := (hg.mul hh).mul (hasDerivAt_eF σ hy t)
  refine this.congr_deriv ?_
  have e : a + 2 - 1 = a + 1 := by omega
  simp only [wF, e, Pi.mul_apply, Pi.pow_apply]
  push_cast
  ring
end GlobalTheory.HeckeTwo.HDecay
