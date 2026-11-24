-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.HDecay.hTrans_eq_fourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:39:54.450326+00:00
-- url     : https://prove2.me/submissions/f0f3c725-ac07-4e21-bb8d-5a4e45870470

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformRapidDecay
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_phi_eq_wF

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
variable {σ y}
namespace GlobalTheory.HeckeTwo.HDecay
theorem _root_.solution (hy : y ≠ 0) (ν : ℝ) : hTrans σ ν y = 𝓕 (wF σ y 0 0) ν := by
  rw [Real.fourier_real_eq_integral_exp_smul, hTrans]
  congr 1
  funext t
  rw [phi_eq_wF hy t, smul_eq_mul, mul_comm (Complex.exp _)]
  congr 2
  push_cast
  ring
end GlobalTheory.HeckeTwo.HDecay
