-- Prove2me | solution 1 for GlobalTheory.HeckeTheta.Decay.norm_term_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:56:10.379347+00:00
-- url     : https://prove2.me/submissions/f095ea73-dd50-44d2-9669-c6b4bdfdac2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableWeightedHeckeThetaKernelHalfSpace
import Theorems.Thm_GlobalTheory_HeckeTheta_Decay_gC_nonneg
import Theorems.Thm_GlobalTheory_HeckeTheta_Decay_norm_gauss_le
import Theorems.Thm_GlobalTheory_HeckeTheta_Decay_norm_dil_sq
import Theorems.Thm_GlobalTheory_HeckeTheta_Decay_sum_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeTheta GlobalTheory.HeckeTheta.Decay
open GlobalTheory.HeckeTheta
variable {I : Type} [Fintype I]
namespace GlobalTheory.HeckeTheta.Decay
theorem _root_.solution (n : I → ℤ) (y : I → ℝ) (v : I → ℂ) {τ : ℝ} (hτ : 0 ≤ τ)
    (hy : ∀ i, τ ≤ Real.exp (y i)) :
    ‖gauss n (dil y v)‖ ≤ gC n * Real.exp (-Real.pi * τ * ‖v‖ ^ 2) := by
  refine (norm_gauss_le n _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (gC_nonneg n)
  apply Real.exp_le_exp.mpr
  simp_rw [norm_dil_sq]
  have := mul_le_mul_of_nonneg_left (sum_ge y v hτ hy) Real.pi_pos.le
  linarith
end GlobalTheory.HeckeTheta.Decay
