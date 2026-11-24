-- Prove2me | solution 1 for GlobalTheory.HeckeTheta.Decay.norm_gauss_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:40:12.306831+00:00
-- url     : https://prove2.me/submissions/9f459604-12c7-4ef7-8222-b456e5328c2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableWeightedHeckeThetaKernelHalfSpace
import Theorems.Thm_GlobalTheory_HeckeTheta_Decay_pow_mul_exp_le
import Theorems.Thm_GlobalTheory_HeckeTheta_norm_hmon


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
theorem _root_.solution (n : I → ℤ) (w : I → ℂ) :
    ‖gauss n w‖ ≤ gC n * Real.exp (-Real.pi * ∑ i, ‖w i‖ ^ 2) := by
  unfold gauss gC
  rw [norm_prod, Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
  intro i _
  rw [norm_mul, norm_hmon, Complex.norm_exp_ofReal]
  have := pow_mul_exp_le (n i).natAbs (norm_nonneg (w i))
  convert this using 2
end GlobalTheory.HeckeTheta.Decay
