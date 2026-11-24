-- Prove2me | solution 1 for GlobalTheory.frameMul_frameMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:59:03.538098+00:00
-- url     : https://prove2.me/submissions/a2c4a5c5-8e66-4250-961e-08ca2bd4bcf6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Module
open GlobalTheory
variable {ι : Type*} {K : Type*} {V : ι → Type*}
variable [CommSemiring K] [∀ s, AddCommMonoid (V s)] [∀ s, Module K (V s)]
  {l m n : ι → Type*} [∀ s, Fintype (l s)] [∀ s, Fintype (m s)]
namespace GlobalTheory
theorem _root_.solution (x : ∀ s, l s → V s) (b : ∀ s, Matrix (l s) (m s) K)
    (c : ∀ s, Matrix (m s) (n s) K) :
    frameMul (frameMul x b) c = frameMul x (fun s => b s * c s) := by
  funext s j
  simp only [frameMul, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]
end GlobalTheory
