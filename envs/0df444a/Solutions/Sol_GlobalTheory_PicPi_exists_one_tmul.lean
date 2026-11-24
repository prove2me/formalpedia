-- Prove2me | solution 1 for GlobalTheory.PicPi.exists_one_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:27:08.849508+00:00
-- url     : https://prove2.me/submissions/d2bce6de-b1a7-45b2-a987-48220d58d6d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PicPiIsOfFinOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
open GlobalTheory.PicPi
variable {ι : Type} {R : ι → Type} [∀ i, CommRing (R i)] [DecidableEq ι]
namespace GlobalTheory.PicPi
theorem _root_.solution (i : ι) (M : Type) [AddCommGroup M] [Module ((j : ι) → R j) M]
    [Algebra ((j : ι) → R j) (R i)]
    (hA : algebraMap ((j : ι) → R j) (R i) = Pi.evalRingHom R i)
    (z : R i ⊗[(j : ι) → R j] M) : ∃ y : M, (1 : R i) ⊗ₜ y = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r y =>
    refine ⟨(Pi.single i r : (j : ι) → R j) • y, ?_⟩
    rw [← TensorProduct.smul_tmul]
    congr 1
    rw [Algebra.smul_def, hA]
    simp
  | add a b ha hb =>
    obtain ⟨ya, rfl⟩ := ha
    obtain ⟨yb, rfl⟩ := hb
    exact ⟨ya + yb, by rw [TensorProduct.tmul_add]⟩
end GlobalTheory.PicPi
