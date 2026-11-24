-- Prove2me | solution 1 for GlobalTheory.span_range_one_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:33:47.815794+00:00
-- url     : https://prove2.me/submissions/4ef2bf74-184a-4545-9029-acbb0dcd691c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
import Theorems.Thm_GlobalTheory_realExtBilin_tmul
import Theorems.Thm_GlobalTheory_realExt_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.realExtBilin_tmul
attribute [local simp] GlobalTheory.realExt_tmul

set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory
variable {X : Type*} [AddCommGroup X]
namespace GlobalTheory
theorem _root_.solution :
    Submodule.span ℝ (Set.range fun x : X => (1 : ℝ) ⊗ₜ[ℤ] x) = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  induction v with
  | zero => exact zero_mem _
  | add v w hv hw => exact add_mem (hv trivial) (hw trivial)
  | tmul s x =>
    have : s ⊗ₜ[ℤ] x = s • ((1 : ℝ) ⊗ₜ[ℤ] x) := by simp [smul_tmul']
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
end GlobalTheory
