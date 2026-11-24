-- Prove2me | solution 1 for GlobalTheory.Mem.GaussPhase.dot_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:58:24.315528+00:00
-- url     : https://prove2.me/submissions/52f5a25b-c32c-4e32-8a7d-5ef6065560dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtInvApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.GaussPhase
variable {σ : Type} [Fintype σ] [DecidableEq σ]
omit [DecidableEq σ]
namespace GlobalTheory.Mem.GaussPhase
theorem _root_.solution {S : Matrix σ σ ℂ} (hS : Sᵀ = S) (a b : σ → ℂ) :
    (S *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (S *ᵥ b) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hS]
end GlobalTheory.Mem.GaussPhase
