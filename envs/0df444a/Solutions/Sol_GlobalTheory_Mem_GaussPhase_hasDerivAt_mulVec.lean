-- Prove2me | solution 1 for GlobalTheory.Mem.GaussPhase.hasDerivAt_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:55:36.169796+00:00
-- url     : https://prove2.me/submissions/ecb2e740-6722-4011-b47b-d49fe1f1f5f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtInvApply
import Theorems.Thm_GlobalTheory_Mem_GaussPhase_hasDerivAt_dot

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
theorem _root_.solution (S : Matrix σ σ ℂ) {w : ℝ → σ → ℂ} {w' : σ → ℂ} {t : ℝ}
    (h : HasDerivAt w w' t) : HasDerivAt (fun s => S *ᵥ w s) (S *ᵥ w') t :=
  hasDerivAt_pi.mpr fun i => hasDerivAt_dot (S i) h
end GlobalTheory.Mem.GaussPhase
