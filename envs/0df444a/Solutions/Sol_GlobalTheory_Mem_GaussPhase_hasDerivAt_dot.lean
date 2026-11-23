-- Prove2me | solution 1 for GlobalTheory.Mem.GaussPhase.hasDerivAt_dot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:13.437688+00:00
-- url     : https://prove2.me/submissions/cd8f5100-a42b-4449-89a7-f3e594d01d22

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
theorem _root_.solution (x : σ → ℂ) {w : ℝ → σ → ℂ} {w' : σ → ℂ} {t : ℝ} (h : HasDerivAt w w' t) :
    HasDerivAt (fun s => x ⬝ᵥ w s) (x ⬝ᵥ w') t := by
  simp only [dotProduct]
  exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_pi.mp h k).const_mul _
end GlobalTheory.Mem.GaussPhase
