-- Prove2me | solution 1 for GlobalTheory.RealZeros.br_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:37.908663+00:00
-- url     : https://prove2.me/submissions/6cd4d0df-6a2d-4cb4-9360-c85cda26a48a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannZetaNeZeroOfMemIoo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
open GlobalTheory GlobalTheory.RealZeros
namespace GlobalTheory.RealZeros
theorem _root_.solution (N c d k : ℕ) (σ : ℝ) :
    br N c d k σ = ((((N * k + c : ℕ) : ℝ) ^ (-σ) - ((N * k + d : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [br, ofReal_sub, ofReal_cpow (Nat.cast_nonneg _), ofReal_cpow (Nat.cast_nonneg _)]
  simp
end GlobalTheory.RealZeros
