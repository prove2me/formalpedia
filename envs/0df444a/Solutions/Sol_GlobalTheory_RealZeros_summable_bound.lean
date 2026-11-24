-- Prove2me | solution 1 for GlobalTheory.RealZeros.summable_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:38.789207+00:00
-- url     : https://prove2.me/submissions/cc45a96f-6d2e-4c43-a841-f9d8c487401c

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
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    Summable fun k : ℕ => C * ((k + 1 : ℕ) : ℝ) ^ (-ε - 1) :=
  ((summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-ε - 1)) 1).mpr
    (Real.summable_nat_rpow.mpr (by linarith))).mul_left C
end GlobalTheory.RealZeros
