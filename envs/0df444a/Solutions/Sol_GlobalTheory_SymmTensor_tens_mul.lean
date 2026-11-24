-- Prove2me | solution 1 for GlobalTheory.SymmTensor.tens_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:59:58.884744+00:00
-- url     : https://prove2.me/submissions/ea0ec630-95e1-4478-8e04-48ce5e985944

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemAdjoinGlActionOfCommuteTensorPerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
noncomputable section
open GlobalTheory GlobalTheory.SymmTensor
variable {n d : ℕ}
namespace GlobalTheory.SymmTensor
theorem _root_.solution (X Y : Fin d → Matrix (Fin n) (Fin n) ℂ) : tens X * tens Y = tens (X * Y) := by
  ext I K
  simp only [tens, Matrix.mul_apply, Matrix.of_apply, Pi.mul_apply, ← Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
end GlobalTheory.SymmTensor
