-- Prove2me | solution 1 for GlobalTheory.SymmTensor.tens_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:00:00.409294+00:00
-- url     : https://prove2.me/submissions/4fbfe8a0-fa1f-4f76-9e18-8d6613a2b068

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
theorem _root_.solution : tens (1 : Fin d → Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext I K
  simp only [tens, Matrix.of_apply, Pi.one_apply, Matrix.one_apply]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]
end GlobalTheory.SymmTensor
