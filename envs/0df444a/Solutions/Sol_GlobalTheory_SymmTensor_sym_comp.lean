-- Prove2me | solution 1 for GlobalTheory.SymmTensor.sym_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:59:57.383799+00:00
-- url     : https://prove2.me/submissions/c03856f7-a4e9-4182-a43a-a6ad7d977f91

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
theorem _root_.solution (X : Fin d → Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin d)) : sym (X ∘ σ) = sym X :=
  Fintype.sum_equiv (Equiv.mulLeft σ) _ _ fun _ => rfl
end GlobalTheory.SymmTensor
