-- Prove2me | solution 1 for GlobalTheory.T.mem_adjoin_glAction_of_commute_tensorPerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:54:09.048856+00:00
-- url     : https://prove2.me/submissions/760cef51-6c89-403c-97de-052a93bbd7f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemAdjoinGlActionOfCommuteTensorPerm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemAdjoinGlActionOfCommuteTensorPermStatement
import Theorems.Thm_GlobalTheory_SymmTensor_mem_adjoin_polar


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n d : ℕ) (T : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ), (∀ π, T * permMat n d π = permMat n d π * T) → T ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2) := by
  first | exact @GlobalTheory.SymmTensor.mem_adjoin_polar | exact GlobalTheory.SymmTensor.mem_adjoin_polar | (intros; apply GlobalTheory.SymmTensor.mem_adjoin_polar <;> assumption)
end _root_.GlobalTheory.T
