-- Prove2me | solution 1 for GlobalTheory.FunObj.continuous_keptPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:48:30.766591+00:00
-- url     : https://prove2.me/submissions/458b709f-8826-488d-93fd-170e5f8017d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] {n : Type*} {c : ℕ} {n' : Type*}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.FunObj
theorem _root_.solution : Continuous (keptPt : (KeptVar n c n' → k) → _) := by
  refine continuous_matrix fun r s => ?_
  simp only [keptPt, of_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const
end GlobalTheory.FunObj
