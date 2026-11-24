-- Prove2me | solution 1 for GlobalTheory.FunObj.continuous_stepPt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:55.864027+00:00
-- url     : https://prove2.me/submissions/e0832d65-39f1-4378-91c7-f6e88846211d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid k}
namespace GlobalTheory.FunObj
theorem _root_.solution {n n' : Type*} {c : ℕ} (x₀ : Matrix n n' k) :
    Continuous fun e : StepVar n c n' → k => stepPt x₀ e := by
  refine continuous_const.add (continuous_matrix fun r s => ?_)
  simp only [of_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const
end GlobalTheory.FunObj
