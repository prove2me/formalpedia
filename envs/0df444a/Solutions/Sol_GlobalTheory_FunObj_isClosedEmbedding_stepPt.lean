-- Prove2me | solution 1 for GlobalTheory.FunObj.isClosedEmbedding_stepPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:52:41.501183+00:00
-- url     : https://prove2.me/submissions/78585b30-29ec-4728-bec5-16c5116f5e9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field


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
theorem _root_.solution (x₀ : Matrix n n' k) :
    Topology.IsClosedEmbedding (stepPt x₀ : (StepVar n c n' → k) → _) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  refine Function.LeftInverse.isClosedEmbedding
    (f := fun z rs => z rs.1.1 rs.1.2 - basePt c x₀ rs.1.1 rs.1.2) (fun e => ?_)
    (continuous_pi fun rs => (continuous_id.matrix_elem _ _).sub continuous_const)
    (continuous_const.add (continuous_matrix fun r s => ?_))
  · funext rs
    simp only [stepPt, Matrix.add_apply, of_apply, add_sub_cancel_left]
    exact dif_pos rs.2
  · simp only [of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
end GlobalTheory.FunObj
