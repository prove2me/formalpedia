-- Prove2me | solution 1 for GlobalTheory.SplitWeil.Model.measurableEmbedding_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:10.992873+00:00
-- url     : https://prove2.me/submissions/77b155a2-55ca-402f-af37-c134fd4ee117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
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
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitWeil.Model
theorem _root_.solution (n : Type*) [Fintype n] [DecidableEq n] :
    MeasurableEmbedding (fun g : GL n k => g.val) := by
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  refine MeasurableEmbedding.iff_comap_eq.2 ⟨Units.val_injective, rfl, ?_⟩
  have hB : BorelSpace (Matrix n n k) := inferInstanceAs (BorelSpace (n → n → k))
  have : Set.range (fun g : GL n k => g.val) = {x : Matrix n n k | x.det ≠ 0} := by
    ext x
    simp only [Set.mem_range, Set.mem_setOf_eq]
    rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
    rfl
  rw [this]
  exact (isOpen_ne_fun (continuous_id.matrix_det) continuous_const).measurableSet
end GlobalTheory.SplitWeil.Model
