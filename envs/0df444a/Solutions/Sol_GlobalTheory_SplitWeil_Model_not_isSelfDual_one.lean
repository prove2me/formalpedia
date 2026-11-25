-- Prove2me | solution 1 for GlobalTheory.SplitWeil.Model.not_isSelfDual_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:14:52.355371+00:00
-- url     : https://prove2.me/submissions/a46b7d77-8df9-44e8-b044-39d45886846d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field
import Theorems.Thm_GlobalTheory_SplitWeil_Model_indicator_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_Model_noncompact

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
theorem _root_.solution (ν : Measure k) : ¬ IsSelfDual (1 : AddChar k Circle) ν := by
  rintro ⟨h1, h2⟩
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  have := noncompact (k := k)
  have h := h2 _ indicator_mem_SB
  simp [Measure.real, measure_univ_of_isAddLeftInvariant ν, Set.indicator_of_mem (zero_mem 𝒪[k] : (0 : k) ∈ (𝒪[k] : Set k))] at h
end GlobalTheory.SplitWeil.Model
