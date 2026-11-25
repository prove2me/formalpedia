-- Prove2me | solution 1 for GlobalTheory.exists_linearIndependent_norm_le_succMin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:55:24.991255+00:00
-- url     : https://prove2.me/submissions/e2f4504e-edfb-48ed-892d-13228213a450

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Theorems.Thm_GlobalTheory_succMinOf_mem
import Theorems.Thm_GlobalTheory_natCast_le_rank_of_le_finrank
import Theorems.Thm_GlobalTheory_finite_mem_and_norm_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped Pointwise
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {L L' : Submodule ℤ E} {i j : ℕ} {r : ℝ}
namespace GlobalTheory
theorem _root_.solution [FiniteDimensional ℝ E] [DiscreteTopology L]
    (hi : i ≤ finrank ℝ (span ℝ (L : Set E))) :
    ∃ v : Fin i → E, LinearIndependent ℝ v ∧ ∀ k, v k ∈ L ∧ ‖v k‖ ≤ succMin L i :=
  (mem_succMinRadii_iff.1
    (succMinOf_mem (finite_mem_and_norm_le L) (natCast_le_rank_of_le_finrank hi))).2
end GlobalTheory
