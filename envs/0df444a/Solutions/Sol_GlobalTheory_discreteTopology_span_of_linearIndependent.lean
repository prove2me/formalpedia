-- Prove2me | solution 1 for GlobalTheory.discreteTopology_span_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:46:57.982282+00:00
-- url     : https://prove2.me/submissions/c9bf1c53-365c-4d9b-b232-8c40472a4698

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
import Theorems.Thm_GlobalTheory_discreteTopology_of_le
import Theorems.Thm_GlobalTheory_exists_basis_range_subset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Module Submodule Matrix
open GlobalTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]
namespace GlobalTheory
theorem _root_.solution {ι : Type*} {v : ι → V}
    (hv : LinearIndependent ℝ v) : DiscreteTopology (span ℤ (Set.range v)) := by
  obtain ⟨β, hβ⟩ := exists_basis_range_subset hv
  exact discreteTopology_of_le (span_mono hβ)
end GlobalTheory
