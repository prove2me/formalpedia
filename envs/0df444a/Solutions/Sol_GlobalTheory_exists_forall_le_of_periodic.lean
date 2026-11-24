-- Prove2me | solution 1 for GlobalTheory.exists_forall_le_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:42:32.166842+00:00
-- url     : https://prove2.me/submissions/b6c55e1a-2052-4851-942b-6b8e0cd05a3e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsAddFundamentalDomainLatticeDomain
import Theorems.Thm_GlobalTheory_existsUnique_add_mem_latticeDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Submodule Set
open GlobalTheory
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
namespace GlobalTheory
theorem _root_.solution {f : E → ℝ} (hc : Continuous f)
    (hf : ∀ a ∈ L, ∀ x, f (x + a) = f x) : ∃ x₀, ∀ x, f x ≤ f x₀ := by
  have hK := (latticeDomain_isBounded L).isCompact_closure
  obtain ⟨a₀, ha₀, -⟩ := existsUnique_add_mem_latticeDomain L 0
  obtain ⟨x₀, -, hx₀⟩ := hK.exists_isMaxOn ⟨_, subset_closure ha₀⟩ hc.continuousOn
  refine ⟨x₀, fun x => ?_⟩
  obtain ⟨a, ha, -⟩ := existsUnique_add_mem_latticeDomain L x
  rw [← hf a a.2 x]
  exact hx₀ (subset_closure ha)
end GlobalTheory
