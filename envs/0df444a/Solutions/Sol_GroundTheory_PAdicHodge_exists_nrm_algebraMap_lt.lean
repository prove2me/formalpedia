-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_nrm_algebraMap_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:25:58.22683+00:00
-- url     : https://prove2.me/submissions/293b7e86-b35c-4d13-88d3-8c84abe34a15

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.LocalField ValuativeRel Filter Topology
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
variable {K}
variable (K Ω)
namespace GroundTheory.PAdicHodge
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) :
    ∃ a : K, a ≠ 0 ∧ nrm K (algebraMap K Ω a) < ε := by
  letI := normedField K
  obtain ⟨a, ha0, ha1⟩ := NormedField.exists_norm_lt_one K
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε ha1
  refine ⟨a ^ n, pow_ne_zero _ (norm_pos_iff.mp ha0), ?_⟩
  rw [nrm_algebraMap, norm_pow]
  exact hn
end GroundTheory.PAdicHodge
