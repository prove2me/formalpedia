-- Prove2me | solution 1 for GroundTheory.PAdicHodge.nrm_le_one_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:20:56.04049+00:00
-- url     : https://prove2.me/submissions/45e4f2dd-d661-46f2-aa31-79ab27d78df2

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_nonneg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_pow

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
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {a : Ω} (ha : nrm K a ≤ 1) (n : ℕ) : nrm K (a ^ n) ≤ 1 := by
  rw [nrm_pow]; exact pow_le_one₀ (nrm_nonneg _) ha
end GroundTheory.PAdicHodge
