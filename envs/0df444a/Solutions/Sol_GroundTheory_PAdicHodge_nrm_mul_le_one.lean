-- Prove2me | solution 1 for GroundTheory.PAdicHodge.nrm_mul_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:17:32.153292+00:00
-- url     : https://prove2.me/submissions/fcff4bdb-ba49-4d4c-bf4b-2960cf43976e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_nonneg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_mul

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
theorem _root_.solution {a b : Ω} (ha : nrm K a ≤ 1) (hb : nrm K b ≤ 1) : nrm K (a * b) ≤ 1 := by
  rw [nrm_mul]; exact mul_le_one₀ ha (nrm_nonneg _) hb
end GroundTheory.PAdicHodge
