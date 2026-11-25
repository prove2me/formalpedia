-- Prove2me | solution 1 for GroundTheory.PAdicHodge.nrm_lt_nrm_iff_valuation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:35:12.868936+00:00
-- url     : https://prove2.me/submissions/b98602b8-7b74-4519-a917-4d52360ad819

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_le_nrm_iff_valuation

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
variable [ValuativeRel Ω] [ValuativeExtension K Ω]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (x y : Ω) :
    nrm K x < nrm K y ↔ valuation Ω x < valuation Ω y := by
  rw [← not_le, ← not_le, nrm_le_nrm_iff_valuation]
end GroundTheory.PAdicHodge
