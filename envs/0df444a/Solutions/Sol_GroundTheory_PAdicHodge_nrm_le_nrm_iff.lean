-- Prove2me | solution 1 for GroundTheory.PAdicHodge.nrm_le_nrm_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:08:28.261717+00:00
-- url     : https://prove2.me/submissions/54373237-fa40-491f-ad08-a3c891d7c934

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower

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
theorem _root_.solution (x y : Ω) : nrm K x ≤ nrm K y ↔ x ≤ᵥ y :=
  (vle_iff_spectralNorm_le (K := K) x y).symm
end GroundTheory.PAdicHodge
