-- Prove2me | solution 1 for GroundTheory.PAdicHodge.NormTower.IsFam.nrm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:33:57.555978+00:00
-- url     : https://prove2.me/submissions/c26977ca-9cce-40f9-873e-8a2a37272a26

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsRing

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
open GroundTheory.PAdicHodge.NormTower
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] {p : ℕ}
  (t : NormTower K Ω p)
variable {t}
namespace GroundTheory.PAdicHodge.NormTower
namespace IsFam
theorem _root_.solution {z : ℕ → Ω} (hz : t.IsFam z) (i j : ℕ) :
    nrm K (z i) = nrm K (z (i + j)) ^ t.D i j := by
  rw [← hz.Nto_eq i j, nrm_Nto]
end IsFam
end GroundTheory.PAdicHodge.NormTower
