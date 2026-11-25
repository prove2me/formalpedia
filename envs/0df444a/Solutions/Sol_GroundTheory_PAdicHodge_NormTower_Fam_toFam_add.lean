-- Prove2me | solution 1 for GroundTheory.PAdicHodge.NormTower.Fam.toFam_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:31:34.704255+00:00
-- url     : https://prove2.me/submissions/de6a4855-9b04-4b0d-9f27-00ef5acbf785

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsRing
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsField
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Fam_equivFrac_add
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Fam_equivFrac_toFam

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
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.LocalField ValuativeRel Filter Topology
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] {p : ℕ}
open GroundTheory.PAdicHodge.NormTower
variable (t : NormTower K Ω p)
open GroundTheory.PAdicHodge.NormTower.Fam
variable {t}
namespace GroundTheory.PAdicHodge.NormTower.Fam
theorem _root_.solution (a b : t.Plus) : (a + b).toFam = a.toFam + b.toFam := by
  apply (equivFrac t).injective
  rw [equivFrac_add, equivFrac_toFam, equivFrac_toFam, equivFrac_toFam, map_add]
end GroundTheory.PAdicHodge.NormTower.Fam
