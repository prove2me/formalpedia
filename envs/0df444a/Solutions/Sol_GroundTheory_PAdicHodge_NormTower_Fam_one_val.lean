-- Prove2me | solution 1 for GroundTheory.PAdicHodge.NormTower.Fam.one_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:38:58.098019+00:00
-- url     : https://prove2.me/submissions/34352d70-a26b-44f5-b994-e2fb6cfdc3ca

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsRing
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsField
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Fam_equivFrac_one
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
theorem _root_.solution (n : ℕ) : (1 : t.Fam).1 n = 1 := by
  have : (1 : t.Fam) = (1 : t.Plus).toFam := by
    apply (equivFrac t).injective
    rw [equivFrac_one, equivFrac_toFam, map_one]
  rw [this]; rfl
end GroundTheory.PAdicHodge.NormTower.Fam
