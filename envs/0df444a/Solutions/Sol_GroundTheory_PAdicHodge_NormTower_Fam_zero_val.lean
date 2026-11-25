-- Prove2me | solution 1 for GroundTheory.PAdicHodge.NormTower.Fam.zero_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:39:01.742437+00:00
-- url     : https://prove2.me/submissions/3f00611c-c68b-4fd7-8b23-1453ff2336e2

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsRing
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsField
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Fam_equivFrac_zero
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
theorem _root_.solution (n : ℕ) : (0 : t.Fam).1 n = 0 := by
  have : (0 : t.Fam) = (0 : t.Plus).toFam := by
    apply (equivFrac t).injective
    rw [equivFrac_zero, equivFrac_toFam, map_zero]
  rw [this]; rfl
end GroundTheory.PAdicHodge.NormTower.Fam
