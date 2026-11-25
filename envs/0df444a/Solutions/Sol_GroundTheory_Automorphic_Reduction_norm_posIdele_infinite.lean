-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.norm_posIdele_infinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:54:37.372968+00:00
-- url     : https://prove2.me/submissions/4cc5ce83-7a4e-4988-9791-58fdcc6f6c32

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalConditionIndex
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionDirichlet
import Theorems.Thm_GroundTheory_Automorphic_Reduction_infiniteProj_posIdele
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj



set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution (ρ : ℝ) (hρ : 0 < ρ) (w : InfinitePlace K) :
    ‖((posIdele ρ hρ : IdeleGroup K) : 𝔸[K]).1 w‖ = ρ := by
  rw [← coe_infiniteProj, infiniteProj_posIdele]
  have h := norm_posRealElem_pow w (pow_pos hρ w.mult).le
  have hm : w.mult ≠ 0 := by unfold InfinitePlace.mult; split_ifs <;> norm_num
  exact (pow_left_inj₀ (norm_nonneg _) hρ.le hm).1 h
end GroundTheory.Automorphic.Reduction
