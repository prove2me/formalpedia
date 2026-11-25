-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.isCompact_units_abs_log_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:37:33.321768+00:00
-- url     : https://prove2.me/submissions/2f4f04e2-726a-492d-a414-97db8f1e797b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Theorems.Thm_GroundTheory_Global_IdeleGroup_abs_log_le_iff
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Topology Filter NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
omit [NumberField K]
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (w : InfinitePlace K) (M : ℝ) :
    IsCompact {z : (w.Completion)ˣ | |Real.log ‖(z : w.Completion)‖| ≤ M} := by
  rw [Units.isEmbedding_val₀.isCompact_iff]
  have h : ((↑) : (w.Completion)ˣ → w.Completion) ''
      {z : (w.Completion)ˣ | |Real.log ‖(z : w.Completion)‖| ≤ M} =
      {c : w.Completion | Real.exp (-M) ≤ ‖c‖ ∧ ‖c‖ ≤ Real.exp M} := by
    ext c
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (abs_log_le_iff (norm_pos_iff.2 z.ne_zero)).1 hz
    · rintro ⟨h1, h2⟩
      have hc : c ≠ 0 := norm_pos_iff.1 ((Real.exp_pos _).trans_le h1)
      exact ⟨Units.mk0 c hc, (abs_log_le_iff (norm_pos_iff.2 hc)).2 ⟨h1, h2⟩, rfl⟩
  rw [h]
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · exact (Metric.isBounded_closedBall (x := (0 : w.Completion)) (r := Real.exp M)).subset
      fun c hc ↦ by simpa using hc.2
end GroundTheory.Global.IdeleGroup
