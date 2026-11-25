-- Prove2me | solution 1 for GroundTheory.PAdicHodge.nrm_sub_le_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:50:47.375307+00:00
-- url     : https://prove2.me/submissions/089660e7-acff-42df-9bdf-09d079d87b67

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_neg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_add_le_max
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue


attribute [local simp] GroundTheory.PAdicHodge.nrm_neg

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
namespace GroundTheory.PAdicHodge
theorem _root_.solution (x y : Ω) : nrm K (x - y) ≤ max (nrm K x) (nrm K y) := by
  rw [sub_eq_add_neg, ← nrm_neg y]
  exact nrm_add_le_max x (-y)
end GroundTheory.PAdicHodge
