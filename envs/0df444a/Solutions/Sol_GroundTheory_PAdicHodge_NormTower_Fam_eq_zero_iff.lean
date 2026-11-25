-- Prove2me | solution 1 for GroundTheory.PAdicHodge.NormTower.Fam.eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:43:36.536376+00:00
-- url     : https://prove2.me/submissions/5a60c070-4880-411b-81df-35b3cec1aa10

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsRing
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsField
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Fam_val_eq_zero_iff
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Fam_zero_val
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Fam_one_val
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_one
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_zero
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_eq_zero
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_neg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_one
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.PAdicHodge.NormTower.N_one
attribute [local simp] GroundTheory.PAdicHodge.NormTower.N_zero
attribute [local simp] GroundTheory.PAdicHodge.nrm_eq_zero
attribute [local simp] GroundTheory.PAdicHodge.nrm_neg
attribute [local simp] GroundTheory.PAdicHodge.nrm_one
attribute [local simp] GroundTheory.PAdicHodge.nrm_zero


attribute [local simp] GroundTheory.PAdicHodge.NormTower.Fam.zero_val
attribute [local simp] GroundTheory.PAdicHodge.NormTower.Fam.one_val

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
theorem _root_.solution (x : t.Fam) : x = 0 ↔ x.1 0 = 0 := by
  constructor
  · rintro rfl; exact zero_val 0
  · intro h
    exact Subtype.ext (funext fun n ↦ by rw [zero_val]; exact (val_eq_zero_iff x n).mpr h)
end GroundTheory.PAdicHodge.NormTower.Fam
