-- Prove2me | solution 1 for GroundTheory.PAdicHodge.NormTower.Fam.inv_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:03:52.48856+00:00
-- url     : https://prove2.me/submissions/e388c4eb-c013-475b-9f66-3fa9b3236063

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsRing
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsField
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Fam_val_eq_zero_iff
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Fam_mul_val
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Fam_zero_val
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Fam_one_val
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Fam_eq_zero_iff
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_inv
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
theorem _root_.solution (x : t.Fam) (n : ℕ) : x⁻¹.1 n = (x.1 n)⁻¹ := by
  by_cases hx : x = 0
  · subst hx; simp
  have hxn : ∀ n, x.1 n ≠ 0 := fun n ↦ by
    rw [Ne, val_eq_zero_iff, ← eq_zero_iff]; exact hx
  let y : t.Fam := ⟨fun n ↦ (x.1 n)⁻¹, fun n ↦ ⟨inv_mem (x.mem n), by rw [t.N_inv, x.N_eq]⟩⟩
  have hxy : x * y = 1 := Subtype.ext (funext fun n ↦ by
    rw [mul_val, one_val]; exact mul_inv_cancel₀ (hxn n))
  rw [inv_eq_of_mul_eq_one_right hxy]
end GroundTheory.PAdicHodge.NormTower.Fam
