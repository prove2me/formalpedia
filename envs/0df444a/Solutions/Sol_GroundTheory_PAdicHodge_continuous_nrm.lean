-- Prove2me | solution 1 for GroundTheory.PAdicHodge.continuous_nrm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:09:05.260965+00:00
-- url     : https://prove2.me/submissions/2595432c-76b0-4e45-b197-30d514a95abf

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_zero
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_one
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_neg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_eq_zero
import Theorems.Thm_GroundTheory_PAdicHodge_abs_nrm_sub_nrm_le
import Theorems.Thm_GroundTheory_PAdicHodge_exists_nrm_algebraMap_lt
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_lt_nrm_iff_valuation
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


attribute [local simp] GroundTheory.PAdicHodge.nrm_zero
attribute [local simp] GroundTheory.PAdicHodge.nrm_one
attribute [local simp] GroundTheory.PAdicHodge.nrm_neg
attribute [local simp] GroundTheory.PAdicHodge.nrm_eq_zero

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
variable [TopologicalSpace Ω] [IsValuativeTopology Ω]
variable (K Ω)
namespace GroundTheory.PAdicHodge
theorem _root_.solution : Continuous (nrm K : Ω → ℝ) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨a, ha0, ha⟩ := exists_nrm_algebraMap_lt K Ω hε
  have hv : valuation Ω (algebraMap K Ω a) ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective K Ω).ne ha0
  have hmem := (IsValuativeTopology.hasBasis_nhds x).mem_of_mem (i := Units.mk0 _ hv) trivial
  filter_upwards [hmem] with y hy
  simp only [Units.val_mk0] at hy
  rw [Real.dist_eq]
  refine lt_of_le_of_lt (abs_nrm_sub_nrm_le y x) (lt_of_lt_of_le ?_ ha.le)
  exact (nrm_lt_nrm_iff_valuation _ _).mpr hy
end GroundTheory.PAdicHodge
