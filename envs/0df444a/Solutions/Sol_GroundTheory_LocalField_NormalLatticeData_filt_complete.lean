-- Prove2me | solution 1 for GroundTheory.LocalField.NormalLatticeData.filt_complete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:29:55.807433+00:00
-- url     : https://prove2.me/submissions/2a8fa762-7454-45b5-96f3-6d0f3d8cfb02

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal
import Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_val_sub_one_mem
import Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_div_mem_filt_iff
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_smul_F
import Theorems.Thm_GroundTheory_LocalField_exists_limit_normalLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.StableFiltration.coe_smul_F



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
open GroundTheory.LocalField.NormalLatticeData
variable (D : NormalLatticeData K L)
attribute [local instance] action
namespace GroundTheory.LocalField.NormalLatticeData
theorem _root_.solution : FiltrationComplete D.filt.F := by
  intro x hx
  obtain ⟨z, hz, hlim⟩ := exists_limit_normalLattice D.π D.θ D.irreducible D.linearIndependent
    (s := D.k) (fun n => D.val (x n) - 1) (fun n => D.val_sub_one_mem (x n)) (fun N => by
      obtain ⟨M, hM⟩ := hx N
      refine ⟨M, fun m hm n hn => ?_⟩
      have := D.div_mem_filt_iff.mp (hM m hm n hn)
      rwa [sub_sub_sub_cancel_right])
  obtain ⟨w, hw, -⟩ := D.exists_unit le_rfl hz
  have hw0 : w ∈ D.units 0 := by
    rw [mem_units, hw, add_sub_cancel_left]
    exact hz
  refine ⟨⟨w, hw0⟩, fun N => ?_⟩
  obtain ⟨M, hM⟩ := hlim N
  refine ⟨M, fun n hn => D.div_mem_filt_iff.mpr ?_⟩
  have e : D.val (x n) - D.val ⟨w, hw0⟩ = (D.val (x n) - 1) - z := by
    simp only [val, hw]
    ring
  rw [e]
  exact hM n hn
end GroundTheory.LocalField.NormalLatticeData
