-- Prove2me | solution 1 for Lean4LPD.LayerWitness.gamma_layers_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:13:50.092417+00:00
-- url     : https://prove2.me/submissions/44de476b-1b15-4924-8d15-13d27f30c1c2

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Theorems.Thm_Lean4LPD_PauliString_support_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_self_mem_branch
public import Theorems.Thm_Lean4LPD_PauliString_oneLayer_nil
public import Theorems.Thm_Lean4LPD_PauliString_oneLayer_cons
public import Theorems.Thm_Lean4LPD_PauliString_reachable_nil
public import Theorems.Thm_Lean4LPD_PauliString_reachable_cons
public import Theorems.Thm_Lean4LPD_PauliString_cover_nil
public import Theorems.Thm_Lean4LPD_PauliString_reachable_weight_le
public import Theorems.Thm_P2M_Lean4LPD_LayerWitness_isLayer_L__a95698ae6318
public import Theorems.Thm_P2M_Lean4LPD_LayerWitness_isLayer_L__ef16fb08fa2b
public import Theorems.Thm_Lean4LPD_LayerWitness_weight_Z_three
public import Theorems.Thm_Lean4LPD_PauliString_mem_antiSites
public import Theorems.Thm_Lean4LPD_PauliString_mem_support
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_phaseMul_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_self_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_phase
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_x
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_z
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_zero
public import Theorems.Thm_Lean4LPD_PauliString_site_mul
public import Theorems.Thm_Lean4LPD_PauliString_site_one
public import Theorems.Thm_Lean4LPD_PauliString_site_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_mul_self_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_left
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_self
public import Theorems.Thm_Lean4LPD_PauliString_weight_one
public import Theorems.Thm_Lean4LPD_PauliString_weight_phaseMul
attribute [local simp] Lean4LPD.PauliString.mem_antiSites
attribute [local simp] Lean4LPD.PauliString.mem_support
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_phaseMul_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_self_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_phase
attribute [local simp] Lean4LPD.PauliString.phaseMul_x
attribute [local simp] Lean4LPD.PauliString.phaseMul_z
attribute [local simp] Lean4LPD.PauliString.phaseMul_zero
attribute [local simp] Lean4LPD.PauliString.site_mul
attribute [local simp] Lean4LPD.PauliString.site_one
attribute [local simp] Lean4LPD.PauliString.site_phaseMul
attribute [local simp] Lean4LPD.PauliString.sympForm_mul_self_right
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_left
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_right
attribute [local simp] Lean4LPD.PauliString.sympForm_self
attribute [local simp] Lean4LPD.PauliString.weight_one
attribute [local simp] Lean4LPD.PauliString.weight_phaseMul


attribute [local simp] Lean4LPD.PauliString.support_phaseMul
attribute [local simp] Lean4LPD.PauliString.self_mem_branch
attribute [local simp] Lean4LPD.PauliString.oneLayer_nil
attribute [local simp] Lean4LPD.PauliString.oneLayer_cons
attribute [local simp] Lean4LPD.PauliString.reachable_nil
attribute [local simp] Lean4LPD.PauliString.reachable_cons
attribute [local simp] Lean4LPD.PauliString.cover_nil

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.LayerWitness
open PauliString
namespace Lean4LPD.LayerWitness
theorem _root_.solution :
    ∀ q ∈ reachable (layers := [L₁, L₂]) (Z 3), q.weight ≤ 4 := by
  intro q hq
  have h := reachable_weight_le (kh := 2)
    (fun L hL => by
      rcases List.mem_cons.1 hL with rfl | hL
      · exact isLayer_L₁
      · rw [List.mem_singleton.1 hL]; exact isLayer_L₂)
    (by norm_num) hq
  simpa [weight_Z_three] using h
end Lean4LPD.LayerWitness
