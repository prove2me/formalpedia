-- Prove2me | solution 1 for Lean4LPD.LayerWitness.gamma_layers_weight_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:13:51.376237+00:00
-- url     : https://prove2.me/submissions/e253b666-a62e-4129-adb1-def3fdfb1786

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Theorems.Thm_P2M_Lean4LPD_LayerWitness_weight_P__2eb9aa3c5ab1
public import Theorems.Thm_P2M_Lean4LPD_LayerWitness_P__mem_reachable_4ba0f0956398

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.LayerWitness
open PauliString
namespace Lean4LPD.LayerWitness
theorem _root_.solution :
    ∃ q ∈ reachable (layers := [L₁, L₂]) (Z 3), q.weight = 4 :=
  ⟨P₄, P₄_mem_reachable, weight_P₄⟩
end Lean4LPD.LayerWitness
