-- Prove2me | solution 1 for Lean4LPD.LayerWitness.gamma_weight_bound_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:13:55.903622+00:00
-- url     : https://prove2.me/submissions/63a1a32a-08a3-493a-babf-c5cbbc70b40a

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Theorems.Thm_P2M_Lean4LPD_LayerWitness_weight_P__99b0c6161c46
public import Theorems.Thm_P2M_Lean4LPD_LayerWitness_P__mem_reachable_cc8d734340ab

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.LayerWitness
open PauliString
namespace Lean4LPD.LayerWitness
theorem _root_.solution :
    ∃ q ∈ reachable (layers := [L₁, L₂, L₁]) (Z 3), 4 < q.weight :=
  ⟨P₆, P₆_mem_reachable, by rw [weight_P₆]; norm_num⟩
end Lean4LPD.LayerWitness
