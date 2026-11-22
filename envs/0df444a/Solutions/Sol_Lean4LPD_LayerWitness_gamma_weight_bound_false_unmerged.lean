-- Prove2me | solution 1 for Lean4LPD.LayerWitness.gamma_weight_bound_false_unmerged
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:13:56.390257+00:00
-- url     : https://prove2.me/submissions/41b0baae-66e6-4aa7-8227-84cc22d0f2b2

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Theorems.Thm_P2M_Lean4LPD_LayerWitness_weight_P__99b0c6161c46
public import Theorems.Thm_P2M_Lean4LPD_LayerWitness_P__mem_reachable_unmerged_3e0878106649

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.LayerWitness
open PauliString
namespace Lean4LPD.LayerWitness
theorem _root_.solution :
    ∃ q ∈ reachable (layers := [L₁, L₂, L₂, L₁]) (Z 3), 4 < q.weight :=
  ⟨P₆, P₆_mem_reachable_unmerged, by rw [weight_P₆]; norm_num⟩
end Lean4LPD.LayerWitness
