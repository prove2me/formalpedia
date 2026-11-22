-- Prove2me | solution 1 for Lean4LPD.PauliString.weight_mul_add_card_cancelSites
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:59:21.658895+00:00
-- url     : https://prove2.me/submissions/2f141a48-4257-4034-95fe-9d7daf3c2521

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n} {i : Fin n}
namespace Lean4LPD.PauliString
theorem _root_.solution (G s : PauliString n) :
    weight (G * s) + (cancelSites G s).card = weight s + (createSites G s).card := by
  have h1 : (cancelSites G s).card + weight (G * s)
      = (support s ∪ support (G * s)).card :=
    Finset.card_sdiff_add_card _ _
  have h2 : (createSites G s).card + weight s
      = (support (G * s) ∪ support s).card :=
    Finset.card_sdiff_add_card _ _
  rw [Finset.union_comm] at h2
  omega
end Lean4LPD.PauliString
