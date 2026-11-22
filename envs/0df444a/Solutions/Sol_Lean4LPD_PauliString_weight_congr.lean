-- Prove2me | solution 1 for Lean4LPD.PauliString.weight_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:18:18.415196+00:00
-- url     : https://prove2.me/submissions/6efdd08c-ef97-4264-b027-e82948499a71

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution {s t : PauliString n} (hx : s.x = t.x) (hz : s.z = t.z) :
    weight s = weight t := by
  have hsite : site s = site t := by funext i; rw [site, site, hx, hz]
  rw [weight, weight, support, support, hsite]
end Lean4LPD.PauliString
