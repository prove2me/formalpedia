-- Prove2me | solution 1 for Lean4LPD.entryFactor_nonneg_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:03:33.640355+00:00
-- url     : https://prove2.me/submissions/aaa6c501-2882-4b65-a176-f5630530a0c1

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Truncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerLadder
public import Theorems.Thm_Lean4LPD_epsJump_nonneg_all

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {kh1 c a : ℝ} (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (m : ℕ) : 0 ≤ entryFactor kh1 c a m :=
  tsum_nonneg fun i => epsJump_nonneg_all hkh hc ha (m + i) m
end Lean4LPD
