-- Prove2me | solution 1 for Lean4LPD.partFactor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:07:52.260625+00:00
-- url     : https://prove2.me/submissions/1386e838-6b32-495f-99d4-ed11575f9afd

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Theorems.Thm_Lean4LPD_partFactor_antitone
public import Theorems.Thm_Lean4LPD_partFactor_at_diag
public import Theorems.Thm_Lean4LPD_diagFactor_le

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {j : ℕ} {s : ℝ} (hj : 2 ≤ j) (hs : (j : ℝ) ≤ s) :
    partFactor j s ≤ (9 / 4 : ℝ) ^ (j - 1) :=
  calc partFactor j s ≤ partFactor j (j : ℝ) :=
        partFactor_antitone (by omega) (le_refl _) hs
    _ = diagFactor j := partFactor_at_diag j
    _ ≤ (9 / 4 : ℝ) ^ (j - 1) := diagFactor_le j hj
end Lean4LPD
