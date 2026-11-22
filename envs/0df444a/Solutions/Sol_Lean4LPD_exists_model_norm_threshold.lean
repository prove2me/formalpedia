-- Prove2me | solution 1 for Lean4LPD.exists_model_norm_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:45.992782+00:00
-- url     : https://prove2.me/submissions/e19d6d16-dec2-4995-9cc1-ca3b8f007879

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Threshold
public import Theorems.Thm_Lean4LPD_exists_norm_threshold
public import Theorems.Thm_Lean4LPD_decayBase_lt_one
public import Theorems.Thm_Lean4LPD_decayBase_nonneg


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Filter
open scoped Topology
namespace Lean4LPD
theorem _root_.solution {G kh α t c M ε : ℝ}
    (hG : 0 < G) (hkh : 1 < kh) (hα : 0 < α) (ht : 0 ≤ t)
    (htime : t < tZeroModel G kh α) (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧ decayBase G kh α t ^ (m + 1) *
      (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M ≤ ε :=
  exists_norm_threshold (decayBase_nonneg hG hkh hα ht)
    (decayBase_lt_one hG hkh hα htime) c M hε
end Lean4LPD
