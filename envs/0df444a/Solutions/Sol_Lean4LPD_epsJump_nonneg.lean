-- Prove2me | solution 1 for Lean4LPD.epsJump_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:58:56.435616+00:00
-- url     : https://prove2.me/submissions/01e48b65-7672-495c-b096-13f199bf2eff

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
public import Theorems.Thm_Lean4LPD_rungW_nonneg

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {kh1 c a : ℝ} (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) (j nu : ℕ)
    (h : 1 ≤ nu + j) : 0 ≤ epsJump kh1 c a j nu := by
  have hW := rungW_nonneg hkh hc h
  have hfac : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
  unfold epsJump
  positivity
end Lean4LPD
