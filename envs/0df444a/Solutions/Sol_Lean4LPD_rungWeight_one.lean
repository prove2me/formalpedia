-- Prove2me | solution 1 for Lean4LPD.rungWeight_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:58:16.348802+00:00
-- url     : https://prove2.me/submissions/18a169cd-6cf8-4116-9d75-c2e89b8e0d48

module
public import Mathlib.Data.Real.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Defs

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
namespace Lean4LPD
theorem _root_.solution (ko kh : ℕ) : rungWeight ko kh 1 = ko := by
  simp [rungWeight]
end Lean4LPD
