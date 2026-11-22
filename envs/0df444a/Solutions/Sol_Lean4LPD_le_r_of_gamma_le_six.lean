-- Prove2me | solution 1 for Lean4LPD.le_r_of_gamma_le_six
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:04:53.075798+00:00
-- url     : https://prove2.me/submissions/bcb7b36f-9754-4d74-99ce-6e6cdc5cf65b

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real
namespace Lean4LPD
theorem _root_.solution {r m G : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m) (hG6 : G ≤ 6) :
    5 ≤ r := by
  obtain ⟨hr, hm, hG, _, hrG⟩ := h
  nlinarith only [hrG, hm1, hr, hG6, sq_nonneg (m - 1)]
end Lean4LPD
