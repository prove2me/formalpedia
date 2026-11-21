-- Prove2me | solution 1 for MiLAC.interconnection_eq_phaseShifter_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:36:21.470473+00:00
-- url     : https://prove2.me/submissions/7b13c4e0-6b32-478f-93cb-cbed3c1d00f4

module
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.PEquiv
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic

set_option autoImplicit true
@[expose] public section
public section
open MiLAC
namespace MiLAC
theorem _root_.solution :
    interconnection = phaseShifter 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [interconnection, phaseShifter]
end MiLAC
