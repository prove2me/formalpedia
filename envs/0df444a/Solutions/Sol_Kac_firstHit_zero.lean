-- Prove2me | solution 1 for Kac.firstHit_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:16:32.21518+00:00
-- url     : https://prove2.me/submissions/765d9d9c-0530-49fa-991c-5ad51516c77b

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
public import Theorems.Thm_Kac_notYet_zero
public import Theorems.Thm_Kac_notYet_succ
attribute [local simp] Kac.notYet_zero
attribute [local simp] Kac.notYet_succ

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory Topology
open scoped ENNReal
open Kac
variable {α : Type*} {f : α → α} {A : Set α}
namespace Kac
theorem _root_.solution : firstHit f A 0 = A := by
  simp [firstHit]
end Kac
