-- Prove2me | solution 1 for Kac.setOf_lt_returnTime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:16:04.407854+00:00
-- url     : https://prove2.me/submissions/a0d571c2-df7e-4622-986f-45fcb704bd56

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
public import Theorems.Thm_Kac_notYet_zero
public import Theorems.Thm_Kac_notYet_succ
public import Theorems.Thm_Kac_lt_returnTime_iff
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
theorem _root_.solution (n : ℕ) :
    {x | (n : ℕ∞) < returnTime f A x} = f ⁻¹' notYet f A n := by
  ext x
  simp only [mem_ofPred_eq, mem_preimage, lt_returnTime_iff]
end Kac
