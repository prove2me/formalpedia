-- Prove2me | solution 1 for Kac.iInter_notYet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:12:12.40481+00:00
-- url     : https://prove2.me/submissions/dbc01a21-1148-40d2-944e-ca2f99475c84

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
public import Theorems.Thm_Kac_notYet_zero
public import Theorems.Thm_Kac_notYet_succ
public import Theorems.Thm_Kac_mem_notYet_iff
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
theorem _root_.solution : ⋂ n, notYet f A n = (⋃ k : ℕ, f^[k] ⁻¹' A)ᶜ := by
  ext x
  simp only [mem_iInter, mem_compl_iff, mem_iUnion, mem_preimage, not_exists]
  constructor
  · intro h k hk
    exact (mem_notYet_iff (k + 1) x).mp (h (k + 1)) k (by omega) hk
  · intro h n
    exact (mem_notYet_iff n x).mpr (fun k _ => h k)
end Kac
