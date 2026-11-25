-- Prove2me | solution 1 for Kac.antitone_notYet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:12:21.103481+00:00
-- url     : https://prove2.me/submissions/b1c4716c-2999-4da4-b469-8ed290365c4f

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
public import Theorems.Thm_Kac_mem_notYet_iff

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory Topology
open scoped ENNReal
open Kac
variable {α : Type*} {f : α → α} {A : Set α}
namespace Kac
theorem _root_.solution : Antitone (notYet f A) := by
  intro m n hmn x hx
  rw [mem_notYet_iff] at hx ⊢
  exact fun k hk => hx k (by omega)
end Kac
