-- Prove2me | solution 1 for Kac.inter_lt_returnTime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:24:31.298044+00:00
-- url     : https://prove2.me/submissions/86c65ea5-6030-4ade-bf45-e67c22b8b4ec

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
public import Theorems.Thm_Kac_setOf_lt_returnTime

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory Topology
open scoped ENNReal
open Kac
variable {α : Type*} {f : α → α} {A : Set α}
namespace Kac
theorem _root_.solution (n : ℕ) :
    A ∩ {x | (n : ℕ∞) < returnTime f A x} = A ∩ f ⁻¹' notYet f A n := by
  rw [setOf_lt_returnTime]
end Kac
