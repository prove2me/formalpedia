-- Prove2me | solution 1 for Kac.notYet_eq_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:15:53.765333+00:00
-- url     : https://prove2.me/submissions/fc8b3284-249d-446e-9c49-81d68007b335

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
public import Theorems.Thm_P2M_Kac_notYet_succ__e7ce5a310839

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory Topology
open scoped ENNReal
open Kac
variable {α : Type*} {f : α → α} {A : Set α}
namespace Kac
theorem _root_.solution (n : ℕ) : notYet f A n = firstHit f A n ∪ notYet f A (n + 1) := by
  rw [notYet_succ', firstHit, ← inter_union_distrib_left, union_compl_self, inter_univ]
end Kac
