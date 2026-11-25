-- Prove2me | solution 1 for Kac.disjoint_firstHit_notYet_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:16:12.195241+00:00
-- url     : https://prove2.me/submissions/457a8978-8d7f-4f82-bac2-a450a3cbf84f

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
theorem _root_.solution (n : ℕ) : Disjoint (firstHit f A n) (notYet f A (n + 1)) := by
  rw [notYet_succ']
  exact Set.disjoint_left.mpr fun x hx hx' => hx'.2 hx.2
end Kac
