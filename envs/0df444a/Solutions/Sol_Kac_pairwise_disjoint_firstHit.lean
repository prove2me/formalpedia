-- Prove2me | solution 1 for Kac.pairwise_disjoint_firstHit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:12:29.07447+00:00
-- url     : https://prove2.me/submissions/4a2f234b-a54a-4ab7-8589-adbce91b7557

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
theorem _root_.solution :
    Pairwise fun m n : ℕ => Disjoint (firstHit f A m) (firstHit f A n) := by
  intro m n hmn
  rcases Nat.lt_or_gt_of_ne hmn with h | h
  · exact Set.disjoint_left.mpr fun x hm hn => (mem_notYet_iff n x).mp hn.1 m h hm.2
  · exact Set.disjoint_left.mpr fun x hm hn => (mem_notYet_iff m x).mp hm.1 n h hn.2
end Kac
