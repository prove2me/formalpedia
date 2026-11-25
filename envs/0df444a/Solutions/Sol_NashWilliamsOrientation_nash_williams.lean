-- Prove2me | solution 1 for NashWilliamsOrientation.nash_williams
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:48:23.872294+00:00
-- url     : https://prove2.me/submissions/b46086d1-03e5-4391-a6b6-be072ba18d69

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Defs
public import Definitions.Def_NashWilliamsOrientation_Solution
public import Theorems.Thm_NashWilliams_nash_williams


set_option autoImplicit true
@[expose] public section
public section
open NashWilliamsOrientation
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
namespace NashWilliamsOrientation
theorem _root_.solution (k : ℕ) (ends : ι → V × V) (hloop : ∀ i, (ends i).1 ≠ (ends i).2)
    (hconn : ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → 2 * k ≤ cut ends S) :
    ∃ o : ι → Bool, ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → k ≤ outCut ends o S :=
  NashWilliams.nash_williams k ends hloop hconn
end NashWilliamsOrientation
