-- Prove2me | solution 1 for LatinQuarter.cyclic_scs_eq_quarter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:49.27191+00:00
-- url     : https://prove2.me/submissions/39204d0c-eb73-4b8b-9c9f-b96fcc13d198

module
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Definitions.Def_LeanPool_LatinQuarter_LowerBound
public import Definitions.Def_LeanPool_LatinQuarter_CornerSize
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Theorems.Thm_LatinQuarter_critical_set_lower_bound
public import Theorems.Thm_LatinQuarter_cornerSet_card
public import Theorems.Thm_LatinQuarter_cornerSet_isCritical

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
namespace LatinQuarter
theorem _root_.solution (n : ℕ) (hn : 0 < n) :
    scsOf (cyclic n) = n * n / 4 := by
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨cornerSet n, cornerSet_isCritical n hn, cornerSet_card n hn⟩
  · rintro m ⟨P, hP, rfl⟩
    exact critical_set_lower_bound P (cyclic n) hP
end LatinQuarter
