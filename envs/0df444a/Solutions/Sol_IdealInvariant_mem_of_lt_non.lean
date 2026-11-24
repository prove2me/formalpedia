-- Prove2me | solution 1 for IdealInvariant.mem_of_lt_non
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:26:45.068807+00:00
-- url     : https://prove2.me/submissions/f7f70934-9308-4a0d-8f17-84b5d59f8cb1

module
public import Mathlib.SetTheory.Cardinal.Basic
public import Definitions.Def_AddUN_IdealInvariant
public import Theorems.Thm_IdealInvariant_non_le

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Set
open IdealInvariant
variable {X : Type u} {I : Set (Set X)} {𝒜 : Set (Set X)} {A : Set X}
namespace IdealInvariant
theorem _root_.solution (h : #A < non I) : A ∈ I :=
  by_contra fun hA ↦ (non_le hA).not_gt h
end IdealInvariant
