-- Prove2me | solution 1 for IdealInvariant.sUnion_mem_of_lt_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:33:39.371299+00:00
-- url     : https://prove2.me/submissions/4861e6dc-c0d0-4402-8033-d3a77fcd0051

module
public import Mathlib.SetTheory.Cardinal.Basic
public import Definitions.Def_AddUN_IdealInvariant
public import Theorems.Thm_IdealInvariant_add_le

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Set
open IdealInvariant
variable {X : Type u} {I : Set (Set X)} {𝒜 : Set (Set X)} {A : Set X}
namespace IdealInvariant
theorem _root_.solution (h𝒜 : 𝒜 ⊆ I) (h : #𝒜 < add I) : ⋃₀ 𝒜 ∈ I :=
  by_contra fun hU ↦ (add_le h𝒜 hU).not_gt h
end IdealInvariant
