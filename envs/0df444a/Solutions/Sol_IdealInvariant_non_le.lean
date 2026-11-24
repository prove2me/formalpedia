-- Prove2me | solution 1 for IdealInvariant.non_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:20:40.404765+00:00
-- url     : https://prove2.me/submissions/62ca579b-3082-4b5c-9d41-31773825c108

module
public import Mathlib.SetTheory.Cardinal.Basic
public import Definitions.Def_AddUN_IdealInvariant

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Set
open IdealInvariant
variable {X : Type u} {I : Set (Set X)} {𝒜 : Set (Set X)} {A : Set X}
namespace IdealInvariant
theorem _root_.solution (hA : A ∉ I) : non I ≤ #A :=
  ciInf_le' (fun A : {A : Set X // A ∉ I} ↦ #A.1) ⟨A, hA⟩
end IdealInvariant
