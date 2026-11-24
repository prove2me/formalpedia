-- Prove2me | solution 1 for IdealInvariant.cof_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:33:36.280611+00:00
-- url     : https://prove2.me/submissions/9b86821b-3601-4dc8-b412-5d5afee8ca32

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
theorem _root_.solution (h𝒜 : 𝒜 ⊆ I) (hcof : ∀ A ∈ I, ∃ B ∈ 𝒜, A ⊆ B) : cof I ≤ #𝒜 :=
  ciInf_le' (fun 𝒜 : {𝒜 : Set (Set X) // 𝒜 ⊆ I ∧ ∀ A ∈ I, ∃ B ∈ 𝒜, A ⊆ B} ↦ #𝒜.1)
    ⟨𝒜, h𝒜, hcof⟩
end IdealInvariant
