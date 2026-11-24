-- Prove2me | solution 1 for IdealInvariant.exists_notMem_mk_eq_non
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:20:39.848521+00:00
-- url     : https://prove2.me/submissions/9d25947c-958e-4853-aeea-1170a5e51153

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
theorem _root_.solution (hI : ∃ A, A ∉ I) : ∃ A, A ∉ I ∧ #A = non I := by
  obtain ⟨A, hA⟩ := hI
  have : Nonempty {A : Set X // A ∉ I} := ⟨⟨A, hA⟩⟩
  obtain ⟨⟨B, hB⟩, h⟩ := ciInf_mem fun A : {A : Set X // A ∉ I} ↦ #A.1
  exact ⟨B, hB, h⟩
end IdealInvariant
