-- Prove2me | solution 1 for IdealInvariant.non_le_non
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:33:46.0268+00:00
-- url     : https://prove2.me/submissions/246172fc-b690-4f3c-bf8d-70483acfbd6c

module
public import Mathlib.SetTheory.Cardinal.Basic
public import Definitions.Def_AddUN_IdealInvariant
public import Theorems.Thm_IdealInvariant_non_le
public import Theorems.Thm_IdealInvariant_exists_notMem_mk_eq_non

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Set
open IdealInvariant
variable {X : Type u} {I : Set (Set X)} {𝒜 : Set (Set X)} {A : Set X}
namespace IdealInvariant
theorem _root_.solution {J : Set (Set X)} (hIJ : I ⊆ J) (hJ : ∃ A, A ∉ J) : non I ≤ non J := by
  obtain ⟨A, hA, hcard⟩ := exists_notMem_mk_eq_non hJ
  exact hcard ▸ non_le fun h ↦ hA (hIJ h)
end IdealInvariant
