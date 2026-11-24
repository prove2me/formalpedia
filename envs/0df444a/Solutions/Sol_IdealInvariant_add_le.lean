-- Prove2me | solution 1 for IdealInvariant.add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:20:24.701304+00:00
-- url     : https://prove2.me/submissions/3d514a84-707a-4cc6-b52b-e88a522f1c43

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
theorem _root_.solution (h𝒜 : 𝒜 ⊆ I) (hU : ⋃₀ 𝒜 ∉ I) : add I ≤ #𝒜 :=
  ciInf_le' (fun 𝒜 : {𝒜 : Set (Set X) // 𝒜 ⊆ I ∧ ⋃₀ 𝒜 ∉ I} ↦ #𝒜.1) ⟨𝒜, h𝒜, hU⟩
end IdealInvariant
