-- Prove2me | solution 1 for IdealInvariant.exists_sUnion_notMem_mk_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:36:12.676433+00:00
-- url     : https://prove2.me/submissions/e6d86dfd-7967-4a35-beee-7a76f6526629

module
public import Definitions.Def_AddUN_CantorMeasure
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Topology.Separation.Profinite
public import Definitions.Def_AddUN_Localisation

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open IdealInvariant
universe u
variable {X : Type u} {I : Set (Set X)}
namespace IdealInvariant
theorem _root_.solution (hI : ∃ 𝒜 ⊆ I, ⋃₀ 𝒜 ∉ I) :
    ∃ 𝒜 ⊆ I, ⋃₀ 𝒜 ∉ I ∧ #𝒜 = add I := by
  obtain ⟨𝒜, h𝒜, hU⟩ := hI
  have : Nonempty {𝒜 : Set (Set X) // 𝒜 ⊆ I ∧ ⋃₀ 𝒜 ∉ I} := ⟨⟨𝒜, h𝒜, hU⟩⟩
  obtain ⟨⟨ℬ, hℬ, hV⟩, h⟩ :=
    ciInf_mem fun 𝒜 : {𝒜 : Set (Set X) // 𝒜 ⊆ I ∧ ⋃₀ 𝒜 ∉ I} ↦ #𝒜.1
  exact ⟨ℬ, hℬ, hV, h⟩
end IdealInvariant
