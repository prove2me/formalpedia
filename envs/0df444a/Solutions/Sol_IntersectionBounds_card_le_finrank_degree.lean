-- Prove2me | solution 1 for IntersectionBounds.card_le_finrank_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:58:17.877422+00:00
-- url     : https://prove2.me/submissions/1fa9a9df-d5a5-45c7-84e9-d3b149b069f5

module
public import Definitions.Def_IntersectionBounds_EvaluationSpace
public import Definitions.Def_IntersectionBounds_Separation
public import Theorems.Thm_IntersectionBounds_separator_linearIndependent
public import Theorems.Thm_IntersectionBounds_separator_mem_degree


set_option autoImplicit true
@[expose] public section
public section
open IntersectionBounds
open Finset Submodule
universe u v
variable {V : Type u} {K : Type v} [Field K]
variable (F : Finset (Finset V)) (L : Finset K)
open Classical
namespace IntersectionBounds
theorem _root_.solution
    (hself : ∀ A ∈ F, (A.card : K) ∉ L)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ((A ∩ B).card : K) ∈ L) :
    F.card ≤ Module.finrank K (degreeSpace (K := K) F L.card) := by
  classical
  let f : F → (F → K) := fun A => separator F L A.val
  have hli : LinearIndependent K f := separator_linearIndependent F L hself hinter
  have hspan : span K (Set.range f) ≤ degreeSpace F L.card := by
    apply Submodule.span_le.mpr
    rintro _ ⟨A, rfl⟩
    exact separator_mem_degree F L A.val
  calc
    _ = Module.finrank K (span K (Set.range f)) := by
      rw [finrank_span_eq_card hli, Fintype.card_coe]
    _ ≤ _ := Submodule.finrank_mono hspan
end IntersectionBounds
