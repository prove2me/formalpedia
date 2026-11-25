-- Prove2me | solution 1 for IntersectionBounds.extension_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:49:57.866118+00:00
-- url     : https://prove2.me/submissions/93d895d4-b3f4-47a7-8851-82a09e8f8f7f

module
public import Definitions.Def_IntersectionBounds_EvaluationSpace
public import Definitions.Def_IntersectionBounds_Definitions
public import Definitions.Def_IntersectionBounds_UniformSpace
public import Theorems.Thm_IntersectionBounds_indicator_empty
attribute [local simp] IntersectionBounds.indicator_empty



set_option autoImplicit true
@[expose] public section
public section
open IntersectionBounds
open Finset Submodule
universe u v
variable {V : Type u} [Fintype V] {K : Type v} [Field K]
variable (F : Finset (Finset V))
open Classical
namespace IntersectionBounds
theorem _root_.solution (k : ℕ) (huni : Uniform F k) (T : Finset V) :
    ((k : K) - T.card) • (indicator F T : F → K) =
      ∑ a ∈ (univ \ T), indicator F (insert a T) := by
  classical
  funext B
  by_cases hT : T ⊆ B.val
  · simp only [Pi.smul_apply, indicator, if_pos hT, smul_eq_mul, mul_one, Finset.sum_apply]
    have hsets : (univ \ T).filter (fun a => insert a T ⊆ B.val) = B.val \ T := by
      ext a
      simp [Finset.insert_subset_iff, hT, and_comm]
    rw [Finset.sum_boole, hsets, Finset.card_sdiff_of_subset hT,
      Nat.cast_sub (Finset.card_le_card hT), huni B.val B.property]
  · have hall (a : V) : ¬ insert a T ⊆ B.val :=
      fun h => hT ((Finset.subset_insert a T).trans h)
    simp [indicator, hT, hall]
end IntersectionBounds
