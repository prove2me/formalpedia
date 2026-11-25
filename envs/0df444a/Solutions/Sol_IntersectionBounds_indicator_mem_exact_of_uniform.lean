-- Prove2me | solution 1 for IntersectionBounds.indicator_mem_exact_of_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:54:40.602849+00:00
-- url     : https://prove2.me/submissions/a1497f53-5cd4-4013-b505-d74ca93cdb46

module
public import Definitions.Def_IntersectionBounds_EvaluationSpace
public import Definitions.Def_IntersectionBounds_Definitions
public import Definitions.Def_IntersectionBounds_UniformSpace
public import Theorems.Thm_IntersectionBounds_extension_identity
public import Theorems.Thm_IntersectionBounds_indicator_empty
public import Theorems.Thm_IntersectionBounds_indicator_mem_exact
attribute [local simp] IntersectionBounds.indicator_empty



set_option autoImplicit true
@[expose] public section
public section
open IntersectionBounds
open Finset Submodule
universe u v
variable {V : Type u} [Fintype V] {K : Type v} [Field K]
variable (F : Finset (Finset V))
namespace IntersectionBounds
theorem _root_.solution [CharZero K] (k s : ℕ)
    (huni : Uniform F k) (hs : s ≤ k) (T : Finset V) (hT : T.card ≤ s) :
    (indicator F T : F → K) ∈ exactSpace F s := by
  classical
  have aux : ∀ d : ℕ, ∀ T : Finset V, T.card ≤ s → s - T.card = d →
      (indicator F T : F → K) ∈ exactSpace F s := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro T hT hd
      by_cases heq : T.card = s
      · exact indicator_mem_exact F T s heq
      have hlt : T.card < s := by omega
      have hcoef : (k : K) - T.card ≠ 0 := by
        apply sub_ne_zero.mpr
        exact_mod_cast (show k ≠ T.card by omega)
      have hsum : (∑ a ∈ (univ \ T), indicator F (insert a T) : F → K) ∈
          exactSpace F s := by
        apply Submodule.sum_mem
        intro a ha
        have hnot := (Finset.mem_sdiff.mp ha).2
        have hcard := Finset.card_insert_of_notMem hnot
        apply ih (s - (insert a T).card) (by omega) (insert a T) (by omega) rfl
      rw [← extension_identity F k huni T] at hsum
      have h := (exactSpace F s).smul_mem ((k : K) - T.card)⁻¹ hsum
      simpa [smul_smul, hcoef] using h
  exact aux _ T hT rfl
end IntersectionBounds
