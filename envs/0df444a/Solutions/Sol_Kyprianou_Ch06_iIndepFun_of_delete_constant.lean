-- Prove2me | solution 1 for Kyprianou.Ch06.iIndepFun_of_delete_constant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:30:14.408793+00:00
-- url     : https://prove2.me/submissions/229485f5-06ed-4ad6-a746-dc528c96ec65

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory

/-- Extend finite-dimensional rectangle independence across a single
deterministic zero coordinate without changing the nonzero family. -/
theorem solution
    {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) (hprob : P Set.univ = 1)
    (f : ι → Ω → Real) (k : ι)
    (hconst : f k = fun _ => 0)
    (hrest : ∀ (S : Finset ι), k ∉ S →
      ∀ (A : ι → Set Real), (∀ i ∈ S, MeasurableSet (A i)) →
      P (⋂ i ∈ S, f i ⁻¹' A i) =
        ∏ i ∈ S, P (f i ⁻¹' A i)) :
    ProbabilityTheory.iIndepFun f P := by
  classical
  rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S A hA
  by_cases hk : k ∈ S
  · have hS : S = insert k (S.erase k) := (Finset.insert_erase hk).symm
    have hnot : k ∉ S.erase k := by simp
    have hrect := hrest (S.erase k) hnot A (by
      intro i hi
      exact hA i (Finset.mem_of_mem_erase hi))
    rw [hS, Finset.prod_insert hnot]
    have hinter :
        (⋂ i ∈ insert k (S.erase k), f i ⁻¹' A i) =
          (f k ⁻¹' A k) ∩ (⋂ i ∈ S.erase k, f i ⁻¹' A i) := by
      ext ω
      simp [Finset.mem_insert]
    rw [hinter]
    by_cases hv : (0 : Real) ∈ A k
    · have hfull : f k ⁻¹' A k = (Set.univ : Set Ω) := by
        ext ω
        simp [hconst, hv]
      rw [hfull, Set.univ_inter, hrect]
      simp [hfull, hprob]
    · have hempty : f k ⁻¹' A k = (∅ : Set Ω) := by
        ext ω
        simp [hconst, hv]
      rw [hempty, Set.empty_inter, measure_empty]
      simp [hempty]
  · exact hrest S hk A hA
