-- Prove2me | solution 1 for Kyprianou.Ch06.iIndepFun_constZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:25:58.639539+00:00
-- url     : https://prove2.me/submissions/355f6a0e-cdf7-4e8e-af04-6c71d9c716c8

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
/-- A finite collection of identically zero random variables is independent. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (hprob : P Set.univ = 1) (n : Nat) :
    ProbabilityTheory.iIndepFun (fun _ : Fin n => fun _ : Ω => (0 : Real)) P := by
  classical
  rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  by_cases h : ∀ i ∈ S, (0 : Real) ∈ sets i
  · have hleft :
        (⋂ i ∈ S, (fun _ : Ω => (0 : Real)) ⁻¹' sets i) = Set.univ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_univ, iff_true]
      intro j hj
      exact h j hj
    have hright : ∀ i ∈ S, P ((fun _ : Ω => (0 : Real)) ⁻¹' sets i) = 1 := by
      intro i hi
      simp [h i hi, hprob]
    rw [hleft, hprob]
    exact Finset.prod_eq_one hright |>.symm
  · push_neg at h
    obtain ⟨i, hi, hnot⟩ := h
    have hevent :
        (⋂ i ∈ S, (fun _ : Ω => (0 : Real)) ⁻¹' sets i) = ∅ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      intro hall
      exact hnot (hall i hi)
    rw [hevent, measure_empty]
    exact (Finset.prod_eq_zero hi (by simp [hnot])).symm
