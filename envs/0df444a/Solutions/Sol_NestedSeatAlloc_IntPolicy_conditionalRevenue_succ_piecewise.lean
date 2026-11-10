-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.conditionalRevenue_succ_piecewise
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T16:32:52.143982+00:00
-- url     : https://prove2.me/submissions/75b6c345-83d9-4209-8025-4303f4d89499

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option autoImplicit false

section HelpersBB63
open NestedSeatAlloc.IntPolicy MeasureTheory ProbabilityTheory

theorem indep_const_bb63 :
    iIndepFun (fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) (Measure.dirac ()) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  by_cases h : ∀ i ∈ S, (1 : ℝ) ∈ sets i
  · have hL : (⋂ i ∈ S, (fun (_ : Unit) => (1 : ℝ)) ⁻¹' sets i) = Set.univ := by
      ext u
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_univ, iff_true]
      exact h
    rw [hL, measure_univ]
    symm
    apply Finset.prod_eq_one
    intro i hi
    have : (fun (_ : Unit) => (1 : ℝ)) ⁻¹' sets i = Set.univ := by
      ext u; simp [h i hi]
    rw [this, measure_univ]
  · push_neg at h
    obtain ⟨i, hi, hni⟩ := h
    have hL : (⋂ i ∈ S, (fun (_ : Unit) => (1 : ℝ)) ⁻¹' sets i) = ∅ := by
      ext u
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      intro hall
      exact hni (hall i hi)
    rw [hL, measure_empty]
    symm
    apply Finset.prod_eq_zero hi
    have : (fun (_ : Unit) => (1 : ℝ)) ⁻¹' sets i = ∅ := by
      ext u; simp [hni]
    rw [this, measure_empty]

noncomputable def fare_bb63 : ℕ → ℝ := fun k => 3 - (k : ℝ)

noncomputable def prot_bb63 : ℕ → ℝ := fun _ => 1

theorem seatModel_bb63 :
    IsSeatModel (Measure.dirac ()) (fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) fare_bb63 where
  isProb := inferInstance
  meas := fun _ => measurable_const
  indep := indep_const_bb63
  nonneg := fun _ _ => zero_le_one
  fare_strictAnti := fun k _ => by
    simp only [fare_bb63]
    push_cast
    linarith

theorem policy_bb63 : IsProtectionPolicy prot_bb63 :=
  fun _ _ => zero_le_one

end HelpersBB63

open NestedSeatAlloc.IntPolicy MeasureTheory ProbabilityTheory in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (k : ℕ) (y s : ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p) (hy : 0 ≤ y),
    condRevenue P X f p (k + 1) y s =
      (if s < p k then condRevenue P X f p k y s
       else if s < p k + y then (s - p k) * f (k + 1) + condRevenue P X f p k y (p k)
       else y * f (k + 1) + condRevenue P X f p k y (s - y))) := by
  intro h
  have h1 := h (Measure.dirac ()) (fun (_ : ℕ) (_ : Unit) => (1 : ℝ))
    fare_bb63 prot_bb63 1 0 (1 / 2) seatModel_bb63 policy_bb63 le_rfl
  simp only [condRevenue, integral_dirac, revenue, fare_bb63, prot_bb63, Function.update] at h1
  norm_num at h1
