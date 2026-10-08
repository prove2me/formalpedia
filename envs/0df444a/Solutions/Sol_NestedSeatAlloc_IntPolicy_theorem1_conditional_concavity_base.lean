-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.theorem1_conditional_concavity_base
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:45:21.302779+00:00
-- url     : https://prove2.me/submissions/bb753c93-a3a6-4c4e-82af-9716ad1a7c84

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option autoImplicit false

namespace NSA9c8Cex

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem indep_unit (X : ℕ → Unit → ℝ) :
    iIndepFun X (Measure.dirac () : Measure Unit) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  by_cases h : ∀ i ∈ S, () ∈ X i ⁻¹' sets i
  · have h1 : () ∈ ⋂ i ∈ S, X i ⁻¹' sets i := by
      simp only [Set.mem_iInter]; exact h
    rw [Measure.dirac_apply' _ (MeasurableSet.of_discrete), Set.indicator_of_mem h1]
    symm
    apply Finset.prod_eq_one
    intro i hi
    rw [Measure.dirac_apply' _ (MeasurableSet.of_discrete), Set.indicator_of_mem (h i hi)]
    rfl
  · push Not at h
    obtain ⟨i, hi, hni⟩ := h
    have h1 : () ∉ ⋂ i ∈ S, X i ⁻¹' sets i := by
      simp only [Set.mem_iInter, not_forall]; exact ⟨i, hi, hni⟩
    rw [Measure.dirac_apply' _ (MeasurableSet.of_discrete), Set.indicator_of_notMem h1]
    symm
    apply Finset.prod_eq_zero hi
    rw [Measure.dirac_apply' _ (MeasurableSet.of_discrete), Set.indicator_of_notMem hni]

theorem model : IsSeatModel (Measure.dirac () : Measure Unit) (fun _ _ => (0 : ℝ))
    (fun k => -(k : ℝ)) where
  isProb := inferInstance
  meas := fun _ => measurable_const
  indep := indep_unit _
  nonneg := fun _ _ => le_refl _
  fare_strictAnti := fun k _ => by push_cast; linarith

theorem policy : IsProtectionPolicy (fun _ => (0 : ℝ)) := fun _ _ => le_refl _

theorem cr_eval (s : ℝ) :
    condRevenue (Measure.dirac () : Measure Unit) (fun _ _ => (0 : ℝ)) (fun k => -(k : ℝ))
      (fun _ => (0 : ℝ)) 1 1 s = if s < 1 then -1 * s else -1 * 1 := by
  unfold condRevenue
  rw [integral_dirac]
  simp [revenue]

theorem cex : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (_hM : IsSeatModel P X f)
    (_hp : IsProtectionPolicy p),
    ∀ y, 0 ≤ y → ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p 1 y)) := by
  intro h
  have hc := h (Measure.dirac () : Measure Unit) (fun _ _ => (0 : ℝ)) (fun k => -(k : ℝ))
    (fun _ => (0 : ℝ)) model policy 1 zero_le_one
  have h0 : (0:ℝ) ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr (le_refl _)
  have h2 : (2:ℝ) ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr (by norm_num)
  have := hc.2 h0 h2
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (show (1/2:ℝ) + 1/2 = 1 by norm_num)
  simp only [smul_eq_mul, cr_eval] at this
  norm_num at this

end NSA9c8Cex

open MeasureTheory ProbabilityTheory in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (_hM : NestedSeatAlloc.IntPolicy.IsSeatModel P X f)
    (_hp : NestedSeatAlloc.IntPolicy.IsProtectionPolicy p),
    ∀ y, 0 ≤ y → ConcaveOn ℝ (Set.Ici 0) (NestedSeatAlloc.IntPolicy.condRevenue P X f p 1 y)) := by
  exact NSA9c8Cex.cex
