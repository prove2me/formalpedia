-- Prove2me | solution 1 for Kyprianou.Ch04.physicalPastEventIntervalIncrementV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:38:49.222974+00:00
-- url     : https://prove2.me/submissions/6791c243-9317-4bb6-a6f4-dd567bdb92fe

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

/-- A past-event and future-interval mask extracts exactly the weighted increment. -/
theorem solution {Ω : Type} (R : Measure (ℝ × ℝ)) (s t : NNReal) (hst : s ≤ t)
    (A : Set Ω) (g : (NNReal × Ω) × ℝ → ℝ) (ω : Ω)
    (hi : IntegrableOn (fun z : ℝ × ℝ => g ((z.1.toNNReal,ω),z.2))
      (Icc (0 : ℝ) (t : ℝ) ×ˢ univ) R) :
    (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ),
      (((Ioc s t ×ˢ A) ×ˢ (univ : Set ℝ)).indicator g) ((z.1.toNNReal,ω),z.2) ∂ R) =
    A.indicator (fun _ =>
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ),
        g ((z.1.toNNReal,ω),z.2) ∂ R) -
      ∫ z in Icc (0 : ℝ) (s : ℝ) ×ˢ (univ : Set ℝ),
        g ((z.1.toNNReal,ω),z.2) ∂ R) ω := by
  classical
  let U (a : NNReal) := Icc (0 : ℝ) (a : ℝ) ×ˢ (univ : Set ℝ)
  let k := fun z : ℝ × ℝ => g ((z.1.toNNReal,ω),z.2)
  by_cases hA : ω ∈ A
  · rw [indicator_of_mem hA]
    have hD : U t \ U s = Ioc (s : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ) := by
      ext z
      simp only [U,mem_diff,mem_prod,mem_univ,and_true,mem_Icc,mem_Ioc,not_and_or,not_le]
      constructor
      · rintro ⟨⟨hz,ht⟩,hz'|hs⟩
        · exact False.elim (not_lt_of_ge hz hz')
        · exact ⟨hs,ht⟩
      · rintro ⟨hs,ht⟩
        exact ⟨⟨le_trans s.coe_nonneg hs.le,ht⟩,Or.inr hs⟩
    have he : (fun z : ℝ × ℝ =>
      (((Ioc s t ×ˢ A) ×ˢ (univ : Set ℝ)).indicator g) ((z.1.toNNReal,ω),z.2)) =
      (U t \ U s).indicator k := by
      funext z
      have hmem : ((z.1.toNNReal,ω),z.2) ∈ ((Ioc s t ×ˢ A) ×ˢ (univ : Set ℝ)) ↔
          z ∈ U t \ U s := by
        rw [hD]
        simp [hA,Real.lt_toNNReal_iff_coe_lt,Real.toNNReal_le_iff_le_coe]
      by_cases hz : z ∈ U t \ U s
      · rw [indicator_of_mem (hmem.mpr hz),indicator_of_mem hz]
      · rw [indicator_of_notMem (fun h => hz (hmem.mp h)),indicator_of_notMem hz]
    rw [he,integral_indicator (measurableSet_Icc.prod MeasurableSet.univ |>.diff
      (measurableSet_Icc.prod MeasurableSet.univ)),Measure.restrict_restrict
      (measurableSet_Icc.prod MeasurableSet.univ |>.diff (measurableSet_Icc.prod MeasurableSet.univ)),
      inter_eq_left.mpr diff_subset]
    exact setIntegral_sdiff (measurableSet_Icc.prod MeasurableSet.univ) hi
      (Set.prod_mono (Icc_subset_Icc_right (by exact_mod_cast hst)) subset_rfl)
  · rw [indicator_of_notMem hA]
    have he : (fun z : ℝ × ℝ =>
        (((Ioc s t ×ˢ A) ×ˢ (univ : Set ℝ)).indicator g) ((z.1.toNNReal,ω),z.2)) =
        fun _ => 0 := by
      funext z
      exact indicator_of_notMem (fun h => hA h.1.2) _
    rw [he,integral_zero]
