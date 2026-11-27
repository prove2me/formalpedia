-- Prove2me | solution 1 for Kyprianou.Ch04.clippedGridWindowCellIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:38:44.043957+00:00
-- url     : https://prove2.me/submissions/4f217246-277b-48d0-a797-dd58d6620fbf

import Mathlib
open MeasureTheory Set
open scoped NNReal
set_option autoImplicit false

/-- A right-closed grid cell restricted to the observation window equals the
difference of two nested clipped windows, with no time-zero assumption. -/
theorem solution (R : Measure (ℝ × ℝ)) (Q : ℝ × ℝ → ℝ)
    (T t a b : NNReal) (ht : t ≤ T) (hab : a ≤ b)
    (hQ : IntegrableOn Q (Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ)) R)
    (c : ℝ) :
    (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ),
      (Ioc a b).indicator (fun _ => c) z.1.toNNReal * Q z ∂ R) =
      c * ((∫ z in Icc (0 : ℝ) ((min t b : NNReal) : ℝ) ×ˢ (univ : Set ℝ), Q z ∂ R) -
        ∫ z in Icc (0 : ℝ) ((min t a : NNReal) : ℝ) ×ˢ (univ : Set ℝ), Q z ∂ R) := by
  let D (v : NNReal) := Icc (0 : ℝ) (v : ℝ) ×ˢ (univ : Set ℝ)
  let A := Ioc (a : ℝ) (b : ℝ) ×ˢ (univ : Set ℝ)
  have hA : MeasurableSet A := measurableSet_Ioc.prod MeasurableSet.univ
  have hD (v : NNReal) : MeasurableSet (D v) := measurableSet_Icc.prod MeasurableSet.univ
  have hsub {v u : NNReal} (h : v ≤ u) : D v ⊆ D u := fun z hz =>
    ⟨⟨hz.1.1,hz.1.2.trans (by exact_mod_cast h)⟩,hz.2⟩
  have he : A ∩ D t = D (min t b) \ D (min t a) := by
    ext z
    simp only [A,D,mem_inter_iff,mem_diff,mem_prod,mem_Ioc,mem_Icc,mem_univ,and_true,
      NNReal.coe_min,le_min_iff]
    constructor
    · rintro ⟨⟨ha,hb⟩,h0,ht'⟩
      exact ⟨⟨h0,ht',hb⟩,fun h => (not_le_of_gt ha) h.2.2⟩
    · rintro ⟨⟨h0,ht',hb⟩,h⟩
      exact ⟨⟨lt_of_not_ge (fun h' => h ⟨h0,ht',h'⟩),hb⟩,h0,ht'⟩
  calc
    _ = ∫ z in D t, A.indicator (fun z => c * Q z) z ∂ R := by
      apply setIntegral_congr_fun (hD t)
      intro z hz
      have hpos : 0 ≤ z.1 := hz.1.1
      have hc : z.1.toNNReal ∈ Ioc a b ↔ z ∈ A := by
        simp only [A,mem_prod,mem_Ioc,mem_univ,and_true]
        exact_mod_cast (show (a : ℝ) < (z.1.toNNReal : ℝ) ∧
          (z.1.toNNReal : ℝ) ≤ (b : ℝ) ↔ (a : ℝ) < z.1 ∧ z.1 ≤ (b : ℝ) by
            rw [Real.coe_toNNReal z.1 hpos])
      by_cases h : z ∈ A <;> simp [Set.indicator_apply,h,hc]
    _ = ∫ z in A ∩ D t, c * Q z ∂ R := by
      rw [integral_indicator hA,Measure.restrict_restrict hA]
    _ = c * ((∫ z in D (min t b), Q z ∂ R) - ∫ z in D (min t a), Q z ∂ R) := by
      rw [he,integral_const_mul,setIntegral_diff (hD _) (hQ.mono_set
        (hsub ((min_le_left t b).trans ht))) (hsub (min_le_min_left t hab))]
