-- Prove2me | solution 1 for Kyprianou.Ch04.predictablePositiveTailBox
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:13:49.951341+00:00
-- url     : https://prove2.me/submissions/ffa1a20a-f7d1-4463-aa61-31393ebf2887

import Mathlib
open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

/-- An adapted tail generator within the horizon restricts to a weighted tail box. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (t : NNReal) (B : Set ℝ) (hB : MeasurableSet B)
    (a₀ : NNReal) (A : Set Omega) (hA : MeasurableSet[F a₀] A)
    (C₀ : Set ℝ) (hC : MeasurableSet C₀) (hat : a₀ ≤ t)
    (c : ℝ) :
    ∃ (a : NNReal) (C : Set ℝ) (H : Omega → ℝ),
      a ≤ t ∧ MeasurableSet C ∧ C ⊆ B ∧ StronglyMeasurable[F a] H ∧
      (∀ w, |H w| ≤ |c|) ∧
      ∀ (w : Omega) (z : ℝ × ℝ), z.1 ≠ 0 →
        (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B).indicator
          (fun z => c * ((Set.Ioi a₀ ×ˢ A) ×ˢ C₀).indicator (fun _ => (1 : ℝ)) ((z.1.toNNReal,w),z.2)) z =
        (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ C).indicator (fun _ => H w) z := by
  classical
  let H : Omega → ℝ := A.indicator (fun _ => c)
  refine ⟨a₀, B ∩ C₀, H, hat, hB.inter hC, Set.inter_subset_left,
    stronglyMeasurable_const.indicator hA, ?_, ?_⟩
  · intro w
    by_cases hw : w ∈ A <;> simp [H, hw, abs_nonneg]
  · intro w z hz
    by_cases hu : z ∈ Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B
    · have hz0 := hu.1.1
      have hzle := hu.1.2
      have hco : (z.1.toNNReal : ℝ) = z.1 := Real.coe_toNNReal _ hz0
      by_cases ha : (a₀ : ℝ) < z.1 <;> by_cases hw : w ∈ A <;> by_cases hc : z.2 ∈ C₀ <;>
        simp [Set.indicator, hu, H, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioc,
          Set.mem_inter_iff, ← NNReal.coe_lt_coe, hco, ha, hw, hc, hu.2, hzle]
    · have hn : z ∉ Set.Ioc (a₀ : ℝ) (t : ℝ) ×ˢ (B ∩ C₀) :=
        fun h => hu ⟨⟨(NNReal.coe_nonneg a₀).trans h.1.1.le,h.1.2⟩,h.2.1⟩
      simp [Set.indicator_of_notMem hu, Set.indicator_of_notMem hn]
