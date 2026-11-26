-- Prove2me | solution 1 for Kyprianou.Ch04.finiteGeneratorSumTailRepresentation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:20:11.025044+00:00
-- url     : https://prove2.me/submissions/079539b4-a588-48cd-b48d-47c5d1eba59f

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_predictableGeneratorTailBox
open MeasureTheory Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- A finite sum of marked predictable generators has a physical tail-box representation. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (t : NNReal) (B : Set ℝ) (hB : MeasurableSet B)
    (k : ℕ) (D : Fin k → Set ((NNReal × Omega) × ℝ)) (c : Fin k → ℝ)
    (hD : ∀ i, D i ∈ insert Set.univ (insert ∅
      (Set.image2 (· ×ˢ ·)
        {S : Set (NNReal × Omega) |
          (∃ A : Set Omega, MeasurableSet[F ⊥] A ∧ S = ({⊥} ×ˢ A)) ∨
          (∃ a : NNReal, ∃ A : Set Omega, MeasurableSet[F a] A ∧ S = (Set.Ioi a ×ˢ A))}
        {C : Set ℝ | MeasurableSet C}))) :
    ∃ (a : Fin k → NNReal) (C : Fin k → Set ℝ) (H : Fin k → Omega → ℝ),
      (∀ i, a i ≤ t) ∧ (∀ i, MeasurableSet (C i)) ∧ (∀ i, C i ⊆ B) ∧
      (∀ i, StronglyMeasurable[F (a i)] (H i)) ∧
      (∀ i, Integrable (fun w => (H i w)^2) P) ∧
      ∀ (w : Omega) (z : ℝ × ℝ), z.1 ≠ 0 →
        (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B).indicator
          (fun z => ∑ i, c i * (D i).indicator (fun _ => (1 : ℝ))
            ((z.1.toNNReal,w),z.2)) z =
        ∑ i, (Set.Ioc (a i : ℝ) (t : ℝ) ×ˢ C i).indicator (fun _ => H i w) z := by
  classical
  choose a C H ha hC hCB hH hb he using
    fun i => Kyprianou.Ch04.predictableGeneratorTailBox F t B hB (D i) (hD i) (c i)
  refine ⟨a,C,H,ha,hC,hCB,hH,?_,?_⟩
  · intro i
    have hm := (hH i).mono (F.le' (a i))
    apply (integrable_const ((c i)^2)).mono' (hm.pow 2).aestronglyMeasurable
    exact Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_le_sq.mpr (hb i w)
  · intro w z hz
    by_cases hu : z ∈ Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B
    · rw [Set.indicator_of_mem hu]
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [Set.indicator_of_mem hu] using he i w z hz
    · rw [Set.indicator_of_notMem hu]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      simpa only [Set.indicator_of_notMem hu] using (he i w z hz).symm
