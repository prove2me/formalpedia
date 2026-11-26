-- Prove2me | solution 1 for Kyprianou.Ch04.predictableGeneratorTailBox
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:15:41.410617+00:00
-- url     : https://prove2.me/submissions/a2593b3c-953b-4c15-b671-eb5c61b1cd33

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_predictableUnivTailBox
import Theorems.Thm_Kyprianou_Ch04_predictableInitialTailBox
import Theorems.Thm_Kyprianou_Ch04_predictablePositiveTailBox
import Theorems.Thm_Kyprianou_Ch04_predictableBeyondHorizonTailBox
open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

/-- Restrict one marked predictable generator to a positive finite horizon. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (t : NNReal) (B : Set ℝ) (hB : MeasurableSet B)
    (D : Set ((NNReal × Omega) × ℝ))
    (hD : D ∈ insert Set.univ (insert ∅
      (Set.image2 (· ×ˢ ·)
        {S : Set (NNReal × Omega) |
          (∃ A : Set Omega, MeasurableSet[F ⊥] A ∧ S = ({⊥} ×ˢ A)) ∨
          (∃ a : NNReal, ∃ A : Set Omega, MeasurableSet[F a] A ∧ S = (Set.Ioi a ×ˢ A))}
        {C : Set ℝ | MeasurableSet C}))) (c : ℝ) :
    ∃ (a : NNReal) (C : Set ℝ) (H : Omega → ℝ),
      a ≤ t ∧ MeasurableSet C ∧ C ⊆ B ∧ StronglyMeasurable[F a] H ∧
      (∀ w, |H w| ≤ |c|) ∧
      ∀ (w : Omega) (z : ℝ × ℝ), z.1 ≠ 0 →
        (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B).indicator
          (fun z => c * D.indicator (fun _ => (1 : ℝ)) ((z.1.toNNReal,w),z.2)) z =
        (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ C).indicator (fun _ => H w) z := by
  classical
  rcases Set.mem_insert_iff.mp hD with rfl | hD
  · exact Kyprianou.Ch04.predictableUnivTailBox F t B hB c
  rcases Set.mem_insert_iff.mp hD with rfl | hD
  · refine ⟨0, ∅, fun _ => 0, bot_le, MeasurableSet.empty, Set.empty_subset _,
      stronglyMeasurable_const, fun _ => by simpa using abs_nonneg c, ?_⟩
    intro w z hz
    simp
  rcases hD with ⟨S, hS, C, hC, rfl⟩
  rcases hS with ⟨A,hA,rfl⟩ | ⟨a,A,hA,rfl⟩
  · exact Kyprianou.Ch04.predictableInitialTailBox F t B hB A C c
  · by_cases hat : a ≤ t
    · exact Kyprianou.Ch04.predictablePositiveTailBox F t B hB a A hA C hC hat c
    · exact Kyprianou.Ch04.predictableBeyondHorizonTailBox F t B hB a A C hat c
