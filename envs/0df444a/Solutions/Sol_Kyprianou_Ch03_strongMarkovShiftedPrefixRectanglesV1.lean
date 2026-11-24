-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovShiftedPrefixRectanglesV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:25:06.398531+00:00
-- url     : https://prove2.me/submissions/24fead65-ec2b-4228-99f6-968e576e10fe

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch03_strongMarkovOrderedPrefixFactorV1
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real)
    (hAdapt : ∀ t : NNReal, Measurable[F t] (X t))
    (hOne : ∀ (s t : NNReal), s ≤ t → ∀ (A : Set Omega), MeasurableSet[F s] A →
      ∀ (C : Set Real), MeasurableSet C →
      P (A ∩ {w | X t w - X s w ∈ C}) =
        P A * P {w | X t w - X s w ∈ C})
    (hX : IsLevyProcess X P)
    (s : NNReal) (A : Set Omega) (hA : MeasurableSet[F s] A)
    (t : ℕ → NNReal) (ht : Monotone t) (ht0 : t 0 = 0)
    (C : ℕ → Set ℝ) (hC : ∀ i, MeasurableSet (C i)) (n : ℕ) :
    P (A ∩ {w | ∀ k : ℕ, k < n → X (s+t (k+1)) w - X (s+t k) w ∈ C k}) =
    P A * P {w | ∀ k : ℕ, k < n → X (t (k+1)) w - X (t k) w ∈ C k} := by
  classical
  have hshift := Kyprianou.Ch03.strongMarkovOrderedPrefixFactorV1 P F X hAdapt hOne
    s A hA (fun i => s+t i) (fun i j hij => add_le_add le_rfl (ht hij))
    (by simp [ht0]) C hC n
  have hbase := Kyprianou.Ch03.strongMarkovOrderedPrefixFactorV1 P F X hAdapt hOne
    0 Set.univ (@MeasurableSet.univ Omega (F 0)) t ht (by simp) C hC n
  rw [Set.univ_inter, measure_univ, one_mul] at hbase
  rw [hshift, hbase]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  have hle : t k ≤ t (k+1) := ht (Nat.le_succ k)
  have h1 := (hX.stationary_increments (s+t k) (t (k+1)-t k))
  have h2 := (hX.stationary_increments (t k) (t (k+1)-t k))
  have he : t k + (t (k+1)-t k) = t (k+1) := by
    rw [add_comm, tsub_add_cancel_of_le hle]
  rw [add_assoc, he] at h1
  rw [he] at h2
  exact (h1.measure_mem_eq (hC k)).trans (h2.measure_mem_eq (hC k)).symm
