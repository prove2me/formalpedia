-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovOrderedPrefixFactorV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:19:17.81315+00:00
-- url     : https://prove2.me/submissions/8ba077b6-0020-4b3d-894d-e9048ab88ddb

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
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
    (s : NNReal) (A : Set Omega) (hA : MeasurableSet[F s] A)
    (t : ℕ → NNReal) (ht : Monotone t) (hst : s ≤ t 0)
    (C : ℕ → Set ℝ) (hC : ∀ i, MeasurableSet (C i)) (n : ℕ) :
    P (A ∩ {w | ∀ i : ℕ, i < n → X (t (i+1)) w - X (t i) w ∈ C i}) =
      P A * ∏ i ∈ Finset.range n, P {w | X (t (i+1)) w - X (t i) w ∈ C i} := by
  let D : ℕ → Set Omega := fun i => {w | X (t (i+1)) w - X (t i) w ∈ C i}
  let S : ℕ → Set Omega := fun k => ⋂ i : Fin k, D i.val
  have hS (k : ℕ) : MeasurableSet[F (t k)] (S k) := by
    apply MeasurableSet.iInter
    intro i
    have h1 := (hAdapt (t (i.val+1))).mono (F.mono (ht (Nat.succ_le_of_lt i.isLt))) le_rfl
    have h2 := (hAdapt (t i.val)).mono (F.mono (ht i.isLt.le)) le_rfl
    exact (h1.sub h2) (hC i.val)
  have hstep (k : ℕ) : S (k+1) = S k ∩ D k := by
    ext w
    simp only [S, Set.mem_iInter, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨fun i => h ⟨i.val, by omega⟩, h ⟨k, by omega⟩⟩
    · rintro ⟨h, hk⟩ i
      by_cases hi : i.val < k
      · exact h ⟨i.val, hi⟩
      · have he : i.val = k := by omega
        simpa only [he] using hk
  have hprod : ∀ k, P (A ∩ S k) = P A * ∏ i ∈ Finset.range k, P (D i) := by
    intro k
    induction k with
    | zero => simp [S]
    | succ k ih =>
      have hAt := F.mono (hst.trans (ht (Nat.zero_le k))) _ hA
      rw [hstep, ← Set.inter_assoc]
      rw [hOne (t k) (t (k+1)) (ht (Nat.le_succ k)) _ (hAt.inter (hS k)) _ (hC k)]
      rw [ih, Finset.prod_range_succ, mul_assoc]
  have he : {w | ∀ i : ℕ, i < n → X (t (i+1)) w - X (t i) w ∈ C i} = S n := by
    ext w
    simp only [S, D, Set.mem_iInter, Set.mem_setOf_eq]
    exact ⟨fun h i => h i.val i.isLt, fun h i hi => h ⟨i, hi⟩⟩
  rw [he]
  exact hprod n
