-- Prove2me | solution 1 for GreedWorks.OnlineList.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:24:36.630015+00:00
-- url     : https://prove2.me/submissions/846c3091-7dc4-4696-971d-bc39b2decb76

import Mathlib
import Definitions.Def_GreedWorks_OnlineList_Model
import Definitions.Def_GreedWorks_OnlineList_LP

open GreedWorks.OnlineList MeasureTheory ProbabilityTheory

noncomputable section

private lemma summable_first_term {M : Type*} [Fintype M] {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω]
    (I : StochasticInstance M n Ω) (y : ProcessingPoint M n)
    (hy : IsPrimalFeasible I y) (i : M) (j : Fin n) :
    Summable (fun s : ℕ => y i j s / mean I i j * ((s : ℝ) + 1 / 2)) := by
  have h := (hy.2.2.2.1 i j).mul_left (mean I i j)⁻¹
  refine h.congr (fun s => ?_)
  ring

private lemma summable_primal_term {M : Type*} [Fintype M] {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω]
    (I : StochasticInstance M n Ω) (y : ProcessingPoint M n)
    (hy : IsPrimalFeasible I y) (i : M) (j : Fin n) :
    Summable (fun s : ℕ => y i j s / mean I i j * ((s : ℝ) + 1 / 2) + y i j s / 2) := by
  exact (summable_first_term I y hy i j).add ((hy.2.2.1 i j).div_const 2)

private lemma summable_stoch_term {M : Type*} [Fintype M] {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω]
    (I : StochasticInstance M n Ω) (y : ProcessingPoint M n)
    (hy : IsPrimalFeasible I y) (i : M) (j : Fin n) :
    Summable (fun s : ℕ =>
      y i j s / mean I i j * ((s : ℝ) + 1 / 2) + (1 - cvSquared I i j) / 2 * y i j s) := by
  exact (summable_first_term I y hy i j).add ((hy.2.2.1 i j).mul_left ((1 - cvSquared I i j) / 2))

private lemma cvSquared_le_Delta {M : Type*} [Fintype M] {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω]
    (I : StochasticInstance M n Ω) (i : M) (j : Fin n) (hi : I.eligible i j) :
    cvSquared I i j ≤ I.Delta := by
  unfold cvSquared mean
  have hmean : 1 ≤ ∫ ω, (I.P i j ω : ℝ) ∂I.Pr := I.meanAtLeastOne i j hi
  have hsq : 0 < (∫ ω, (I.P i j ω : ℝ) ∂I.Pr) ^ 2 := by positivity
  rw [div_le_iff₀ hsq]
  exact I.cvBound i j hi

private lemma primalCompletion_le {M : Type*} [Fintype M] {n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω]
    (I : StochasticInstance M n Ω) (y : ProcessingPoint M n)
    (hy : IsStochasticFeasible I y) (j : Fin n) :
    primalCompletion I y j ≤ (1 + I.Delta / 2) * stochasticCompletion I y j := by
  classical
  let E : Finset M := Finset.univ.filter (fun i : M => I.eligible i j)
  have hterm : ∀ i ∈ E,
      (∑' s : ℕ, (y i j s / mean I i j * ((s : ℝ) + 1 / 2) + y i j s / 2)) ≤
      (∑' s : ℕ, (y i j s / mean I i j * ((s : ℝ) + 1 / 2) +
        (1 - cvSquared I i j) / 2 * y i j s)) +
      (I.Delta / 2) * (∑' s : ℕ, y i j s) := by
    intro i hi
    have helig : I.eligible i j := (Finset.mem_filter.mp hi).2
    have hcv : cvSquared I i j ≤ I.Delta := cvSquared_le_Delta I i j helig
    have hp := (summable_primal_term I y hy.1 i j).hasSum
    have hs := (summable_stoch_term I y hy.1 i j).hasSum
    have hy_s := (hy.1.2.2.1 i j).hasSum
    refine hasSum_le (fun s => ?_) hp (hs.add (hy_s.mul_left (I.Delta / 2)))
    have hys : 0 ≤ y i j s := hy.1.1 i j s
    have hmul : cvSquared I i j * y i j s ≤ I.Delta * y i j s :=
      mul_le_mul_of_nonneg_right hcv hys
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hprimal_eq : primalCompletion I y j =
      ∑ i ∈ E, ∑' s : ℕ, (y i j s / mean I i j * ((s : ℝ) + 1 / 2) + y i j s / 2) := by
    unfold primalCompletion
    rfl
  have hstoch_eq : stochasticCompletion I y j =
      ∑ i ∈ E, ∑' s : ℕ, (y i j s / mean I i j * ((s : ℝ) + 1 / 2) +
        (1 - cvSquared I i j) / 2 * y i j s) := by
    unfold stochasticCompletion
    rfl
  rw [← hprimal_eq, ← hstoch_eq] at hsum
  have h5 : (∑ i ∈ E, ∑' s : ℕ, y i j s) ≤ stochasticCompletion I y j := hy.2 j
  have hDelta : 0 ≤ I.Delta / 2 := by
    have := I.Delta_nonneg
    linarith
  have hmul5 : (I.Delta / 2) * (∑ i ∈ E, ∑' s : ℕ, y i j s) ≤
      (I.Delta / 2) * stochasticCompletion I y j :=
    mul_le_mul_of_nonneg_left h5 hDelta
  linarith

end

theorem solution {M : Type*} [Fintype M] [Nonempty M] (n : ℕ)
    {Ω : Type*} [MeasurableSpace Ω]
    (I : StochasticInstance M n Ω) (y : ProcessingPoint M n)
    (hy : IsStochasticFeasible I y) :
    ∃ y' : ProcessingPoint M n,
      IsPrimalFeasible I y' ∧
        primalValue I y' ≤ (1 + I.Delta / 2) * stochasticValue I y := by
  refine ⟨y, hy.1, ?_⟩
  unfold primalValue stochasticValue
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  have hj := primalCompletion_le I y hy j
  have hw : 0 ≤ I.weight j := I.weight_nonneg j
  calc I.weight j * primalCompletion I y j
      ≤ I.weight j * ((1 + I.Delta / 2) * stochasticCompletion I y j) :=
        mul_le_mul_of_nonneg_left hj hw
    _ = (1 + I.Delta / 2) * (I.weight j * stochasticCompletion I y j) := by ring
