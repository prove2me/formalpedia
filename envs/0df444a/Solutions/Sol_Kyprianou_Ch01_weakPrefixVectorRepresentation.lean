-- Prove2me | solution 1 for Kyprianou.Ch01.weakPrefixVectorRepresentation
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T03:05:48.223228+00:00
-- url     : https://prove2.me/submissions/db20dea4-d772-49c2-8e6b-8e08d263d404

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.FunProp
open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (increment : ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, Measurable (increment n))
    (n : ℕ) :
    let S : ℕ → Ω → ℝ :=
      fun k ω => ∑ i ∈ Finset.range k, increment i ω
    let H : Set Ω :=
      {ω | ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < S j ω}
    let V : Ω → (Finset.range n → ℝ) :=
      fun ω i => increment i.1 ω
    ∃ (g : (Finset.range n → ℝ) → ℝ)
      (A : Set (Finset.range n → ℝ)),
      Measurable g ∧ MeasurableSet A ∧
      (∀ ω : Ω, S n ω = g (V ω)) ∧ H = V ⁻¹' A := by
  intro S H V
  let ps : ℕ → (Finset.range n → ℝ) → ℝ := fun j v =>
    ∑ i : Finset.range n, if (i : ℕ) < j then v i else 0
  have hps : ∀ j, Measurable (ps j) := fun j => by
    apply Finset.measurable_sum
    intro i _
    split_ifs
    · exact measurable_pi_apply i
    · exact measurable_const
  have key : ∀ j, j ≤ n → ∀ ω, S j ω = ps j (V ω) := by
    intro j hj ω
    simp only [S, ps, V]
    rw [Finset.sum_coe_sort (Finset.range n) (fun i => if i < j then increment i ω else 0)]
    rw [← Finset.sum_filter, Finset.range_eq_Ico, Finset.range_eq_Ico]
    congr 1
    ext i; simp only [Finset.mem_filter, Finset.mem_Ico]; omega
  refine ⟨ps n, {v | ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < ps j v}, hps n, ?_, key n le_rfl, ?_⟩
  · have : {v : Finset.range n → ℝ | ∀ j : ℕ, 1 ≤ j → j ≤ n → 0 < ps j v} =
        ⋂ j ∈ Finset.range (n+1), {v | 1 ≤ j → 0 < ps j v} := by
      ext v; simp only [mem_setOf_eq, mem_iInter, Finset.mem_range]
      exact ⟨fun h j hj h1 => h j h1 (by omega), fun h j h1 hj => h j (by omega) h1⟩
    rw [this]
    refine Finset.measurableSet_biInter _ fun j _ => ?_
    by_cases h1 : 1 ≤ j
    · simpa [h1] using measurableSet_lt measurable_const (hps j)
    · simp [h1]
  · ext ω
    simp only [H, Set.mem_setOf_eq, Set.mem_preimage]
    exact ⟨fun h j h1 hj => (key j hj ω) ▸ h j h1 hj, fun h j h1 hj => (key j hj ω).symm ▸ h j h1 hj⟩
