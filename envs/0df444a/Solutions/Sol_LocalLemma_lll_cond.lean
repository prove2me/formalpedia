-- Prove2me | solution 1 for LocalLemma.lll_cond
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:25:12.391099+00:00
-- url     : https://prove2.me/submissions/cbef35fe-0aaa-45af-88fb-1d8ad25bc9ca

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
public import Definitions.Def_LocalLemmaLib_LocalLemma
public import Theorems.Thm_LocalLemma_avoid_anti
public import Theorems.Thm_LocalLemma_lll_chain

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma
namespace LocalLemma
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (Γ : SimpleGraph (Fin n))
    [DecidableRel Γ.Adj] (hΓ : IsDependencyGraph μ A Γ) (x : Fin n → ℝ) (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i < 1)
    (hP : ∀ i, μ.real (A i) ≤ x i * ∏ j ∈ Γ.neighborFinset i, (1 - x j)) :
    ∀ S : Finset (Fin n), ∀ i ∉ S, μ.real (avoid A S ∩ A i) ≤ x i * μ.real (avoid A S) := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
  intro i hi
  set S₂ := S.filter (fun j => ¬ Γ.Adj i j) with hS₂
  have hS₂S : S₂ ⊆ S := Finset.filter_subset _ _
  have h1 : μ.real (avoid A S ∩ A i) ≤ μ.real (avoid A S₂ ∩ A i) :=
    measureReal_mono (Set.inter_subset_inter_left _ (avoid_anti A hS₂S))
  have hm1 : MeasurableSet[MeasurableSpace.generateFrom {A i}] (A i) :=
    MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _)
  have hm2 : MeasurableSet[MeasurableSpace.generateFrom
      {s | ∃ j, j ≠ i ∧ ¬ Γ.Adj i j ∧ s = A j}] (avoid A S₂) := by
    have : ∀ j ∈ S₂, MeasurableSet[MeasurableSpace.generateFrom
        {s | ∃ j, j ≠ i ∧ ¬ Γ.Adj i j ∧ s = A j}] (A j)ᶜ := by
      intro j hj
      rw [hS₂, Finset.mem_filter] at hj
      refine MeasurableSet.compl (MeasurableSpace.measurableSet_generateFrom ?_)
      exact ⟨j, fun h => hi (h ▸ hj.1), hj.2, rfl⟩
    exact Finset.measurableSet_biInter _ this
  have h2 : μ.real (avoid A S₂ ∩ A i) = μ.real (A i) * μ.real (avoid A S₂) := by
    have := (Indep_iff _ _ μ).1 (hΓ i) (A i) (avoid A S₂) hm1 hm2
    rw [Set.inter_comm]
    simp only [Measure.real, this, ENNReal.toReal_mul]
  have hsub : S \ S₂ ⊆ Γ.neighborFinset i := by
    intro j hj
    simp only [hS₂, Finset.mem_sdiff, Finset.mem_filter, not_and, not_not] at hj
    simpa using hj.2 hj.1
  have h3 : ∏ j ∈ Γ.neighborFinset i, (1 - x j) ≤ ∏ j ∈ S \ S₂, (1 - x j) := by
    rw [← Finset.prod_sdiff hsub]
    have h0 : 0 ≤ ∏ j ∈ S \ S₂, (1 - x j) := Finset.prod_nonneg fun j _ => by linarith [hx1 j]
    have hle : ∏ j ∈ Γ.neighborFinset i \ (S \ S₂), (1 - x j) ≤ 1 :=
      Finset.prod_le_one (fun j _ => by linarith [hx1 j]) (fun j _ => by linarith [hx0 j])
    nlinarith
  have h4 := lll_chain μ A hA x hx1 S ih (S \ S₂) Finset.sdiff_subset
  rw [Finset.sdiff_sdiff_eq_self hS₂S] at h4
  have hμ : 0 ≤ μ.real (avoid A S₂) := measureReal_nonneg
  calc μ.real (avoid A S ∩ A i) ≤ μ.real (A i) * μ.real (avoid A S₂) := h1.trans h2.le
    _ ≤ (x i * ∏ j ∈ Γ.neighborFinset i, (1 - x j)) * μ.real (avoid A S₂) :=
        mul_le_mul_of_nonneg_right (hP i) hμ
    _ ≤ (x i * ∏ j ∈ S \ S₂, (1 - x j)) * μ.real (avoid A S₂) := by
        gcongr; exact hx0 i
    _ = x i * ((∏ j ∈ S \ S₂, (1 - x j)) * μ.real (avoid A S₂)) := by ring
    _ ≤ x i * μ.real (avoid A S) := mul_le_mul_of_nonneg_left h4 (hx0 i)
end LocalLemma
