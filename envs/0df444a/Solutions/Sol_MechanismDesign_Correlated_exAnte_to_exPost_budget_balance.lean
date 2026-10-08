-- Prove2me | solution 1 for MechanismDesign.Correlated.exAnte_to_exPost_budget_balance
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:07:46.795762+00:00
-- url     : https://prove2.me/submissions/92bf842f-5fa9-42c7-ac1d-a5785f15cfec

import Mathlib
import Definitions.Def_MechanismDesign_Correlated_IndepModel



namespace MechanismDesign.Correlated

open MeasureTheory Indep

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*}
    [∀ i, MeasurableSpace (Θ i)]

lemma bb_mp (ρ : ∀ i, Measure (Θ i)) [∀ i, IsProbabilityMeasure (ρ i)] (j : ι) :
    MeasurePreserving (fun p : (∀ k, Θ k) × Θ j => Function.update p.1 j p.2)
      ((Measure.pi ρ).prod (ρ j)) (Measure.pi ρ) := by
  refine ⟨measurable_update', ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (∀ k, Θ k) × Θ j => Function.update p.1 j p.2) ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi (Function.update s j Set.univ)) ×ˢ s j := by
    ext ⟨θ, x⟩
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun k => ?_, by simpa using h j⟩
      by_cases hk : k = j
      · subst hk; simp
      · have := h k
        rw [Function.update_of_ne hk] at this
        rw [Function.update_of_ne hk]; exact this
    · rintro ⟨h1, h2⟩ k
      by_cases hk : k = j
      · subst hk; simpa using h2
      · have := h1 k
        rw [Function.update_of_ne hk] at this
        rw [Function.update_of_ne hk]; exact this
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have : ∀ k, ρ k (Function.update s j Set.univ k) = if k = j then 1 else ρ k (s k) := by
    intro k
    by_cases hk : k = j
    · subst hk; simp
    · rw [Function.update_of_ne hk, if_neg hk]
  simp only [this]
  rw [← Finset.mul_prod_erase Finset.univ (fun k => ρ k (s k)) (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ (fun k => if k = j then (1 : ENNReal) else ρ k (s k))
      (Finset.mem_univ j)]
  simp only [if_true, one_mul]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [if_neg (Finset.ne_of_mem_erase hk)]

lemma bb_marg (ρ : ∀ i, Measure (Θ i)) [∀ i, IsProbabilityMeasure (ρ i)] (j : ι)
    (g : (∀ k, Θ k) → ℝ) (hg : Integrable g (prior ρ)) :
    Integrable (fun θ : ∀ k, Θ k => ∫ θ', g (Function.update θ' j (θ j)) ∂prior ρ) (prior ρ) ∧
    ∫ θ : ∀ k, Θ k, (∫ θ', g (Function.update θ' j (θ j)) ∂prior ρ) ∂prior ρ =
      ∫ θ, g θ ∂prior ρ := by
  unfold prior at *
  have hΦ := bb_mp ρ j
  have hgΦ : Integrable (fun p : (∀ k, Θ k) × Θ j => g (Function.update p.1 j p.2))
      ((Measure.pi ρ).prod (ρ j)) := hΦ.integrable_comp hg.aestronglyMeasurable |>.2 hg
  have hG : Integrable (fun x : Θ j => ∫ θ', g (Function.update θ' j x) ∂Measure.pi ρ) (ρ j) :=
    hgΦ.integral_prod_right
  have hev := measurePreserving_eval ρ j
  refine ⟨hev.integrable_comp hG.aestronglyMeasurable |>.2 hG, ?_⟩
  have h1 : ∫ θ : ∀ k, Θ k, (∫ θ', g (Function.update θ' j (θ j)) ∂Measure.pi ρ) ∂Measure.pi ρ =
      ∫ x, (∫ θ', g (Function.update θ' j x) ∂Measure.pi ρ) ∂ρ j := by
    rw [← hev.map_eq, integral_map hev.measurable.aemeasurable
      (by rw [hev.map_eq]; exact hG.aestronglyMeasurable)]
  rw [h1, ← integral_prod_symm _ hgΦ]
  conv_rhs => rw [← hΦ.map_eq]
  rw [integral_map hΦ.measurable.aemeasurable (by rw [hΦ.map_eq]; exact hg.aestronglyMeasurable)]

end

theorem bb_core {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*}
    [∀ i, MeasurableSpace (Θ i)] {A : Type*}
    (ρ : ∀ i, Measure (Θ i)) [∀ i, IsProbabilityMeasure (ρ i)] (hN : 2 ≤ Fintype.card ι)
    (M : DirectMechanism ι Θ A) (hM : IsTransferRule ρ M.t) (hBB : IsExAnteBB ρ M) :
    ∃ M' : DirectMechanism ι Θ A, IsTransferRule ρ M'.t ∧ Equivalent ρ M M' ∧ IsExPostBB M' := by
  haveI : IsProbabilityMeasure (prior ρ) := by unfold prior; infer_instance
  let T : ∀ j, Θ j → ℝ := fun j y => interimTransfer ρ M.t j y
  let c : ι → ℝ := fun j => ∫ θ, M.t j θ ∂prior ρ
  let N : ℝ := Fintype.card ι
  have hN1 : N - 1 ≠ 0 := by
    have : (2:ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hN
    simp only [N]; linarith
  let k : ℝ := 1 / (N - 1)
  let D : ι → (∀ j, Θ j) → ℝ := fun j θ => T j (θ j) - c j
  have hmarg := fun j => bb_marg ρ j (M.t j) (hBB.1 j)
  have hDint : ∀ j, Integrable (D j) (prior ρ) := fun j => (hmarg j).1.sub (integrable_const _)
  have hDzero : ∀ j, ∫ θ, D j θ ∂prior ρ = 0 := by
    intro j
    have h := integral_sub (μ := prior ρ) (hmarg j).1 (integrable_const (c j))
    simp only [D, T, interimTransfer]
    rw [h, (hmarg j).2, integral_const]
    simp [c]
  let t' : ι → (∀ j, Θ j) → ℝ := fun i θ => T i (θ i) - k * ∑ j ∈ Finset.univ.erase i, D j θ
  have hupd : ∀ i y, (fun θ => t' i (Function.update θ i y)) =
      fun θ => T i y - k * ∑ j ∈ Finset.univ.erase i, D j θ := by
    intro i y
    funext θ
    simp only [t', Function.update_self]
    congr 2
    apply Finset.sum_congr rfl
    intro j hj
    simp only [D, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hint : ∀ i y, Integrable (fun θ => t' i (Function.update θ i y)) (prior ρ) := by
    intro i y
    rw [hupd]
    exact (integrable_const _).sub ((integrable_finset_sum _ (fun j _ => hDint j)).const_mul k)
  refine ⟨⟨M.q, t'⟩, hint, ⟨rfl, ?_⟩, ?_⟩
  · intro i y
    show ∫ θ, t' i (Function.update θ i y) ∂prior ρ = T i y
    rw [hupd, integral_sub (integrable_const _)
      ((integrable_finset_sum _ (fun j _ => hDint j)).const_mul k), integral_const,
      integral_const_mul, integral_finset_sum _ (fun j _ => hDint j)]
    simp [hDzero]
  · intro θ
    show ∑ i, t' i θ = 0
    have hsum : ∀ i, ∑ j ∈ Finset.univ.erase i, D j θ = ∑ j, D j θ - D i θ := by
      intro i
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    have hc : ∑ j, c j = 0 := by
      simp only [c]
      rw [← integral_finset_sum _ (fun j _ => hBB.1 j)]
      exact hBB.2
    simp only [t', hsum, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    have hS : ∑ j, D j θ = ∑ j, T j (θ j) - ∑ j, c j := by
      simp only [D, Finset.sum_sub_distrib]
    rw [hS, hc]
    have : k * ((Fintype.card ι : ℝ) * (∑ j, T j (θ j) - 0) - (∑ j, T j (θ j) - 0)) =
        ∑ j, T j (θ j) := by
      simp only [k]
      field_simp
      simp only [N]
      ring
    linarith

end MechanismDesign.Correlated

open MechanismDesign.Correlated
open MeasureTheory Indep

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*}
    [∀ i, MeasurableSpace (Θ i)] {A : Type*}
    (ρ : ∀ i, Measure (Θ i)) [∀ i, IsProbabilityMeasure (ρ i)] (hN : 2 ≤ Fintype.card ι)
    (M : DirectMechanism ι Θ A) (hM : IsTransferRule ρ M.t) (hBB : IsExAnteBB ρ M) :
    ∃ M' : DirectMechanism ι Θ A, IsTransferRule ρ M'.t ∧ Equivalent ρ M M' ∧ IsExPostBB M' := by
  exact bb_core ρ hN M hM hBB
