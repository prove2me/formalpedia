-- Prove2me | solution 1 for MechanismDesign.Correlated.interim_cyclical_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:04:46.09458+00:00
-- url     : https://prove2.me/submissions/4bd22795-c347-43e7-9d74-5f986f5a447d

import Mathlib
import Definitions.Def_MechanismDesign_Correlated_IndepModel



namespace MechanismDesign.Correlated

open MeasureTheory Indep

lemma icm_ext {X : Type*} (val : X → X → ℝ) (s : ℕ → X) (m : ℕ) (z : X) :
    ∑ k ∈ Finset.range (m + 1), (val (Function.update s (m+1) z (k+1)) (Function.update s (m+1) z k)
      - val (Function.update s (m+1) z k) (Function.update s (m+1) z k)) =
    ∑ k ∈ Finset.range m, (val (s (k+1)) (s k) - val (s k) (s k)) + (val z (s m) - val (s m) (s m)) := by
  rw [Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.1 hk
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · rw [Function.update_self, Function.update_of_ne (by omega)]

lemma icm_rochet {X : Type*} (val : X → X → ℝ)
    (hcyc : ∀ (m : ℕ) (s : ℕ → X), s m = s 0 →
      ∑ k ∈ Finset.range m, (val (s (k+1)) (s k) - val (s k) (s k)) ≤ 0) :
    ∃ T : X → ℝ, ∀ x y, val x x - T x ≥ val x y - T y := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x0⟩⟩
  · exact ⟨fun _ => 0, fun x => isEmptyElim x⟩
  let C : X → Type _ := fun x => {p : ℕ × (ℕ → X) // p.2 0 = x0 ∧ p.2 p.1 = x}
  let S : ∀ x, C x → ℝ := fun x c =>
    ∑ k ∈ Finset.range c.1.1, (val (c.1.2 (k+1)) (c.1.2 k) - val (c.1.2 k) (c.1.2 k))
  have hne : ∀ x, Nonempty (C x) := fun x =>
    ⟨⟨(1, fun k => if k = 0 then x0 else x), by simp, by simp⟩⟩
  have hbdd : ∀ x, BddAbove (Set.range (S x)) := by
    intro x
    refine ⟨-(val x0 x - val x x), ?_⟩
    rintro _ ⟨c, rfl⟩
    obtain ⟨⟨m, s⟩, h0, hm⟩ := c
    have := hcyc (m+1) (Function.update s (m+1) x0) (by
      rw [Function.update_self, Function.update_of_ne (by omega)]; exact h0.symm)
    rw [icm_ext] at this
    simp only at hm
    rw [hm] at this
    show S x _ ≤ _
    simp only [S]
    linarith
  let U : X → ℝ := fun x => ⨆ c, S x c
  refine ⟨fun x => val x x - U x, fun x y => ?_⟩
  have : U y + val x y - val y y ≤ U x := by
    haveI := hne y
    have : U y ≤ U x - (val x y - val y y) := by
      apply ciSup_le
      intro c
      obtain ⟨⟨m, s⟩, h0, hm⟩ := c
      have hc : (m + 1, Function.update s (m+1) x).2 0 = x0 ∧
          (m + 1, Function.update s (m+1) x).2 (m+1) = x := by
        refine ⟨?_, ?_⟩
        · simp only; rw [Function.update_of_ne (by omega)]; exact h0
        · simp
      have hle := le_ciSup (hbdd x) ⟨_, hc⟩
      simp only [S] at hle ⊢
      rw [icm_ext] at hle
      simp only at hm
      rw [hm] at hle
      linarith
    linarith
  linarith

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*}
    [∀ i, MeasurableSpace (Θ i)] {A : Type*} [MeasurableSpace A]

lemma icm_val (ρ : ∀ i, Measure (Θ i)) [∀ i, IsProbabilityMeasure (ρ i)] (u : ∀ i, A → Θ i → ℝ)
    (q : (∀ i, Θ i) → A) (hq : IsDecisionRule ρ u q) (i : ι) (x y : Θ i) :
    Integrable (fun θ => u i (q (Function.update θ i y)) x) (prior ρ) ∧
    interimValue ρ u q i x y = ∫ θ, u i (q (Function.update θ i y)) x ∂prior ρ := by
  have hφ : AEMeasurable (fun θ : ∀ j, Θ j => q (Function.update θ i y)) (prior ρ) :=
    (hq.1.comp measurable_update_left).aemeasurable
  have hI := hq.2 i x y
  unfold interimDist at hI
  refine ⟨(integrable_map_measure hI.aestronglyMeasurable hφ).1 hI, ?_⟩
  unfold interimValue interimDist
  exact integral_map hφ hI.aestronglyMeasurable

theorem icm_core (ρ : ∀ i, Measure (Θ i)) [∀ i, IsProbabilityMeasure (ρ i)]
    (u : ∀ i, A → Θ i → ℝ)
    (q : (∀ i, Θ i) → A) (hq : IsDecisionRule ρ u q) :
    (∃ t : ι → (∀ i, Θ i) → ℝ, IsTransferRule ρ t ∧ IsBIC ρ u ⟨q, t⟩) ↔
      IsInterimCyclicallyMonotone ρ u q := by
  haveI : IsProbabilityMeasure (prior ρ) := by unfold prior; infer_instance
  constructor
  · rintro ⟨t, ht, hB⟩ i m s hs
    have key : ∀ x y : Θ i, interimValue ρ u q i x x - interimTransfer ρ t i x ≥
        interimValue ρ u q i x y - interimTransfer ρ t i y := by
      intro x y
      have h := hB i x y
      simp only at h
      rw [integral_sub (icm_val ρ u q hq i x x).1 (ht i x),
        integral_sub (icm_val ρ u q hq i x y).1 (ht i y)] at h
      rw [(icm_val ρ u q hq i x x).2, (icm_val ρ u q hq i x y).2]
      unfold interimTransfer
      exact h
    let W : ℕ → ℝ := fun k => interimValue ρ u q i (s k) (s k) - interimTransfer ρ t i (s k)
    have : ∑ κ ∈ Finset.range m,
        (interimValue ρ u q i (s (κ + 1)) (s κ) - interimValue ρ u q i (s κ) (s κ)) ≤
        ∑ κ ∈ Finset.range m, (W (κ+1) - W κ) := by
      apply Finset.sum_le_sum
      intro k _
      have := key (s (k+1)) (s k)
      simp only [W]
      linarith
    rw [Finset.sum_range_sub] at this
    simp only [W, hs] at this
    linarith
  · intro hICM
    choose T hT using fun i => icm_rochet (fun x y => interimValue ρ u q i x y) (hICM i)
    refine ⟨fun i θ => T i (θ i), ?_, ?_⟩
    · intro i y
      simp only [Function.update_self]
      exact integrable_const _
    · intro i x y
      simp only [Function.update_self]
      rw [integral_sub (icm_val ρ u q hq i x x).1 (integrable_const _),
        integral_sub (icm_val ρ u q hq i x y).1 (integrable_const _)]
      rw [← (icm_val ρ u q hq i x x).2, ← (icm_val ρ u q hq i x y).2]
      have hu : (prior ρ).real Set.univ = 1 := by simp
      simp only [integral_const, smul_eq_mul, hu, one_mul]
      exact hT i x y

end
end MechanismDesign.Correlated

open MechanismDesign.Correlated
open MeasureTheory Indep

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*}
    [∀ i, MeasurableSpace (Θ i)] {A : Type*} [MeasurableSpace A]
    (ρ : ∀ i, Measure (Θ i)) [∀ i, IsProbabilityMeasure (ρ i)] (u : ∀ i, A → Θ i → ℝ)
    (q : (∀ i, Θ i) → A) (hq : IsDecisionRule ρ u q) :
    (∃ t : ι → (∀ i, Θ i) → ℝ, IsTransferRule ρ t ∧ IsBIC ρ u ⟨q, t⟩) ↔
      IsInterimCyclicallyMonotone ρ u q := by
  exact icm_core ρ u q hq
