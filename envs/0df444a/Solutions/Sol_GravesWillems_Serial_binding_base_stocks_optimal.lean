-- Prove2me | solution 1 for GravesWillems.Serial.binding_base_stocks_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T17:09:02.877866+00:00
-- url     : https://prove2.me/submissions/efa4ceaf-0494-4b0e-bbf6-cb6bf5e8060c

import Mathlib
import Definitions.Def_GravesWillems_Serial_backlog
import Definitions.Def_GravesWillems_Serial_programP

set_option autoImplicit false

open MeasureTheory

namespace GW80431763

open GravesWillems.Serial

/-- Monotone comparison of the backlog recursion: if the partial sums `p` of `B - B'`
are nonnegative on the relevant window, the backlog under `B` exceeds that under `B'`
by at most `p j`. -/
theorem aux_le (T : ℕ → ℕ) (B B' : ℕ → ℝ) (d : ℤ → ℝ) (p : ℕ → ℝ)
    (hp : ∀ m : ℕ, B (m + 1) - B' (m + 1) = p (m + 1) - p m) :
    ∀ (r j : ℕ) (t : ℤ), (∀ k, j ≤ k → k ≤ j + r → 0 ≤ p k) →
      backlogAux T B d r (j + 1) t ≤ backlogAux T B' d r (j + 1) t + p j := by
  intro r
  induction r with
  | zero =>
    intro j t hk
    have := hk j le_rfl (by omega)
    simp [backlogAux]
    linarith
  | succ r ih =>
    intro j t hk
    have hj := hk j le_rfl (by omega)
    have hih := ih (j + 1) (t - (T (j + 1) : ℤ)) (fun k h1 h2 => hk k (by omega) (by omega))
    have hpj := hp j
    simp only [backlogAux]
    set W := windowDemand d (t - (T (j + 1) : ℤ)) t
    set X := backlogAux T B d r (j + 1 + 1) (t - (T (j + 1) : ℤ))
    set Y := backlogAux T B' d r (j + 1 + 1) (t - (T (j + 1) : ℤ))
    have h1 : W + X - B (j + 1) ≤ (W + Y - B' (j + 1)) + p j := by linarith
    have h2 : W + Y - B' (j + 1) ≤ max 0 (W + Y - B' (j + 1)) := le_max_right _ _
    have h3 : (0:ℝ) ≤ max 0 (W + Y - B' (j + 1)) := le_max_left _ _
    apply max_le
    · linarith
    · linarith

theorem aux_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (d : Ω → ℤ → ℝ) (hd : ∀ τ : ℤ, Integrable (fun ω => d ω τ) μ)
    (T : ℕ → ℕ) (B : ℕ → ℝ) :
    ∀ (r i : ℕ) (t : ℤ), Integrable (fun ω => backlogAux T B (d ω) r i t) μ := by
  intro r
  induction r with
  | zero =>
    intro i t
    simp [backlogAux]
  | succ r ih =>
    intro i t
    simp only [backlogAux]
    have hW : Integrable (fun ω => windowDemand (d ω) (t - (T i : ℤ)) t) μ := by
      unfold windowDemand
      exact integrable_finsetSum _ (fun τ _ => hd τ)
    have hX := ih (i + 1) (t - (T i : ℤ))
    have hs : Integrable (fun ω => windowDemand (d ω) (t - (T i : ℤ)) t
        + backlogAux T B (d ω) r (i + 1) (t - (T i : ℤ)) - B i) μ :=
      (hW.add hX).sub (integrable_const _)
    exact (integrable_const (0:ℝ)).sup hs

theorem abel_id (h p : ℕ → ℝ) (hp0 : p 0 = 0) :
    ∀ N : ℕ, ∑ i ∈ Finset.Icc 1 N, h i * (p i - p (i - 1))
      = ∑ i ∈ Finset.Icc 2 N, (h (i - 1) - h i) * p (i - 1) + h N * p N := by
  intro N
  induction N with
  | zero => simp [hp0]
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [hp0]
    · rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih]
      simp only [Nat.add_sub_cancel]
      ring

theorem a6_prefix (N : ℕ) (T : ℕ → ℕ) (D : ℕ → ℝ) :
    ∀ i, 1 ≤ i → i ≤ N →
      ∑ m ∈ Finset.Icc 1 i, a6 N T D m = D (∑ m ∈ Finset.Icc 1 i, T m) := by
  intro i
  induction i with
  | zero => intro h; omega
  | succ n ih =>
    intro h1 h2
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [a6]
    · rw [Finset.sum_Icc_succ_top (by omega), ih hn (by omega)]
      have hne : n + 1 ≠ 1 := by omega
      have hmem : n + 1 ∈ Finset.Icc 2 N := Finset.mem_Icc.mpr ⟨by omega, h2⟩
      simp only [a6, hne, hmem, if_false, if_true, Nat.add_sub_cancel]
      ring

end GW80431763

open GravesWillems.Serial MeasureTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (d : Ω → ℤ → ℝ) (hd : ∀ τ : ℤ, Integrable (fun ω => d ω τ) μ)
    (N : ℕ) (T : ℕ → ℕ) (D : ℕ → ℝ) (hD0 : D 0 = 0) (hD : Monotone D)
    (h : ℕ → ℝ) (he : ∀ i ∈ Finset.Ico 1 N, 0 ≤ h i - h (i + 1)) (hhN : 0 ≤ h N) (t : ℤ) :
    Feasible N T D (a6 N T D) ∧
    ∀ B : ℕ → ℝ, Feasible N T D B →
      objective μ d N T h (a6 N T D) t ≤ objective μ d N T h B t := by
  have hpre := GW80431763.a6_prefix N T D
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i hi
    rw [Finset.mem_Icc] at hi
    rw [hpre i hi.1 hi.2]
  · intro i hi
    rw [Finset.mem_Icc] at hi
    by_cases h1 : i = 1
    · subst h1
      simp only [a6, if_true]
      rw [← hD0]; exact hD (Nat.zero_le _)
    · have hmem : i ∈ Finset.Icc 2 N := Finset.mem_Icc.mpr ⟨by omega, hi.2⟩
      simp only [a6, h1, hmem, if_false, if_true]
      have : ∑ m ∈ Finset.Icc 1 (i - 1), T m ≤ ∑ m ∈ Finset.Icc 1 i, T m :=
        Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc le_rfl (by omega))
      linarith [hD this]
  · intro B ⟨hS, _⟩
    set A := a6 N T D
    set p : ℕ → ℝ := fun k => ∑ m ∈ Finset.Icc 1 k, (B m - A m) with hpdef
    have hp0 : p 0 = 0 := by simp [p]
    have hp : ∀ m : ℕ, B (m + 1) - A (m + 1) = p (m + 1) - p m := by
      intro m
      simp only [p]
      rw [Finset.sum_Icc_succ_top (by omega)]
      ring
    have hpnn : ∀ k, k ≤ N → 0 ≤ p k := by
      intro k hk
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; simp [hp0]
      · simp only [p]
        rw [Finset.sum_sub_distrib, hpre k h0 hk]
        have := hS k (Finset.mem_Icc.mpr ⟨h0, hk⟩)
        linarith
    -- pointwise / integral comparison of backlogs
    have hQ : ∀ i ∈ Finset.Icc 2 N,
        ∫ ω, backlog N T B (d ω) i t ∂μ ≤ ∫ ω, backlog N T A (d ω) i t ∂μ + p (i - 1) := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have hint1 := GW80431763.aux_integrable μ d hd T B (N + 1 - (j + 1)) (j + 1) t
      have hint2 := GW80431763.aux_integrable μ d hd T A (N + 1 - (j + 1)) (j + 1) t
      have hpt : ∀ ω, backlog N T B (d ω) (j + 1) t ≤ backlog N T A (d ω) (j + 1) t + p j := by
        intro ω
        unfold backlog
        exact GW80431763.aux_le T B A (d ω) p hp _ j t
          (fun k h1 h2 => hpnn k (by omega))
      have hm : ∫ ω, backlogAux T B (d ω) (N + 1 - (j + 1)) (j + 1) t ∂μ ≤
          ∫ ω, (backlogAux T A (d ω) (N + 1 - (j + 1)) (j + 1) t + p j) ∂μ :=
        integral_mono hint1 (hint2.add (integrable_const (p j))) hpt
      rw [integral_add hint2 (integrable_const _)] at hm
      simpa [backlog] using hm
    have hsum : ∑ i ∈ Finset.Icc 2 N, (h (i - 1) - h i) * ∫ ω, backlog N T B (d ω) i t ∂μ
        ≤ ∑ i ∈ Finset.Icc 2 N, ((h (i - 1) - h i) * ∫ ω, backlog N T A (d ω) i t ∂μ
            + (h (i - 1) - h i) * p (i - 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hei : 0 ≤ h (i - 1) - h i := by
        have hi' := Finset.mem_Icc.mp hi
        have := he (i - 1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
        rwa [Nat.sub_add_cancel (by omega)] at this
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (hQ i hi) hei
    rw [Finset.sum_add_distrib] at hsum
    have hab := GW80431763.abel_id h p hp0 N
    have hdiff : ∑ i ∈ Finset.Icc 1 N, h i * B i
        = ∑ i ∈ Finset.Icc 1 N, h i * A i + ∑ i ∈ Finset.Icc 1 N, h i * (p i - p (i - 1)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      rw [Nat.add_sub_cancel, ← hp m]
      ring
    have hpN := hpnn N le_rfl
    have hNN : 0 ≤ h N * p N := mul_nonneg hhN hpN
    unfold objective
    linarith
