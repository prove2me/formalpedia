-- Prove2me | solution 1 for GravesWillems.Serial.transfer_step_improves
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T05:09:46.451128+00:00
-- url     : https://prove2.me/submissions/3271e5ea-1f63-4036-9bfc-0761acf149dc

import Mathlib
import Definitions.Def_GravesWillems_Serial_backlog
import Definitions.Def_GravesWillems_Serial_programP
open MeasureTheory

namespace GravesWillems.Serial

lemma aux_tsi_transfer_apply (B : ℕ → ℝ) (k : ℕ) (Δ : ℝ) (m : ℕ) :
    transfer B k Δ m = B m - (if m = k then Δ else 0) + (if m = k + 1 then Δ else 0) := by
  unfold transfer
  simp only [Function.update_apply]
  split_ifs with h1 h2 <;> first | (exfalso; omega) | (subst_vars; ring)

lemma aux_tsi_transfer_sum (B : ℕ → ℝ) (k : ℕ) (Δ : ℝ) (s : Finset ℕ) :
    ∑ m ∈ s, transfer B k Δ m = ∑ m ∈ s, B m - (if k ∈ s then Δ else 0)
      + (if k + 1 ∈ s then Δ else 0) := by
  simp only [aux_tsi_transfer_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq']

lemma aux_tsi_split (f : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ∑ m ∈ Finset.Icc 1 k, f m = ∑ m ∈ Finset.Icc 1 (k - 1), f m + f k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Finset.sum_Icc_succ_top (by omega)]
  simp

lemma aux_tsi_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (d : Ω → ℤ → ℝ) (hd : ∀ τ : ℤ, Integrable (fun ω => d ω τ) μ)
    (T : ℕ → ℕ) (B : ℕ → ℝ) : ∀ (r i : ℕ) (t : ℤ),
    Integrable (fun ω => backlogAux T B (d ω) r i t) μ := by
  intro r
  induction r with
  | zero => intro i t; simp [backlogAux]
  | succ r ih =>
    intro i t
    simp only [backlogAux]
    have hw : Integrable (fun ω => windowDemand (d ω) (t - (T i : ℤ)) t) μ := by
      unfold windowDemand
      exact integrable_finsetSum _ (fun τ _ => hd τ)
    have h2 := ((hw.add (ih (i+1) (t - (T i : ℤ)))).sub (integrable_const (B i)))
    exact (integrable_zero _ _ _).sup h2

lemma aux_tsi_high (T : ℕ → ℕ) (B : ℕ → ℝ) (k : ℕ) (Δ : ℝ) (d : ℤ → ℝ) :
    ∀ (r i : ℕ) (t : ℤ), k + 2 ≤ i →
      backlogAux T (transfer B k Δ) d r i t = backlogAux T B d r i t := by
  intro r
  induction r with
  | zero => intro i t _; simp [backlogAux]
  | succ r ih =>
    intro i t hi
    simp only [backlogAux]
    rw [ih (i+1) _ (by omega), aux_tsi_transfer_apply]
    simp [show i ≠ k by omega, show i ≠ k + 1 by omega]

lemma aux_tsi_mid (T : ℕ → ℕ) (B : ℕ → ℝ) (k : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ) (d : ℤ → ℝ)
    (r : ℕ) (t : ℤ) :
    backlogAux T B d r (k+1) t - Δ ≤ backlogAux T (transfer B k Δ) d r (k+1) t ∧
    backlogAux T (transfer B k Δ) d r (k+1) t ≤ backlogAux T B d r (k+1) t := by
  cases r with
  | zero => simp [backlogAux]; linarith
  | succ r =>
    simp only [backlogAux]
    rw [aux_tsi_high T B k Δ d r (k+1+1) _ (by omega), aux_tsi_transfer_apply]
    simp only [show k + 1 ≠ k by omega, if_false, if_true, sub_zero]
    set a := windowDemand d (t - (T (k+1) : ℤ)) t
      + backlogAux T B d r (k + 1 + 1) (t - (T (k+1) : ℤ))
    constructor
    · rw [sub_le_iff_le_add]
      have h1 := le_max_left 0 (a - (B (k+1) + Δ))
      have h2 := le_max_right 0 (a - (B (k+1) + Δ))
      apply max_le <;> linarith
    · exact max_le_max le_rfl (by linarith)

lemma aux_tsi_low (T : ℕ → ℕ) (B : ℕ → ℝ) (k : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ) (d : ℤ → ℝ) :
    ∀ (r i : ℕ) (t : ℤ), i ≤ k →
      backlogAux T B d r i t ≤ backlogAux T (transfer B k Δ) d r i t := by
  intro r
  induction r with
  | zero => intro i t _; simp [backlogAux]
  | succ r ih =>
    intro i t hi
    simp only [backlogAux]
    rcases Nat.lt_or_ge i k with hlt | hge
    · rw [aux_tsi_transfer_apply]
      simp only [show i ≠ k by omega, show i ≠ k + 1 by omega, if_false, sub_zero, add_zero]
      have := ih (i+1) (t - (T i : ℤ)) (by omega)
      exact max_le_max le_rfl (by linarith)
    · have hik : i = k := by omega
      rw [hik, aux_tsi_transfer_apply]
      simp only [if_true, show k ≠ k + 1 by omega, if_false, add_zero]
      have := (aux_tsi_mid T B k Δ hΔ d r (t - (T k : ℤ))).1
      exact max_le_max le_rfl (by linarith)

end GravesWillems.Serial

open GravesWillems.Serial

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (d : Ω → ℤ → ℝ) (hd : ∀ τ : ℤ, Integrable (fun ω => d ω τ) μ)
    (N : ℕ) (T : ℕ → ℕ) (D : ℕ → ℝ) (hD0 : D 0 = 0) (hD : Monotone D)
    (h : ℕ → ℝ) (he : ∀ i ∈ Finset.Ico 1 N, 0 ≤ h i - h (i + 1))
    (B : ℕ → ℝ) (hB : Feasible N T D B) (k : ℕ) (hk1 : 1 ≤ k) (hkN : k + 1 ≤ N)
    (hbind : ∀ i ∈ Finset.Ico 1 k,
      ∑ m ∈ Finset.Icc 1 i, B m = D (∑ m ∈ Finset.Icc 1 i, T m))
    (hstrict : D (∑ m ∈ Finset.Icc 1 k, T m) < ∑ m ∈ Finset.Icc 1 k, B m) :
    Feasible N T D (transfer B k (B k - D (∑ m ∈ Finset.Icc 1 k, T m)
        + D (∑ m ∈ Finset.Icc 1 (k - 1), T m))) ∧
    (∀ i ∈ Finset.Icc 1 k,
      ∑ m ∈ Finset.Icc 1 i, transfer B k (B k - D (∑ m ∈ Finset.Icc 1 k, T m)
          + D (∑ m ∈ Finset.Icc 1 (k - 1), T m)) m
        = D (∑ m ∈ Finset.Icc 1 i, T m)) ∧
    ∀ t : ℤ,
      objective μ d N T h (transfer B k (B k - D (∑ m ∈ Finset.Icc 1 k, T m)
          + D (∑ m ∈ Finset.Icc 1 (k - 1), T m))) t
        ≤ objective μ d N T h B t := by
  have hprev : ∑ m ∈ Finset.Icc 1 (k-1), B m = D (∑ m ∈ Finset.Icc 1 (k-1), T m) := by
    rcases Nat.lt_or_ge k 2 with hk | hk
    · have : k - 1 = 0 := by omega
      rw [this]; simp [hD0]
    · exact hbind (k-1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
  have hsplitB := aux_tsi_split B k hk1
  have hTmono : ∑ m ∈ Finset.Icc 1 (k-1), T m ≤ ∑ m ∈ Finset.Icc 1 k, T m := by
    apply Finset.sum_le_sum_of_subset
    exact Finset.Icc_subset_Icc le_rfl (by omega)
  have hDmono := hD hTmono
  set Δ := B k - D (∑ m ∈ Finset.Icc 1 k, T m) + D (∑ m ∈ Finset.Icc 1 (k - 1), T m)
    with hΔdef
  have hPk : ∑ m ∈ Finset.Icc 1 k, B m - Δ = D (∑ m ∈ Finset.Icc 1 k, T m) := by
    rw [hsplitB, hprev, hΔdef]; ring
  have hΔpos : 0 ≤ Δ := by linarith
  have hBk : 0 ≤ B k - Δ := by rw [hΔdef]; linarith
  have hsum := fun i => aux_tsi_transfer_sum B k Δ (Finset.Icc 1 i)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro i hi
    rw [Finset.mem_Icc] at hi
    rw [hsum i]
    rcases lt_trichotomy i k with h1 | h1 | h1
    · rw [if_neg (by simp; omega), if_neg (by simp; omega)]
      have := hB.1 i (Finset.mem_Icc.mpr hi)
      linarith
    · subst h1
      rw [if_pos (by simp; omega), if_neg (by simp)]
      linarith
    · rw [if_pos (by simp; omega), if_pos (by simp; omega)]
      have := hB.1 i (Finset.mem_Icc.mpr hi)
      linarith
  · intro i hi
    rw [Finset.mem_Icc] at hi
    rw [aux_tsi_transfer_apply]
    by_cases h1 : i = k
    · subst h1
      rw [if_pos rfl, if_neg (by omega)]
      linarith
    · by_cases h2 : i = k + 1
      · subst h2
        rw [if_neg (by omega), if_pos rfl]
        have := hB.2 (k+1) (Finset.mem_Icc.mpr hi)
        linarith
      · rw [if_neg h1, if_neg h2]
        have := hB.2 i (Finset.mem_Icc.mpr hi)
        linarith
  · intro i hi
    rw [Finset.mem_Icc] at hi
    rw [hsum i]
    rcases lt_or_eq_of_le hi.2 with h1 | h1
    · rw [if_neg (by simp; omega), if_neg (by simp; omega)]
      have := hbind i (Finset.mem_Ico.mpr ⟨hi.1, h1⟩)
      linarith
    · subst h1
      rw [if_pos (by simp; omega), if_neg (by simp)]
      linarith
  · intro t
    unfold objective
    have hh : ∑ i ∈ Finset.Icc 1 N, h i * transfer B k Δ i
        = ∑ i ∈ Finset.Icc 1 N, h i * B i - (h k - h (k+1)) * Δ := by
      simp only [aux_tsi_transfer_apply, mul_add, mul_sub, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq']
      rw [if_pos (by simp; omega), if_pos (by simp; omega)]
      ring
    rw [hh]
    have hint := aux_tsi_integrable μ d hd T
    have key : ∀ i ∈ Finset.Icc 2 N,
        (h (i-1) - h i) * ∫ ω, backlog N T B (d ω) i t ∂μ
          - (h (i-1) - h i) * ∫ ω, backlog N T (transfer B k Δ) (d ω) i t ∂μ
          ≤ if i = k + 1 then (h k - h (k+1)) * Δ else 0 := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      have he' : 0 ≤ h (i-1) - h i := by
        have := he (i-1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
        rwa [show i - 1 + 1 = i by omega] at this
      simp only [backlog]
      rcases lt_trichotomy i (k+1) with h1 | h1 | h1
      · rw [if_neg (by omega), ← mul_sub]
        have hle : ∫ ω, backlogAux T B (d ω) (N + 1 - i) i t ∂μ
            ≤ ∫ ω, backlogAux T (transfer B k Δ) (d ω) (N + 1 - i) i t ∂μ :=
          integral_mono (hint B _ _ _) (hint _ _ _ _)
            (fun ω => aux_tsi_low T B k Δ hΔpos (d ω) _ _ _ (by omega))
        nlinarith
      · subst h1
        rw [if_pos rfl, ← mul_sub]
        simp only [Nat.add_sub_cancel]
        have hle : ∫ ω, backlogAux T B (d ω) (N + 1 - (k+1)) (k+1) t ∂μ
            ≤ ∫ ω, (backlogAux T (transfer B k Δ) (d ω) (N + 1 - (k+1)) (k+1) t + Δ) ∂μ :=
          integral_mono (hint B _ _ _) ((hint _ _ _ _).add (integrable_const Δ))
            (fun ω => by
              have := (aux_tsi_mid T B k Δ hΔpos (d ω) (N + 1 - (k+1)) t).1
              linarith)
        rw [integral_add (hint _ _ _ _) (integrable_const Δ), integral_const] at hle
        simp only [probReal_univ, smul_eq_mul, one_mul] at hle
        simp only [Nat.add_sub_cancel] at he'
        nlinarith
      · rw [if_neg (by omega)]
        have : ∀ ω, backlogAux T (transfer B k Δ) (d ω) (N + 1 - i) i t
            = backlogAux T B (d ω) (N + 1 - i) i t :=
          fun ω => aux_tsi_high T B k Δ (d ω) _ _ _ (by omega)
        simp only [this, sub_self, le_refl]
    have hs := Finset.sum_le_sum key
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (by simp; omega)] at hs
    linarith
