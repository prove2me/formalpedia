-- Prove2me | solution 1 for GravesWillems.Serial.last_stage_reduction_improves
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T13:38:58.032816+00:00
-- url     : https://prove2.me/submissions/074007e7-71ef-401c-aef6-3cd6b8cca34d

import Mathlib
import Definitions.Def_GravesWillems_Serial_backlog
import Definitions.Def_GravesWillems_Serial_programP

set_option autoImplicit false

open MeasureTheory

namespace P2M_771b6157

open GravesWillems.Serial

theorem backlogAux_anti (T : ℕ → ℕ) (B B' : ℕ → ℝ) (hBB : ∀ j, B' j ≤ B j) (d : ℤ → ℝ) :
    ∀ (r i : ℕ) (t : ℤ), backlogAux T B d r i t ≤ backlogAux T B' d r i t := by
  intro r
  induction r with
  | zero => intro i t; simp [backlogAux]
  | succ r ih =>
    intro i t
    simp only [backlogAux]
    have h1 := ih (i + 1) (t - (T i : ℤ))
    have h2 := hBB i
    apply max_le_max le_rfl
    linarith

theorem intAux {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (d : Ω → ℤ → ℝ) (hd : ∀ τ : ℤ, Integrable (fun ω => d ω τ) μ)
    (T : ℕ → ℕ) (B : ℕ → ℝ) :
    ∀ (r i : ℕ) (t : ℤ), Integrable (fun ω => backlogAux T B (d ω) r i t) μ := by
  intro r
  induction r with
  | zero => intro i t; simp only [backlogAux]; exact integrable_zero _ _ _
  | succ r ih =>
    intro i t
    simp only [backlogAux]
    have hw : Integrable (fun ω => windowDemand (d ω) (t - (T i : ℤ)) t) μ := by
      unfold windowDemand
      exact integrable_finsetSum _ (fun τ _ => hd τ)
    have h2 := (hw.add (ih (i + 1) (t - (T i : ℤ)))).sub (integrable_const (B i))
    have h3 := (integrable_zero Ω ℝ μ).sup h2
    refine h3.congr (Filter.Eventually.of_forall fun ω => ?_)
    rfl

end P2M_771b6157

open MeasureTheory GravesWillems.Serial in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (d : Ω → ℤ → ℝ) (hd : ∀ τ : ℤ, Integrable (fun ω => d ω τ) μ)
    (N : ℕ) (hN : 1 ≤ N) (T : ℕ → ℕ) (D : ℕ → ℝ) (hD0 : D 0 = 0) (hD : Monotone D)
    (h : ℕ → ℝ) (he : ∀ i ∈ Finset.Ico 1 N, 0 ≤ h i - h (i + 1)) (hhN : 0 ≤ h N)
    (B : ℕ → ℝ) (hB : Feasible N T D B)
    (hbind : ∀ i ∈ Finset.Ico 1 N,
      ∑ m ∈ Finset.Icc 1 i, B m = D (∑ m ∈ Finset.Icc 1 i, T m))
    (hstrict : D (∑ m ∈ Finset.Icc 1 N, T m) < ∑ m ∈ Finset.Icc 1 N, B m) :
    Feasible N T D (Function.update B N
        (B N - (∑ m ∈ Finset.Icc 1 N, B m - D (∑ m ∈ Finset.Icc 1 N, T m)))) ∧
    (∀ i ∈ Finset.Icc 1 N,
      ∑ m ∈ Finset.Icc 1 i, Function.update B N
          (B N - (∑ m ∈ Finset.Icc 1 N, B m - D (∑ m ∈ Finset.Icc 1 N, T m))) m
        = D (∑ m ∈ Finset.Icc 1 i, T m)) ∧
    ∀ t : ℤ,
      objective μ d N T h (Function.update B N
          (B N - (∑ m ∈ Finset.Icc 1 N, B m - D (∑ m ∈ Finset.Icc 1 N, T m)))) t
        ≤ objective μ d N T h B t := by
  have hspos : 0 < ∑ m ∈ Finset.Icc 1 N, B m - D (∑ m ∈ Finset.Icc 1 N, T m) := by linarith
  set s := ∑ m ∈ Finset.Icc 1 N, B m - D (∑ m ∈ Finset.Icc 1 N, T m) with hs
  set B' := Function.update B N (B N - s) with hB'
  have hB'apply : ∀ m, B' m = B m - if m = N then s else 0 := by
    intro m
    rw [hB', Function.update_apply]
    split_ifs with h1
    · subst h1; ring
    · ring
  have hle : ∀ j, B' j ≤ B j := by
    intro j; rw [hB'apply]; split_ifs <;> linarith
  have hlow : ∀ i, i < N → ∑ m ∈ Finset.Icc 1 i, B' m = ∑ m ∈ Finset.Icc 1 i, B m := by
    intro i hi
    apply Finset.sum_congr rfl
    intro m hm
    have hmN : m ≠ N := by
      simp only [Finset.mem_Icc] at hm; omega
    rw [hB'apply]; simp [hmN]
  have htop : ∑ m ∈ Finset.Icc 1 N, B' m = D (∑ m ∈ Finset.Icc 1 N, T m) := by
    simp_rw [hB'apply]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']
    have hNm : N ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hN, le_rfl⟩
    rw [if_pos hNm]
    linarith
  have hbindall : ∀ i ∈ Finset.Icc 1 N,
      ∑ m ∈ Finset.Icc 1 i, B' m = D (∑ m ∈ Finset.Icc 1 i, T m) := by
    intro i hi
    rcases Finset.mem_Icc.mp hi with ⟨hi1, hi2⟩
    rcases lt_or_eq_of_le hi2 with hlt | heq
    · rw [hlow i hlt]
      exact hbind i (Finset.mem_Ico.mpr ⟨hi1, hlt⟩)
    · subst heq; exact htop
  have hnonneg : ∀ i ∈ Finset.Icc 1 N, 0 ≤ B' i := by
    intro i hi
    by_cases hiN : i = N
    · subst hiN
      obtain ⟨n, hn⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
      have hprev : ∑ m ∈ Finset.Icc 1 n, B m = D (∑ m ∈ Finset.Icc 1 n, T m) := by
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0; simp [hD0]
        · exact hbind n (Finset.mem_Ico.mpr ⟨hpos, by omega⟩)
      have hsB : ∑ m ∈ Finset.Icc 1 i, B' m = ∑ m ∈ Finset.Icc 1 n, B' m + B' i := by
        rw [hn, Finset.sum_Icc_succ_top (by omega)]
      have hsT : ∑ m ∈ Finset.Icc 1 i, T m = ∑ m ∈ Finset.Icc 1 n, T m + T i := by
        rw [hn, Finset.sum_Icc_succ_top (by omega)]
      have hmono : D (∑ m ∈ Finset.Icc 1 n, T m) ≤ D (∑ m ∈ Finset.Icc 1 i, T m) := by
        apply hD; rw [hsT]; omega
      have hl := hlow n (by omega)
      linarith
    · rw [hB'apply, if_neg hiN]
      simpa using hB.2 i hi
  refine ⟨⟨fun i hi => (hbindall i hi).ge, hnonneg⟩, hbindall, ?_⟩
  intro t
  unfold objective
  have h1 : ∑ i ∈ Finset.Icc 1 N, h i * B' i ≤ ∑ i ∈ Finset.Icc 1 N, h i * B i := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases hiN : i = N
    · subst hiN; exact mul_le_mul_of_nonneg_left (hle i) hhN
    · rw [hB'apply, if_neg hiN]; simp
  have h2 : ∑ i ∈ Finset.Icc 2 N, (h (i - 1) - h i) * ∫ ω, backlog N T B (d ω) i t ∂μ
      ≤ ∑ i ∈ Finset.Icc 2 N, (h (i - 1) - h i) * ∫ ω, backlog N T B' (d ω) i t ∂μ := by
    apply Finset.sum_le_sum
    intro i hi
    rcases Finset.mem_Icc.mp hi with ⟨hi1, hi2⟩
    have hei : 0 ≤ h (i - 1) - h i := by
      have := he (i - 1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
      rwa [Nat.sub_add_cancel (by omega)] at this
    apply mul_le_mul_of_nonneg_left _ hei
    unfold backlog
    exact integral_mono (P2M_771b6157.intAux μ d hd T B _ _ _)
      (P2M_771b6157.intAux μ d hd T B' _ _ _)
      (fun ω => P2M_771b6157.backlogAux_anti T B B' hle (d ω) _ _ _)
  linarith
