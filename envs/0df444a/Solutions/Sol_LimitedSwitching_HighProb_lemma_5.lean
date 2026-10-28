-- Prove2me | solution 1 for LimitedSwitching.HighProb.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-28T07:04:12.832381+00:00
-- url     : https://prove2.me/submissions/46546af6-c4c4-4015-94af-250885030ad6

import Mathlib
import Definitions.Def_LimitedSwitching_HighProb_Setting


namespace PriorSwitching
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Aux_lemma17
open LimitedSwitching.HighProb

theorem argmin_le {n : ℕ} [NeZero n] (v : Fin n → ℝ) (j : Fin n) :
    v (argminFin v) ≤ v j := by
  have hmem : argminFin v ∈
      Finset.univ.filter (fun i => v i = Finset.univ.inf' Finset.univ_nonempty v) := by
    unfold argminFin
    exact Finset.min'_mem _ _
  rw [Finset.mem_filter] at hmem
  rw [hmem.2]
  exact Finset.inf'_le _ (Finset.mem_univ j)

theorem btl {n : ℕ} [NeZero n] (ℓ : ℕ → Fin n → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1),
        ℓ t (argminFin (fun j => ∑ s ∈ Finset.range (t + 1), ℓ s j))
      ≤ ∑ s ∈ Finset.range (T + 1),
        ℓ s (argminFin (fun j => ∑ s ∈ Finset.range (T + 1), ℓ s j)) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun s => ℓ s _) (T + 1)]
    have h := argmin_le (fun j => ∑ s ∈ Finset.range (T + 1), ℓ s j)
      (argminFin (fun j => ∑ s ∈ Finset.range (T + 1 + 1), ℓ s j))
    linarith

end Aux_lemma17

open LimitedSwitching.HighProb in
theorem solution {n : ℕ} [NeZero n] (ℓ : ℕ → Fin n → ℝ) (T : ℕ) (i : Fin n) :
    ∑ t ∈ Finset.range (T + 1),
        ℓ t (argminFin (fun j => ∑ s ∈ Finset.range (t + 1), ℓ s j))
      ≤ ∑ t ∈ Finset.range (T + 1), ℓ t i := by
  have h1 := Aux_lemma17.btl ℓ T
  have h2 := Aux_lemma17.argmin_le (fun j => ∑ s ∈ Finset.range (T + 1), ℓ s j) i
  linarith

end PriorSwitching

open LimitedSwitching.HighProb
namespace Queelius.Switching

lemma sum_shift (f : ℕ → ℝ) (T : ℕ) :
    ∑ s ∈ Finset.range (T+1), f (s+1) = ∑ t ∈ Finset.Icc 1 (T+1), f t := by
  apply Finset.sum_bij (fun s _ => s+1)
  · intro s hs
    simp only [Finset.mem_range] at hs
    simp only [Finset.mem_Icc]
    omega
  · intro s hs t ht he
    omega
  · intro t ht
    simp only [Finset.mem_Icc] at ht
    refine ⟨t-1, by simp only [Finset.mem_range]; omega, by omega⟩
  · intro s hs
    rfl

lemma sum_no_zero (f : ℕ → ℝ) (T : ℕ) :
    ∑ s ∈ Finset.range (T+1), (if s=0 then 0 else f s) = ∑ t ∈ Finset.Icc 1 T, f t := by
  have hsub : Finset.Icc 1 T ⊆ Finset.range (T+1) := by
    intro t ht
    simp only [Finset.mem_Icc, Finset.mem_range] at *
    omega
  calc
    _ = ∑ t ∈ Finset.Icc 1 T, (if t=0 then 0 else f t) := by
      symm
      apply Finset.sum_subset hsub
      intro t ht hn
      have he : t=0 := by
        simp only [Finset.mem_range] at ht
        simp only [Finset.mem_Icc, not_and_or, not_le] at hn
        omega
      simp [he]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      simp only [Finset.mem_Icc] at ht
      simp [show t≠0 by omega]

lemma switch_count_bound {n : ℕ} (a : ℕ → Fin n) (T : ℕ) :
    ((Finset.Icc 1 T).filter (fun t => a t ≠ a (t+1))).card ≤ switches T a + 1 := by
  let S := (Finset.Icc 1 T).filter (fun t => a t ≠ a (t+1))
  let U := (Finset.Icc 2 T).filter (fun t => a t ≠ a (t-1))
  have hsub : S.image (fun t => t+1) ⊆ insert (T+1) U := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    have ht' := Finset.mem_filter.mp ht
    have htt := Finset.mem_Icc.mp ht'.1
    by_cases he : t+1=T+1
    · simp [he]
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      simpa using Ne.symm ht'.2
  have hc : (S.image (fun t => t+1)).card = S.card :=
    Finset.card_image_of_injective S (by intro i j h; dsimp only at h; omega)
  have hh := Finset.card_le_card hsub
  rw [hc] at hh
  have hi := Finset.card_insert_le (T+1) U
  change S.card ≤ U.card+1
  omega

lemma loss_error_bound {n : ℕ} (a : ℕ → Fin n) (ℓ : ℕ → Fin n → ℝ) (T : ℕ)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ t ∈ Finset.Icc 1 T, ∀ i j, |ℓ t i - ℓ t j| ≤ M) :
    ∑ t ∈ Finset.Icc 1 T, (ℓ t (a t) - ℓ t (a (t+1))) ≤
      M*((switches T a : ℝ)+1) := by
  let S := (Finset.Icc 1 T).filter (fun t => a t ≠ a (t+1))
  have hsum : (∑ t ∈ Finset.Icc 1 T, (ℓ t (a t)-ℓ t (a (t+1)))) ≤
      ∑ t ∈ Finset.Icc 1 T, (if a t ≠ a (t+1) then M else 0) := by
    apply Finset.sum_le_sum
    intro t ht
    by_cases he : a t = a (t+1)
    · simp [he]
    · simp only [if_pos he]
      exact le_trans (le_abs_self _) (hM t ht _ _)
  have heq : (∑ t ∈ Finset.Icc 1 T, (if a t ≠ a (t+1) then M else 0)) = (S.card : ℝ)*M := by
    rw [← Finset.sum_filter]
    simp [S]
  rw [heq] at hsum
  have hc : (S.card : ℝ) ≤ (switches T a : ℝ)+1 := by
    exact_mod_cast switch_count_bound a T
  nlinarith

theorem comparator_bound {n : ℕ} [NeZero n] (P ℓ : ℕ → Fin n → ℝ) (T : ℕ)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ t ∈ Finset.Icc 1 T, ∀ i j, |ℓ t i-ℓ t j| ≤ M)
    (i : Fin n) :
    (∑ t ∈ Finset.Icc 1 T, ℓ t (fplPlay P ℓ t)) - (∑ t ∈ Finset.Icc 1 T, ℓ t i) ≤
      M*((switches T (fplPlay P ℓ) : ℝ)+1) +
        (⨆ j, ∑ t ∈ Finset.Icc 1 (T+1), P t j) -
        ∑ t ∈ Finset.Icc 1 (T+1), P t (fplPlay P ℓ t) := by
  have hb := PriorSwitching.solution (fun s j => (if s=0 then 0 else ℓ s j) + P (s+1) j) T i
  change (∑ s ∈ Finset.range (T+1),
      ((if s=0 then 0 else ℓ s (fplPlay P ℓ (s+1))) + P (s+1) (fplPlay P ℓ (s+1)))) ≤
      ∑ s ∈ Finset.range (T+1), ((if s=0 then 0 else ℓ s i) + P (s+1) i) at hb
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hb
  rw [sum_no_zero, sum_shift (fun t => P t (fplPlay P ℓ t)) T,
    sum_no_zero, sum_shift (fun t => P t i) T] at hb
  have hp : (∑ t ∈ Finset.Icc 1 (T+1), P t i) ≤
      (⨆ j, ∑ t ∈ Finset.Icc 1 (T+1), P t j) := le_ciSup (Finite.bddAbove_range (fun j => ∑ t ∈ Finset.Icc 1 (T+1), P t j)) i
  have he : (∑ t ∈ Finset.Icc 1 T, ℓ t (fplPlay P ℓ t)) =
      (∑ t ∈ Finset.Icc 1 T, ℓ t (fplPlay P ℓ (t+1))) +
      ∑ t ∈ Finset.Icc 1 T, (ℓ t (fplPlay P ℓ t)-ℓ t (fplPlay P ℓ (t+1))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have herr := loss_error_bound (fplPlay P ℓ) ℓ T M hM0 hM
  linarith

end Queelius.Switching

open LimitedSwitching.HighProb in
theorem solution {n : ℕ} [NeZero n] (P : ℕ → Fin n → ℝ) (ℓ : ℕ → Fin n → ℝ) (T : ℕ) (M : ℝ)
    (hM0 : 0 ≤ M) (hM : ∀ t ∈ Finset.Icc 1 T, ∀ i j, |ℓ t i-ℓ t j| ≤ M) :
    regret T ℓ (fplPlay P ℓ) ≤ M*((switches T (fplPlay P ℓ) : ℝ)+1) +
      (⨆ i, ∑ t ∈ Finset.Icc 1 (T+1), P t i) -
      ∑ t ∈ Finset.Icc 1 (T+1), P t (fplPlay P ℓ t) := by
  let i := argminFin (fun j => ∑ t ∈ Finset.Icc 1 T, ℓ t j)
  have hmin : (⨅ j, ∑ t ∈ Finset.Icc 1 T, ℓ t j) = ∑ t ∈ Finset.Icc 1 T, ℓ t i := by
    apply le_antisymm
    · exact ciInf_le (Finite.bddBelow_range _) i
    · apply le_ciInf
      intro j
      exact PriorSwitching.Aux_lemma17.argmin_le (fun j => ∑ t ∈ Finset.Icc 1 T, ℓ t j) j
  unfold regret
  rw [hmin]
  exact Queelius.Switching.comparator_bound P ℓ T M hM0 hM i


namespace Queelius.Switching.Controls

theorem zero_horizon {n : ℕ} [NeZero n] (ℓ : ℕ → Fin n → ℝ) (a : ℕ → Fin n) :
    regret 0 ℓ a = 0 := by simp [regret]

theorem constant_action_switches {n : ℕ} (i : Fin n) (T : ℕ) :
    switches T (fun _ => i) = 0 := by simp [switches]

theorem terminal_switch :
    switches 1 (fun t : ℕ => (if t ≤ 1 then 0 else 1 : Fin 2)) = 0 ∧
    switches 2 (fun t : ℕ => (if t ≤ 1 then 0 else 1 : Fin 2)) = 1 ∧
    ((Finset.Icc 1 1).filter (fun t : ℕ =>
      (if t ≤ 1 then 0 else 1 : Fin 2) ≠ (if t+1 ≤ 1 then 0 else 1 : Fin 2))).card = 1 := by
  decide

end Queelius.Switching.Controls
