-- Prove2me | solution 1 for Kyprianou.Ch03.levy_pastFin_indep_successive_future
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T22:32:46.98396+00:00
-- url     : https://prove2.me/submissions/75dbaa23-5c96-4232-b7d9-4aa69ac2d8d7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_DurrettProbability_Brownian
import Theorems.Thm_Kyprianou_Ch03_levy_shifted_process_measurable
import Theorems.Thm_Kyprianou_Ch03_levy_pastEval_eq_cumsum_increments
import Theorems.Thm_Kyprianou_Ch03_levy_pastIncs_indep_successive_future

open MeasureTheory ProbabilityTheory DurrettProbability Set Finset
open scoped NNReal

set_option autoImplicit false

/-!
Past Finset evaluations ⊥ successive post-`τ` increments.

1. Open measurability.
2. Sort `J ∪ {0,τ}` into monotone past grid `e` ending at `τ`.
3. Open: past successive increments ⊥ future successive increments.
4. Open: evaluations = cumulative past increments.
5. `IndepFun.comp`.
-/

open Kyprianou.Ch03 in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (τ : NNReal)
    (J : Finset (Set.Iic τ))
    (m : ℕ) (lags : Fin (m + 1) → NNReal) (hlags : Monotone lags)
    (h0 : lags 0 = 0) :
    IndepFun
      (fun ω (v : J) => X ((v : Set.Iic τ) : NNReal) ω)
      (fun ω (i : Fin m) =>
        X (τ + lags i.succ) ω - X (τ + lags i.castSucc) ω)
      P := by
  classical
  have hXmeas : ∀ t, Measurable (X t) := by
    intro t
    have hinc : Measurable (fun ω => X (0 + t) ω - X 0 ω) :=
      levy_shifted_process_measurable P X hX 0 t
    simpa [hX.start_zero, zero_add] using hinc
  let Past : Finset NNReal :=
    insert 0 (insert τ (J.image fun v : Set.Iic τ => (v : NNReal)))
  have hPast_le : ∀ s ∈ Past, s ≤ τ := by
    intro s hs
    have hs' : s = 0 ∨ s = τ ∨ s ∈ J.image fun v : Set.Iic τ => (v : NNReal) := by
      simpa [Past] using hs
    rcases hs' with rfl | rfl | hs
    · exact bot_le
    · exact le_rfl
    · rcases mem_image.mp hs with ⟨v, _, rfl⟩; exact v.2
  have hPast_pos : Past.card ≠ 0 := card_ne_zero.mpr ⟨0, mem_insert_self _ _⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Past.card = k + 1 := Nat.exists_eq_succ_of_ne_zero hPast_pos
  let e : Fin (k + 1) ↪o NNReal := Past.orderEmbOfFin hk
  have hrange : Set.range (fun i : Fin (k + 1) => (e i : NNReal)) = (Past : Set NNReal) :=
    range_orderEmbOfFin Past hk
  have he0 : (e 0 : NNReal) = 0 := by
    have h0_mem : (0 : NNReal) ∈ Past := mem_insert_self _ _
    obtain ⟨i, hi⟩ : ∃ i, (e i : NNReal) = 0 := by
      have : (0 : NNReal) ∈ Set.range (fun i : Fin (k + 1) => (e i : NNReal)) := by
        rw [hrange]; exact h0_mem
      exact this
    exact le_antisymm (by rw [← hi]; exact e.monotone (Fin.zero_le i)) bot_le
  have helast : (e (Fin.last k) : NNReal) = τ := by
    have hτ_mem : τ ∈ Past := mem_insert_of_mem (mem_insert_self _ _)
    have hle : (e (Fin.last k) : NNReal) ≤ τ :=
      hPast_le _ (orderEmbOfFin_mem Past hk _)
    obtain ⟨i, hi⟩ : ∃ i, (e i : NNReal) = τ := by
      have : τ ∈ Set.range (fun i : Fin (k + 1) => (e i : NNReal)) := by
        rw [hrange]; exact hτ_mem
      exact this
    exact le_antisymm hle (by rw [← hi]; exact e.monotone (Fin.le_last i))
  have he_le : ∀ i, (e i : NNReal) ≤ τ := fun i =>
    hPast_le _ (orderEmbOfFin_mem Past hk i)
  have hincs :
      IndepFun
        (fun ω (j : Fin k) => X (e j.succ) ω - X (e j.castSucc) ω)
        (fun ω (i : Fin m) => X (τ + lags i.succ) ω - X (τ + lags i.castSucc) ω)
        P :=
    levy_pastIncs_indep_successive_future P X hX τ k (fun i => (e i : NNReal)) he0
      e.monotone helast he_le m lags hlags h0 hXmeas
  let φ : (Fin k → ℝ) → (J → ℝ) := fun s ⟨v, hv⟩ =>
    let hex : ∃ i : Fin (k + 1), (e i : NNReal) = (v : NNReal) := by
      have hv_mem : (v : NNReal) ∈ Past :=
        mem_insert_of_mem (mem_insert_of_mem (mem_image_of_mem _ hv))
      have : (v : NNReal) ∈ Set.range (fun i : Fin (k + 1) => (e i : NNReal)) := by
        rw [hrange]; exact hv_mem
      exact this
    ∑ j : Fin k, if j.castSucc < Classical.choose hex then s j else 0
  have hφ : Measurable φ := by
    refine measurable_pi_lambda _ fun ⟨v, hv⟩ =>
      measurable_fun_sum _ fun j _ => by
        let hex : ∃ i : Fin (k + 1), (e i : NNReal) = (v : NNReal) := by
          have hv_mem : (v : NNReal) ∈ Past :=
            mem_insert_of_mem (mem_insert_of_mem (mem_image_of_mem _ hv))
          have : (v : NNReal) ∈ Set.range (fun i : Fin (k + 1) => (e i : NNReal)) := by
            rw [hrange]; exact hv_mem
          exact this
        by_cases h : j.castSucc < Classical.choose hex
        · convert (measurable_pi_apply j : Measurable fun s : Fin k → ℝ => s j); simp [h]
        · convert (measurable_const : Measurable fun _ : Fin k → ℝ => (0 : ℝ)); simp [h]
  have hpast_eq :
      (fun ω (v : J) => X ((v : Set.Iic τ) : NNReal) ω) =
        fun ω => φ (fun j => X (e j.succ) ω - X (e j.castSucc) ω) := by
    funext ω ⟨v, hv⟩
    let hex : ∃ i : Fin (k + 1), (e i : NNReal) = (v : NNReal) := by
      have hv_mem : (v : NNReal) ∈ Past :=
        mem_insert_of_mem (mem_insert_of_mem (mem_image_of_mem _ hv))
      have : (v : NNReal) ∈ Set.range (fun i : Fin (k + 1) => (e i : NNReal)) := by
        rw [hrange]; exact hv_mem
      exact this
    simpa [φ] using
      levy_pastEval_eq_cumsum_increments X hX.start_zero k (fun i => (e i : NNReal)) he0
        (v : NNReal) (Classical.choose hex) (Classical.choose_spec hex) ω
  have hInd := IndepFun.comp hincs hφ measurable_id
  rw [hpast_eq]
  exact hInd
