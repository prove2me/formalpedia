-- Prove2me | solution 1 for Kyprianou.Ch03.levy_future_finDim_indep_pastSigma
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T17:22:49.430947+00:00
-- url     : https://prove2.me/submissions/1254d369-681e-4246-bd83-107bb03eaf33
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_DurrettProbability_Brownian
import Theorems.Thm_Kyprianou_Ch03_levy_shifted_process_measurable
import Theorems.Thm_Kyprianou_Ch03_levy_pastFin_indep_successive_future
import Theorems.Thm_Kyprianou_Ch03_levy_future_inc_eq_cumsum_successive

open MeasureTheory ProbabilityTheory DurrettProbability Set Finset
open scoped NNReal

set_option autoImplicit false

/-!
Finite-dimensional future/past independence for Lévy processes.

Reduction:
1. Open measurability of shifted increments (`levy_shifted_process_measurable`).
2. Sort future lags `I` into a monotone grid based at `0`.
3. Open: past evaluations `IndepFun` successive post-`τ` increments
   (`levy_pastFin_indep_successive_future`).
4. Open: pathwise telescoping identity (`levy_future_inc_eq_cumsum_successive`).
5. Measurable cumulative-sum map + `IndepFun.comp` recovers the Finset-indexed target.
-/

open Kyprianou.Ch03 in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (τ : NNReal)
    (I : Finset NNReal)
    (J : Finset (Set.Iic τ)) :
    IndepFun
      (fun ω (u : I) => X (τ + (u : NNReal)) ω - X τ ω)
      (fun ω (v : J) => X ((v : Set.Iic τ) : NNReal) ω)
      P := by
  classical
  have hXmeas : ∀ t, Measurable (X t) := by
    intro t
    have hinc : Measurable (fun ω => X (0 + t) ω - X 0 ω) :=
      levy_shifted_process_measurable P X hX 0 t
    simpa [hX.start_zero, zero_add] using hinc
  -- Sort future lags with base 0
  let S : Finset NNReal := insert 0 I
  have hS_pos : S.card ≠ 0 := card_ne_zero.mpr ⟨0, mem_insert_self _ _⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, S.card = m + 1 := Nat.exists_eq_succ_of_ne_zero hS_pos
  let lags : Fin (m + 1) ↪o NNReal := S.orderEmbOfFin hm
  have hlags_mono : Monotone (fun i : Fin (m + 1) => (lags i : NNReal)) := lags.monotone
  have h0 : (lags (0 : Fin (m + 1)) : NNReal) = 0 := by
    have h0_mem : (0 : NNReal) ∈ S := mem_insert_self _ _
    have hle : (lags 0 : NNReal) ≤ 0 := by
      obtain ⟨i, hi⟩ : ∃ i, (lags i : NNReal) = 0 := by
        have hrange : Set.range (fun i => (lags i : NNReal)) = (S : Set NNReal) :=
          range_orderEmbOfFin S hm
        have : (0 : NNReal) ∈ Set.range (fun i => (lags i : NNReal)) := by
          rw [hrange]; exact h0_mem
        exact this
      rw [← hi]
      exact lags.monotone (Fin.zero_le i)
    exact le_antisymm hle bot_le
  have hmem_lags : ∀ u ∈ I, ∃ i : Fin (m + 1), (lags i : NNReal) = u := by
    intro u hu
    have : u ∈ S := mem_insert_of_mem hu
    have hrange : Set.range (fun i => (lags i : NNReal)) = (S : Set NNReal) :=
      range_orderEmbOfFin S hm
    have : u ∈ Set.range (fun i => (lags i : NNReal)) := by rw [hrange]; exact this
    exact this
  -- Open: past ⟂ successive future increments
  have hsucc :
      IndepFun
        (fun ω (v : J) => X ((v : Set.Iic τ) : NNReal) ω)
        (fun ω (i : Fin m) =>
          X (τ + lags i.succ) ω - X (τ + lags i.castSucc) ω)
        P :=
    levy_pastFin_indep_successive_future P X hX τ J m
      (fun i => (lags i : NNReal)) hlags_mono h0
  let succInc : Omega → Fin m → ℝ := fun ω i =>
    X (τ + lags i.succ) ω - X (τ + lags i.castSucc) ω
  -- Cumulative-sum map on the successive-increment coordinate space
  let φ : (Fin m → ℝ) → (I → ℝ) := fun s ⟨u, hu⟩ =>
    let i_u := Classical.choose (hmem_lags u hu)
    ∑ i : Fin m, if i.succ ≤ i_u then s i else 0
  have hφ : Measurable φ := by
    refine measurable_pi_lambda _ fun ⟨u, hu⟩ => ?_
    change Measurable fun s : Fin m → ℝ =>
      ∑ i : Fin m, if i.succ ≤ Classical.choose (hmem_lags u hu) then s i else 0
    exact measurable_fun_sum _ fun i _ => by
      by_cases h : i.succ ≤ Classical.choose (hmem_lags u hu)
      · convert (measurable_pi_apply i : Measurable fun s : Fin m → ℝ => s i)
        simp [h]
      · convert (measurable_const : Measurable fun _ : Fin m → ℝ => (0 : ℝ))
        simp [h]
  have hφ_eq :
      (fun ω (u : I) => X (τ + (u : NNReal)) ω - X τ ω) =
        fun ω => φ (succInc ω) := by
    funext ω ⟨u, hu⟩
    let i_u := Classical.choose (hmem_lags u hu)
    have hi_u : (lags i_u : NNReal) = u := Classical.choose_spec (hmem_lags u hu)
    have htele :=
      levy_future_inc_eq_cumsum_successive X τ m (fun i => (lags i : NNReal))
        hlags_mono h0 u i_u hi_u ω
    -- Align φ's choose with the same i_u used above (definitional)
    change X (τ + u) ω - X τ ω =
      ∑ i : Fin m, if i.succ ≤ Classical.choose (hmem_lags u hu) then succInc ω i else 0
    simpa [succInc, i_u] using htele
  have hInd :
      IndepFun
        (fun ω (v : J) => X ((v : Set.Iic τ) : NNReal) ω)
        (fun ω => φ (succInc ω))
        P :=
    hsucc.comp measurable_id hφ
  rw [hφ_eq]
  exact hInd.symm
