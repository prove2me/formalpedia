-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.SimplePredictable.sum_xi_mul_simpleIntegral_sub_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:05:14.069898+00:00
-- url     : https://prove2.me/submissions/59ab8cc1-5103-45bf-a012-972a2097fff4

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraProduct

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraProduct.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
private lemma LevyStochCalc.Brownian.Ito.min_min_of_le {a b t : ℝ} (h : a ≤ b) : min a (min b t) = min a t := by
  rw [← min_assoc, min_eq_left h]
private lemma LevyStochCalc.Brownian.Ito.min_min_of_le' {a b t : ℝ} (h : a ≤ b) : min b (min a t) = min a t := by
  rw [← min_assoc, min_eq_right h]
/-- **The elementary integral against an elementary integral.** Summing the increments of
`simpleIntegral W K` against the coefficients of `G` gives the elementary integral of the
product `G · K` on the common refinement. -/
theorem solution
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (G K : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T)
    (h_eq : G.partition (Fin.last G.N) = K.partition (Fin.last K.N))
    (t : ℝ) (ω : Ω) :
    (∑ i : Fin G.N, G.ξ i ω *
        (LevyStochCalc.Brownian.Ito.simpleIntegral W K (min (G.partition i.succ) t) ω
          - LevyStochCalc.Brownian.Ito.simpleIntegral W K (min (G.partition i.castSucc) t) ω))
      = LevyStochCalc.Brownian.Ito.simpleIntegral W (G.mul_on_common K h_eq) t ω := by
  classical
  set π : Fin (G.mergedM K + 1) → ℝ := G.mergedπ K with hπ
  set L : Fin (G.mergedM K) → Fin G.N := G.mergedIdxMap_left K h_eq with hL
  set R : Fin (G.mergedM K) → Fin K.N := G.mergedIdxMap_right K h_eq with hR
  have hmono : StrictMono π := G.mergedπ_strictMono K
  have hLle : ∀ j, G.partition (L j).castSucc ≤ π j.castSucc :=
    G.mergedIdxMap_left_idx_le K h_eq
  have hLge : ∀ j, π j.succ ≤ G.partition (L j).succ := G.mergedIdxMap_left_idx_ge K h_eq
  -- `K`'s elementary integral, read on the merged partition
  have hK : ∀ u : ℝ, LevyStochCalc.Brownian.Ito.simpleIntegral W K u ω
      = ∑ j : Fin (G.mergedM K), K.ξ (R j) ω
        * (W.W (min (π j.succ) u) ω - W.W (min (π j.castSucc) u) ω) := by
    intro u
    rw [← K.simpleIntegral_refine_intermediate W (G.mergedM K) π (G.mergedπ_zero K)
      (h_eq ▸ G.mergedπ_last K h_eq) hmono R (G.mergedIdxMap_right_idx_le K h_eq)
      (G.mergedIdxMap_right_idx_ge K h_eq) (G.mergedπ_refines_right K) u ω]
    rfl
  set ΔW : Fin (G.mergedM K) → ℝ := fun j =>
    W.W (min (π j.succ) t) ω - W.W (min (π j.castSucc) t) ω with hΔW
  set D : Fin G.N → Fin (G.mergedM K) → ℝ := fun i j =>
    (W.W (min (π j.succ) (min (G.partition i.succ) t)) ω
        - W.W (min (π j.castSucc) (min (G.partition i.succ) t)) ω)
      - (W.W (min (π j.succ) (min (G.partition i.castSucc) t)) ω
        - W.W (min (π j.castSucc) (min (G.partition i.castSucc) t)) ω) with hD
  have hDself : ∀ j, D (L j) j = ΔW j := by
    intro j
    have h1 : π j.castSucc ≤ π j.succ := (hmono Fin.castSucc_lt_succ).le
    have h2 : G.partition (L j).castSucc ≤ π j.castSucc := hLle j
    rw [hD, hΔW]
    simp only
    rw [LevyStochCalc.Brownian.Ito.min_min_of_le (hLge j), LevyStochCalc.Brownian.Ito.min_min_of_le (h1.trans (hLge j)),
      LevyStochCalc.Brownian.Ito.min_min_of_le' (h2.trans h1), LevyStochCalc.Brownian.Ito.min_min_of_le' h2]
    ring
  have hDzero : ∀ (j : Fin (G.mergedM K)) (i : Fin G.N), i ≠ L j → D i j = 0 := by
    intro j i hne
    have h1 : π j.castSucc ≤ π j.succ := (hmono Fin.castSucc_lt_succ).le
    have hGi : G.partition i.castSucc ≤ G.partition i.succ :=
      G.partition_strictMono.monotone Fin.castSucc_lt_succ.le
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle : (i.succ : Fin (G.N + 1)) ≤ (L j).castSucc := by
        rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hlt
      have hstep : G.partition i.succ ≤ π j.castSucc :=
        (G.partition_strictMono.monotone hle).trans (hLle j)
      rw [hD]
      simp only
      rw [LevyStochCalc.Brownian.Ito.min_min_of_le' hstep, LevyStochCalc.Brownian.Ito.min_min_of_le' (hstep.trans h1),
        LevyStochCalc.Brownian.Ito.min_min_of_le' (hGi.trans hstep), LevyStochCalc.Brownian.Ito.min_min_of_le' ((hGi.trans hstep).trans h1)]
      ring
    · have hle : ((L j).succ : Fin (G.N + 1)) ≤ i.castSucc := by
        rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hgt
      have hstep : π j.succ ≤ G.partition i.castSucc :=
        (hLge j).trans (G.partition_strictMono.monotone hle)
      rw [hD]
      simp only
      rw [LevyStochCalc.Brownian.Ito.min_min_of_le (hstep.trans hGi), LevyStochCalc.Brownian.Ito.min_min_of_le (h1.trans (hstep.trans hGi)),
        LevyStochCalc.Brownian.Ito.min_min_of_le hstep, LevyStochCalc.Brownian.Ito.min_min_of_le (h1.trans hstep)]
      ring
  calc (∑ i : Fin G.N, G.ξ i ω *
          (LevyStochCalc.Brownian.Ito.simpleIntegral W K (min (G.partition i.succ) t) ω
            - LevyStochCalc.Brownian.Ito.simpleIntegral W K (min (G.partition i.castSucc) t) ω))
      = ∑ i : Fin G.N, ∑ j : Fin (G.mergedM K), G.ξ i ω * (K.ξ (R j) ω * D i j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hK, hK, ← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hD]; ring
    _ = ∑ j : Fin (G.mergedM K), ∑ i : Fin G.N, G.ξ i ω * (K.ξ (R j) ω * D i j) :=
        Finset.sum_comm
    _ = ∑ j : Fin (G.mergedM K), G.ξ (L j) ω * K.ξ (R j) ω * ΔW j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_eq_single (L j)
          (fun i _ hne => by rw [hDzero j i hne, mul_zero, mul_zero])
          (fun hnm => absurd (Finset.mem_univ _) hnm), hDself j]
        ring
    _ = LevyStochCalc.Brownian.Ito.simpleIntegral W (G.mul_on_common K h_eq) t ω := by
        unfold LevyStochCalc.Brownian.Ito.simpleIntegral
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hΔW]
        rfl
