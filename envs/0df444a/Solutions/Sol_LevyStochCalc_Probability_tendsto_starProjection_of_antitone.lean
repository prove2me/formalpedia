-- Prove2me | solution 1 for LevyStochCalc.Probability.tendsto_starProjection_of_antitone
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:04:45.316639+00:00
-- url     : https://prove2.me/submissions/1b306a01-00aa-41e7-803f-2af118a2e3d5

import Definitions.Def_LevyStochCalc_Probability_ProjectionLimit_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Orthogonal projections along a decreasing sequence of subspaces

For nested closed subspaces `W ≤ V` the projections compose, `P_W ∘ P_V = P_W`, and Pythagoras
splits the larger projection, `‖P_V x‖² = ‖P_W x‖² + ‖P_V x − P_W x‖²`. Along an antitone sequence
`V 0 ≥ V 1 ≥ ⋯` that makes `n ↦ ‖P_{V n} x‖²` antitone and bounded below, hence convergent, and the
same identity turns its Cauchy property into the Cauchy property of `(P_{V n} x)` itself. The limit
lies in every `V N` and is orthogonal to `⨅ n, V n`, so it *is* the projection onto the
intersection.

This is the Hilbert-space half of the downward `L²` convergence of conditional expectations that
cited result #13b needs; the measure-theoretic half is
`LevyStochCalc/Probability/AEMeasurableInf.lean`, which identifies the intersection of the
`lpMeas` subspaces.

## Main statements

* `starProjection_starProjection_of_le` — the projections compose on nested subspaces.
* `norm_sq_starProjection_of_le` — Pythagoras for nested projections.
* `norm_starProjection_sub_le_of_le` — `‖P_V x − P_U x‖ ≤ ‖P_W x − P_U x‖` for `U ≤ V ≤ W`.
* `tendsto_starProjection_of_antitone` — `P_{V n} x → P_{⨅ V n} x`.
-/

open Filter Topology Submodule

namespace LevyStochCalc.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section Antitone

variable {V : ℕ → Submodule ℝ E} [∀ n, (V n).HasOrthogonalProjection]



theorem _root_.solution (hV : Antitone V)
    (hclosed : ∀ n, IsClosed ((V n : Set E)))
    [(⨅ n, V n).HasOrthogonalProjection] (x : E) :
    Tendsto (fun n => (V n).starProjection x) atTop (𝓝 ((⨅ n, V n).starProjection x)) := by
  set p : ℕ → E := fun n => (V n).starProjection x with hp
  set a : ℕ → ℝ := fun n => ‖p n‖ ^ 2 with ha
  have hanti : Antitone a := antitone_norm_sq_starProjection hV x
  have hbdd : BddBelow (Set.range a) := ⟨0, by rintro _ ⟨n, rfl⟩; positivity⟩
  set L := ⨅ n, a n
  have hL : Tendsto a atTop (𝓝 L) := tendsto_atTop_ciInf hanti hbdd
  have hLle : ∀ n, L ≤ a n := fun n => ciInf_le hbdd n
  have hpy : ∀ n m, n ≤ m → ‖p n - p m‖ ^ 2 = a n - a m := by
    intro n m hnm
    have := norm_sq_starProjection_of_le (hV hnm) x
    simp only [ha, hp] at this ⊢
    linarith
  have hd : ∀ n N, N ≤ n → dist (p n) (p N) ≤ Real.sqrt (a N - L) := by
    intro n N hNn
    rw [dist_comm, dist_eq_norm, ← Real.sqrt_sq (norm_nonneg _), hpy N n hNn]
    exact Real.sqrt_le_sqrt (by linarith [hLle n])
  have hcau : CauchySeq p := by
    refine cauchySeq_of_le_tendsto_0 (fun N => 2 * Real.sqrt (a N - L)) (fun n m N hn hm => ?_) ?_
    · calc dist (p n) (p m) ≤ dist (p n) (p N) + dist (p N) (p m) := dist_triangle _ _ _
        _ ≤ Real.sqrt (a N - L) + Real.sqrt (a N - L) := by
          gcongr
          · exact hd n N hn
          · rw [dist_comm]; exact hd m N hm
        _ = 2 * Real.sqrt (a N - L) := by ring
    · have : Tendsto (fun N => a N - L) atTop (𝓝 0) := by
        simpa using hL.sub_const L
      simpa using (this.sqrt).const_mul 2
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcau
  set W := ⨅ n, V n
  have hyW : y ∈ W := by
    rw [Submodule.mem_iInf]
    intro k
    refine (hclosed k).mem_of_tendsto hy ?_
    filter_upwards [Filter.eventually_ge_atTop k] with m hm
    exact hV hm ((V m).starProjection_apply_mem x)
  have horth : ∀ w ∈ W, inner ℝ (x - y) w = 0 := by
    intro w hw
    have hlim : Tendsto (fun n => inner ℝ (x - p n) w) atTop (𝓝 (inner ℝ (x - y) w)) :=
      ((tendsto_const_nhds.sub hy).inner tendsto_const_nhds)
    have hz : ∀ n, inner ℝ (x - p n) w = 0 := by
      intro n
      have hwn : w ∈ V n := (Submodule.mem_iInf _).1 hw n
      exact (V n).sub_starProjection_mem_orthogonal x w hwn |> fun h => by
        rw [real_inner_comm]; exact h
    simp only [hz] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  have heq : W.starProjection x = y :=
    Submodule.eq_starProjection_of_mem_of_inner_eq_zero hyW horth
  rw [heq]
  exact hy
