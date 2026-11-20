-- Prove2me | solution 1 for LevyStochCalc.Probability.tendsto_condExpL2_of_antitone
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:05:37.418418+00:00
-- url     : https://prove2.me/submissions/661e795e-837a-4bf7-8f3a-7c35bc2d1a5d

import Definitions.Def_LevyStochCalc_Probability_CondExpInf_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# `L²` conditional expectations along a decreasing sequence of σ-algebras

For an antitone sequence of sub-σ-algebras the subspaces `lpMeas (m n)` of `L²` are antitone with
intersection `lpMeas (⨅ n, m n)` (`lpMeas_iInf_of_antitone`, over the `limsup` construction of
`LevyStochCalc.Probability.AEMeasurableInf`), and `condExpL2` is the orthogonal projection onto
them. Projections along an antitone chain of closed subspaces converge to the projection onto the
intersection (`LevyStochCalc.Probability.ProjectionLimit`), so

  `𝔼[f | m n] → 𝔼[f | ⨅ n, m n]` in `L²`.

This is a downward, `L²` counterpart of Lévy's upward theorem
`MeasureTheory.tendsto_eLpNorm_condExp`, the `L¹` convergence along an increasing filtration.
Applied at `m n := ℱ (t + 1/(n+1))` for a right-continuous filtration it gives the
right-`L²`-continuity of `t ↦ 𝔼[ξ | ℱ t]` that the càdlàg regularisation of cited result #13b
needs.

## Main statements

* `lpMeas_iInf_of_antitone` — `⨅ n, lpMeas (m n) = lpMeas (⨅ n, m n)`.
* `tendsto_condExpL2_of_antitone` — the `L²` conditional expectations converge.
-/

open MeasureTheory Filter Topology
open scoped MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*}

variable {m : ℕ → MeasurableSpace Ω} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}



theorem _root_.proj_aux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {V : ℕ → Submodule ℝ E} [∀ n, (V n).HasOrthogonalProjection] (hV : Antitone V)
    (hclosed : ∀ n, IsClosed ((V n : Set E)))
    [(⨅ n, V n).HasOrthogonalProjection] (x : E) :
    Tendsto (fun n => (V n).starProjection x) atTop (𝓝 ((⨅ n, V n).starProjection x)) := by
  set p : ℕ → E := fun n => (V n).starProjection x with hp
  set a : ℕ → ℝ := fun n => ‖p n‖ ^ 2 with ha
  have hanti : Antitone a := LevyStochCalc.Probability.antitone_norm_sq_starProjection hV x
  have hbdd : BddBelow (Set.range a) := ⟨0, by rintro _ ⟨n, rfl⟩; positivity⟩
  set L := ⨅ n, a n
  have hL : Tendsto a atTop (𝓝 L) := tendsto_atTop_ciInf hanti hbdd
  have hLle : ∀ n, L ≤ a n := fun n => ciInf_le hbdd n
  have hpy : ∀ n m, n ≤ m → ‖p n - p m‖ ^ 2 = a n - a m := by
    intro n m hnm
    have := LevyStochCalc.Probability.norm_sq_starProjection_of_le (hV hnm) x
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

theorem _root_.solution (hanti : Antitone m) (hle : ∀ n, m n ≤ m₀)
    (hle_inf : (⨅ n, m n) ≤ m₀) (f : Lp ℝ 2 μ) :
    Tendsto (fun n => ((condExpL2 ℝ ℝ (hle n) f : Lp ℝ 2 μ))) atTop
      (𝓝 ((condExpL2 ℝ ℝ hle_inf f : Lp ℝ 2 μ))) := by
  haveI : ∀ n, Fact (m n ≤ m₀) := fun n => ⟨hle n⟩
  haveI : Fact ((⨅ n, m n) ≤ m₀) := ⟨hle_inf⟩
  set V : ℕ → Submodule ℝ (Lp ℝ 2 μ) := fun n => lpMeas ℝ ℝ (m n) 2 μ
  have hV : Antitone V := antitone_lpMeas (m₀ := m₀) hanti
  have heq : (⨅ n, V n) = lpMeas ℝ ℝ (⨅ n, m n) 2 μ := lpMeas_iInf_of_antitone (m₀ := m₀) hanti
  haveI : (⨅ n, V n).HasOrthogonalProjection := by rw [heq]; infer_instance
  have hclosed : ∀ n, IsClosed ((V n : Set (Lp ℝ 2 μ))) := fun n => by
    rw [← Submodule.orthogonal_orthogonal (V n)]; exact Submodule.isClosed_orthogonal _
  have key := proj_aux hV hclosed f
  rw [starProjection_congr heq f] at key
  exact key
