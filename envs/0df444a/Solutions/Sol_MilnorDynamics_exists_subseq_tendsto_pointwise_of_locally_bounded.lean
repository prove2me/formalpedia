-- Prove2me | solution 1 for MilnorDynamics.exists_subseq_tendsto_pointwise_of_locally_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T01:50:43.465995+00:00
-- url     : https://prove2.me/submissions/95a32ffa-09ed-4260-97ac-277975a757b2

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_exists_subseq_tendsto_of_bounded_on_countable

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- Pointwise extraction for a locally bounded, uniformly equicontinuous family:
a subsequence converges pointwise on `U` to a continuous limit.  The extraction
itself is the published countable-Tychonoff child; the work here is turning
convergence on a countable dense subset into convergence everywhere. -/
theorem solution (U : Set ℂ) (hU : IsOpen U) (f : ℕ → ℂ → ℂ)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ M, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)
    (hmod : ∀ K ⊆ U, IsCompact K → ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ x ∈ K, ∀ y ∈ K,
      ‖x - y‖ < δ → ‖f n x - f n y‖ < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → ℂ, ContinuousOn g U ∧
      ∀ x ∈ U, Tendsto (fun n => f (φ n) x) atTop (nhds (g x)) := by
  classical
  by_cases hUe : U = ∅
  · subst hUe
    exact ⟨id, strictMono_id, fun _ => 0, continuousOn_empty (fun _ : ℂ => 0), by simp⟩
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (α := ℂ)
  have hUne : U.Nonempty := Set.nonempty_iff_ne_empty.mpr hUe
  obtain ⟨s₀, hs₀S, hs₀U⟩ := hSd.exists_mem_open hU hUne
  obtain ⟨D, hD⟩ := (hSc.mono Set.inter_subset_right).exists_eq_range ⟨s₀, hs₀U, hs₀S⟩
  have hDU : ∀ k, D k ∈ U := fun k => (hD.symm ▸ (Set.mem_range_self k : D k ∈ Set.range D)).1
  -- the sequence `D` meets every ball inside `U`
  have hdense : ∀ x ∈ U, ∀ ε > 0, ∃ k, ‖D k - x‖ < ε := by
    intro x hx ε hε
    obtain ⟨s, hsS, hsUb⟩ := hSd.exists_mem_open (hU.inter Metric.isOpen_ball)
      ⟨x, hx, Metric.mem_ball_self hε⟩
    have hsUS : s ∈ U ∩ S := ⟨hsUb.1, hsS⟩
    rw [hD] at hsUS
    obtain ⟨k, hk⟩ := hsUS
    exact ⟨k, by rw [hk]; simpa [dist_eq_norm] using hsUb.2⟩
  have hbd : ∀ k, ∃ M, ∀ n, ‖f n (D k)‖ ≤ M := by
    intro k
    obtain ⟨M, hM⟩ := hb {D k}
      (by intro z hz; obtain rfl := Set.mem_singleton_iff.mp hz; exact hDU k)
      (isCompact_singleton (x := D k))
    exact ⟨M, fun n => hM n (D k) (by simp)⟩
  obtain ⟨φ, hφ, g₀, hg₀⟩ := exists_subseq_tendsto_of_bounded_on_countable D f hbd
  -- the extracted sequence is Cauchy at every point of `U`
  have hcauchy : ∀ x ∈ U, CauchySeq (fun n => f (φ n) x) := by
    intro x hx
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
    have hRpos : 0 < R / 2 := by linarith
    have hKsub : Metric.closedBall x (R / 2) ⊆ U := fun z hz =>
      hRU (by rw [Metric.mem_ball]
              exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith))
    obtain ⟨δ, hδpos, hδmod⟩ :=
      hmod (Metric.closedBall x (R / 2)) hKsub (isCompact_closedBall x (R / 2)) (ε / 4)
        (by linarith)
    obtain ⟨k, hkx⟩ := hdense x hx (min δ (R / 2)) (lt_min hδpos hRpos)
    have hkxK : dist (D k) x < min δ (R / 2) := by rw [dist_eq_norm]; exact hkx
    have hxkδ : ‖x - D k‖ < δ := by
      rw [norm_sub_rev]
      exact lt_of_lt_of_le hkx (min_le_left δ (R / 2))
    have hkxδ : ‖D k - x‖ < δ := lt_of_lt_of_le hkx (min_le_left δ (R / 2))
    have hxK : x ∈ Metric.closedBall x (R / 2) := Metric.mem_closedBall_self hRpos.le
    have hkK : D k ∈ Metric.closedBall x (R / 2) := by
      rw [Metric.mem_closedBall]
      exact le_of_lt (lt_of_lt_of_le hkxK (min_le_right δ (R / 2)))
    have hkconv := hg₀ k
    rw [Metric.tendsto_atTop] at hkconv
    obtain ⟨N, hN⟩ := hkconv (ε / 4) (by linarith)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 : dist (f (φ m) x) (f (φ m) (D k)) < ε / 4 := by
      rw [dist_eq_norm]
      exact hδmod (φ m) x hxK (D k) hkK hxkδ
    have h3 : dist (f (φ n) (D k)) (f (φ n) x) < ε / 4 := by
      rw [dist_eq_norm]
      exact hδmod (φ n) (D k) hkK x hxK hkxδ
    have h2 : dist (f (φ m) (D k)) (f (φ n) (D k)) < ε / 2 := by
      have hm' := hN m hm
      have hn' := hN n hn
      calc dist (f (φ m) (D k)) (f (φ n) (D k))
          ≤ dist (f (φ m) (D k)) (g₀ k) + dist (g₀ k) (f (φ n) (D k)) :=
            dist_triangle _ _ _
        _ = dist (f (φ m) (D k)) (g₀ k) + dist (f (φ n) (D k)) (g₀ k) := by
            rw [dist_comm (g₀ k)]
        _ < ε / 4 + ε / 4 := add_lt_add hm' hn'
        _ = ε / 2 := by ring
    calc dist (f (φ m) x) (f (φ n) x)
        ≤ dist (f (φ m) x) (f (φ m) (D k)) + dist (f (φ m) (D k)) (f (φ n) (D k))
            + dist (f (φ n) (D k)) (f (φ n) x) := dist_triangle4 _ _ _ _
      _ < ε := by linarith
  choose G hG using fun x : U => cauchySeq_tendsto_of_complete (hcauchy x x.2)
  refine ⟨φ, hφ, fun z => if h : z ∈ U then G ⟨z, h⟩ else 0, ?_, ?_⟩
  · rw [Metric.continuousOn_iff]
    intro b hb ε hε
    obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hb)
    have hRpos : 0 < R / 2 := by linarith
    have hKsub : Metric.closedBall b (R / 2) ⊆ U := fun z hz =>
      hRU (by rw [Metric.mem_ball]
              exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith))
    obtain ⟨δ, hδpos, hδmod⟩ :=
      hmod (Metric.closedBall b (R / 2)) hKsub (isCompact_closedBall b (R / 2)) (ε / 2)
        (by linarith)
    refine ⟨min δ (R / 2), lt_min hδpos hRpos, fun a ha hab => ?_⟩
    have haK : a ∈ Metric.closedBall b (R / 2) := by
      rw [Metric.mem_closedBall]
      exact le_of_lt (lt_of_lt_of_le hab (min_le_right δ (R / 2)))
    have hab' : ‖a - b‖ < δ := by
      have h := hab
      rw [dist_eq_norm] at h
      exact lt_of_lt_of_le h (min_le_left δ (R / 2))
    have hbK : b ∈ Metric.closedBall b (R / 2) := Metric.mem_closedBall_self hRpos.le
    have hbdd : ∀ n, ‖f (φ n) a - f (φ n) b‖ ≤ ε / 2 := fun n =>
      le_of_lt (hδmod (φ n) a haK b hbK hab')
    have hlim : Tendsto (fun n => ‖f (φ n) a - f (φ n) b‖) atTop
        (nhds ‖G ⟨a, ha⟩ - G ⟨b, hb⟩‖) :=
      ((hG ⟨a, ha⟩).sub (hG ⟨b, hb⟩)).norm
    have hle : ‖G ⟨a, ha⟩ - G ⟨b, hb⟩‖ ≤ ε / 2 :=
      le_of_tendsto hlim (Eventually.of_forall hbdd)
    simp only [dif_pos ha, dif_pos hb, dist_eq_norm]
    exact lt_of_le_of_lt hle (by linarith)
  · intro x hx
    simp only [dif_pos hx]
    exact hG ⟨x, hx⟩
