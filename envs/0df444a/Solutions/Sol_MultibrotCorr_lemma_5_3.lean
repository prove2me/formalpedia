-- Prove2me | solution 1 for MultibrotCorr.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T01:58:27.092857+00:00
-- url     : https://prove2.me/submissions/1fa80917-26af-4a0f-bcb1-85c78381cd65

import Mathlib
import Definitions.Def_mcorr_branches

open Set Filter Topology Finset

namespace MultibrotCorr

lemma step_growth (e : UnicriticalExponent) (c z w : ℂ)
    (hw : w ∈ unicriticalCorr e.p e.q c z) (hz : (2:ℝ) ^ e.q + ‖c‖ + 1 ≤ ‖z‖) :
    ‖z‖ + 1 ≤ ‖w‖ := by
  have hw' : (w - c) ^ e.q = z ^ e.p := hw
  have h2 : (1:ℝ) ≤ 2 ^ e.q := one_le_pow₀ (by norm_num)
  have ht : (1:ℝ) ≤ ‖z‖ := by nlinarith [norm_nonneg c]
  have h3 : ‖z‖ ≤ ‖z‖ ^ (e.p - e.q) :=
    le_self_pow₀ ht (by have := e.hpq; omega)
  have h4 : ‖w - c‖ ^ e.q = ‖z‖ ^ e.q * ‖z‖ ^ (e.p - e.q) := by
    rw [← norm_pow, hw', norm_pow, ← pow_add]
    congr 1; have := e.hpq; omega
  have h5 : (2 * ‖z‖) ^ e.q ≤ ‖w - c‖ ^ e.q := by
    have h8 : (2:ℝ) ^ e.q ≤ ‖z‖ ^ (e.p - e.q) := by
      have : (2:ℝ) ^ e.q ≤ ‖z‖ := by linarith [norm_nonneg c]
      linarith
    rw [h4, mul_pow, mul_comm (‖z‖ ^ e.q)]
    exact mul_le_mul_of_nonneg_right h8 (pow_nonneg (norm_nonneg z) _)
  have h6 : 2 * ‖z‖ ≤ ‖w - c‖ := by
    by_contra h
    push Not at h
    have := pow_lt_pow_left₀ h (norm_nonneg _) (Nat.pos_iff_ne_zero.mp e.hq)
    linarith
  have h7 : ‖w - c‖ ≤ ‖w‖ + ‖c‖ := by
    have := norm_sub_le w c; linarith
  linarith [norm_nonneg c]

lemma orbit_bound (e : UnicriticalExponent) (c : ℂ) (w : ℕ → ℂ)
    (hw : ∀ i, w (i + 1) ∈ unicriticalCorr e.p e.q c (w i))
    (hb : ∃ R, ∀ i, ‖w i‖ ≤ R) (i : ℕ) : ‖w i‖ ≤ (2:ℝ) ^ e.q + ‖c‖ + 1 := by
  obtain ⟨R, hR⟩ := hb
  by_contra h
  push Not at h
  have key : ∀ k, ‖w i‖ + k ≤ ‖w (i + k)‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := step_growth e c _ _ (hw (i + k)) (by push_cast at ih ⊢; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
      push_cast
      have e1 : i + (k + 1) = i + k + 1 := by ring
      rw [e1]; linarith
  obtain ⟨k, hk⟩ := exists_nat_gt R
  have := key k
  have := hR (i + k)
  linarith [norm_nonneg (w i)]

theorem lemma_5_3_aux (e : UnicriticalExponent) :
    IsClosed {p : ℂ × ℂ | p.2 ∈ filledJulia e p.1} := by
  apply isClosed_of_closure_subset
  intro p hp
  obtain ⟨u, hu, hup⟩ := mem_closure_iff_seq_limit.mp hp
  obtain ⟨N, hN⟩ : ∃ N : ℝ, ∀ n, ‖(u n).1‖ ≤ N := by
    have h1 : Tendsto (fun n => (u n).1) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hup
    have : Bornology.IsBounded (insert p.1 (Set.range fun n => (u n).1)) :=
      h1.isCompact_insert_range.isBounded
    obtain ⟨N, hN⟩ := this.exists_norm_le
    exact ⟨N, fun n => hN _ (Set.mem_insert_of_mem _ ⟨n, rfl⟩)⟩
  have hex : ∀ n, ∃ w : ℕ → ℂ, w 0 = (u n).2 ∧ (∀ i, w (i + 1) ∈ unicriticalCorr e.p e.q (u n).1 (w i)) ∧
      ∃ R, ∀ i, ‖w i‖ ≤ R := fun n => by
    obtain ⟨w, ⟨h0, h1⟩, hb⟩ := hu n
    exact ⟨w, h0, h1, hb⟩
  choose w hw0 hw1 hwb using hex
  set T : ℝ := (2:ℝ) ^ e.q + N + 1 with hT
  have hmem : ∀ n, w n ∈ Set.pi Set.univ (fun _ : ℕ => Metric.closedBall (0:ℂ) T) := by
    intro n i _
    rw [mem_closedBall_zero_iff]
    have := orbit_bound e _ (w n) (hw1 n) (hwb n) i
    have := hN n
    linarith
  have hcomp : IsCompact (Set.pi Set.univ (fun _ : ℕ => Metric.closedBall (0:ℂ) T)) :=
    isCompact_univ_pi (fun _ => isCompact_closedBall _ _)
  obtain ⟨W, hWmem, φ, hφ, hlim⟩ := hcomp.tendsto_subseq hmem
  have hpt : ∀ i, Tendsto (fun n => w (φ n) i) atTop (𝓝 (W i)) := fun i =>
    tendsto_pi_nhds.mp hlim i
  have hc : Tendsto (fun n => (u (φ n)).1) atTop (𝓝 p.1) :=
    ((continuous_fst.tendsto p).comp hup).comp hφ.tendsto_atTop
  have hz : Tendsto (fun n => (u (φ n)).2) atTop (𝓝 p.2) :=
    ((continuous_snd.tendsto p).comp hup).comp hφ.tendsto_atTop
  refine ⟨W, ⟨?_, ?_⟩, T, fun i => ?_⟩
  · have := hpt 0
    simp only [hw0] at this
    exact tendsto_nhds_unique this hz
  · intro i
    show (W (i + 1) - p.1) ^ e.q = W i ^ e.p
    have h1 : Tendsto (fun n => (w (φ n) (i + 1) - (u (φ n)).1) ^ e.q) atTop
        (𝓝 ((W (i + 1) - p.1) ^ e.q)) := ((hpt (i + 1)).sub hc).pow _
    have h2 : Tendsto (fun n => (w (φ n) i) ^ e.p) atTop (𝓝 (W i ^ e.p)) := (hpt i).pow _
    refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
    exact (hw1 (φ n) i).symm
  · have := hWmem i (Set.mem_univ i)
    simpa using this

end MultibrotCorr

theorem solution (e : MultibrotCorr.UnicriticalExponent) :
    IsClosed {p : ℂ × ℂ | p.2 ∈ MultibrotCorr.filledJulia e p.1} :=
  MultibrotCorr.lemma_5_3_aux e
