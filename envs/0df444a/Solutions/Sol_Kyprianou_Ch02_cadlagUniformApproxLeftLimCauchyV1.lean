-- Prove2me | solution 1 for Kyprianou.Ch02.cadlagUniformApproxLeftLimCauchyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:10:13.425288+00:00
-- url     : https://prove2.me/submissions/6f9ec458-d5d1-4042-a45a-4dd2112a45f8

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open Filter Set Topology ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (f : ℝ≥0 → ℝ) (t : ℝ≥0) (ht : 0 < t)
    (F : ℕ → ℝ≥0 → ℝ) (l : ℕ → ℝ)
    (hl : ∀ n, Tendsto (F n) (𝓝[<] t) (𝓝 (l n)))
    (huni : ∀ δ : ℝ, 0 < δ →
      ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ s : ℝ≥0, s ≤ t + 1 →
        |F n s - f s| < δ) :
    CauchySeq l := by
  let T : ℝ≥0 := t + 1
  have htT : t < T := by
    dsimp [T]
    linarith
  haveI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hstayL : ∀ᶠ s in 𝓝[<] t, s ≤ T := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hs.le.trans htT.le
  have huni' : ∀ δ : ℝ, 0 < δ →
      ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ s : ℝ≥0, s ≤ T →
        |F n s - f s| < δ := by
    simpa only [T] using huni
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := huni' (ε / 4) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hLm : ∀ᶠ s in 𝓝[<] t,
      dist (F m s) (l m) < ε / 4 :=
    (hl m).eventually (Metric.ball_mem_nhds _ (by positivity))
  have hLn : ∀ᶠ s in 𝓝[<] t,
      dist (F n s) (l n) < ε / 4 :=
    (hl n).eventually (Metric.ball_mem_nhds _ (by positivity))
  obtain ⟨s, ⟨⟨hsm, hsn⟩, hsT⟩⟩ :=
    ((hLm.and hLn).and hstayL).exists
  have hfm : dist (F m s) (f s) < ε / 4 := by
    simpa only [Real.dist_eq] using hN m hm s hsT
  have hfn : dist (f s) (F n s) < ε / 4 := by
    rw [dist_comm]
    simpa only [Real.dist_eq] using hN n hn s hsT
  have hsm' : dist (l m) (F m s) < ε / 4 := by
    rw [dist_comm]
    exact hsm
  have hA := dist_triangle (l m) (f s) (l n)
  have hB := dist_triangle (l m) (F m s) (f s)
  have hC := dist_triangle (f s) (F n s) (l n)
  linarith
