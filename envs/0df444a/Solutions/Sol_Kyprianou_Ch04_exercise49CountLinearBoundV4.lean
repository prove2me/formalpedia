-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49CountLinearBoundV4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:06:06.392576+00:00
-- url     : https://prove2.me/submissions/552624fc-345f-4bcc-acf6-30887a887d86

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
variable {Ω : Type} [MeasurableSpace Ω]
theorem solution (a : ℕ → ℝ) (K : ℝ → ℕ) (c : ℝ) (hc : 0 < c) (N : ℕ)
    (ha : ∀ n ≥ N, c * (n : ℝ) ≤ ∑ i ∈ Finset.range n, a i)
    (hK : ∀ t n, n < K t ↔ (∑ i ∈ Finset.range (n+1), a i) ≤ t) :
    ∀ t ≥ 0, (K t : ℝ) ≤ N + t / c := by
  intro t ht
  by_cases h : K t ≤ N
  · have hh : (K t : ℝ) ≤ N := by exact_mod_cast h
    linarith [div_nonneg ht hc.le]
  · have hk : 0 < K t := by omega
    have hkn : N ≤ K t := by omega
    obtain ⟨k,hk'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    have hsum := (hK t k).1 (by omega)
    have hh := (ha (K t) hkn).trans (by simpa [hk', Nat.succ_eq_add_one] using hsum)
    have hdiv : (K t : ℝ) ≤ t / c := (le_div_iff₀ hc).2 (by linarith)
    linarith [show (0 : ℝ) ≤ N by positivity]
