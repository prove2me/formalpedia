-- Prove2me | solution 1 for MaxEntTSP.Main.fact_2_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:34:28.534058+00:00
-- url     : https://prove2.me/submissions/d7acde3f-d3c6-4170-9412-78c750f70859

import Mathlib
import Definitions.Def_MaxEntTSP_Main_Model

open MaxEntTSP.Main MetricTSP Finset in
theorem solution (m : ℕ) (x c : Fin m → Fin m → ℝ)
    (hc : IsMetricCost c) (a b : Fin m) (hab : a ≠ b) (hcost0 : c a b = 0)
    (μ : Finset (Sym2 (Fin m)) → ℝ)
    (hμ : IsTreeDistribution (lpSupport x a b) x μ) :
    (∑ T, μ T * treeCost c (insert (s(a, b)) T)) =
      ∑ e ∈ lpSupport x a b, pairCost c e * pairCost x e := by
  set E := lpSupport x a b with hE
  have hab0 : pairCost c s(a, b) = 0 := by
    simp only [pairCost, Sym2.lift_mk]
    rw [hc.1 b a, hcost0]
    ring
  have hnot : s(a, b) ∉ E := by
    intro h
    rw [hE, lpSupport, Finset.mem_filter] at h
    exact h.2.2.1 rfl
  have step1 : ∀ T, μ T * treeCost c (insert (s(a, b)) T) =
      μ T * ∑ e ∈ E, (if e ∈ T then pairCost c e else 0) := by
    intro T
    by_cases hT : μ T = 0
    · rw [hT, zero_mul, zero_mul]
    · have hsub : T ⊆ E := (hμ.2.1 T hT).1
      have hn : s(a, b) ∉ T := fun h => hnot (hsub h)
      congr 1
      rw [treeCost, Finset.sum_insert hn, hab0, zero_add, Finset.sum_ite_mem,
        Finset.inter_eq_right.mpr hsub]
  rw [Finset.sum_congr rfl (fun T _ => step1 T)]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [← hμ.2.2.2 e he, Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  split_ifs <;> ring
