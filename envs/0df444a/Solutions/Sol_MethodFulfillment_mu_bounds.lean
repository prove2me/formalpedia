-- Prove2me | solution 1 for MethodFulfillment.mu_bounds
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:23:41.637282+00:00
-- url     : https://prove2.me/submissions/fed5c8bf-4af8-482e-b610-7adb89b81003

import Mathlib
import Definitions.Def_MethodFulfillment_Instance
import Definitions.Def_MethodFulfillment_Valid
import Definitions.Def_MethodFulfillment_LPFeasible
import Definitions.Def_MethodFulfillment_mu

open MethodFulfillment in
theorem solution {I K Q : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    [Fintype Q] [DecidableEq Q] {T : ℕ} (P : Instance I K Q T) (hP : Valid P)
    (y : Q → Finset (I × K) → ℝ) (hy : LPFeasible P y) (i : I) (k : K) :
    (∀ t, 0 ≤ mu P y t i k ∧ mu P y t i k ≤ 1) ∧ ∑ t, mu P y t i k ≤ (P.S i k : ℝ) := by
  obtain ⟨hy0, hysum, hcap⟩ := hy
  have hpa : ∀ q, 0 ≤ pa P q := fun q => Finset.sum_nonneg (fun t _ => hP.prob_nonneg t q)
  have hyf : ∀ q m, m ∈ (P.methods q).filter (fun m => (i, k) ∈ m) → 0 ≤ y q m :=
    fun q m hm => hy0 q m (Finset.mem_filter.mp hm).1
  refine ⟨fun t => ⟨?_, ?_⟩, ?_⟩
  · unfold mu
    exact Finset.sum_nonneg (fun q _ => Finset.sum_nonneg (fun m hm =>
      div_nonneg (mul_nonneg (hyf q m hm) (hP.prob_nonneg t q)) (hpa q)))
  · unfold mu
    refine le_trans (Finset.sum_le_sum (fun q _ => ?_)) (hP.prob_sum_le_one t)
    by_cases hq0 : pa P q = 0
    · simp only [hq0, div_zero, Finset.sum_const_zero]
      exact hP.prob_nonneg t q
    · calc ∑ m ∈ (P.methods q).filter (fun m => (i, k) ∈ m), y q m * P.p t q / pa P q
          ≤ ∑ m ∈ P.methods q, y q m * P.p t q / pa P q :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun m hm _ => div_nonneg (mul_nonneg (hy0 q m hm) (hP.prob_nonneg t q)) (hpa q))
        _ = (∑ m ∈ P.methods q, y q m) * P.p t q / pa P q := by
            rw [Finset.sum_mul, Finset.sum_div]
        _ = P.p t q := by
            rw [hysum q]
            field_simp
  · unfold mu
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun q _ => Finset.sum_comm)]
    refine le_trans (Finset.sum_le_sum (fun q _ => Finset.sum_le_sum (fun m hm => ?_))) (hcap i k)
    rw [← Finset.sum_div, ← Finset.mul_sum]
    show y q m * pa P q / pa P q ≤ y q m
    by_cases hq0 : pa P q = 0
    · rw [hq0, mul_zero, zero_div]
      exact hyf q m hm
    · rw [mul_div_assoc, div_self hq0, mul_one]
