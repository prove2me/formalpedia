-- Prove2me | solution 1 for Kyprianou.Ch04.bvFiniteSetDominatedSumLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:28:51.673929+00:00
-- url     : https://prove2.me/submissions/b9820fe6-8b09-46e8-9ae9-580cc0206e9c

import Mathlib
open MeasureTheory Filter Set
set_option autoImplicit false

theorem solution
    {I : Type} (G : Finset I → I → ℝ) (g b : I → ℝ)
    (hb : Summable b) (hbn : ∀ i, 0 ≤ b i)
    (hG : ∀ S i, |G S i| ≤ b i)
    (hlim : ∀ i, Tendsto (fun S => G S i) atTop (nhds (g i))) :
    Tendsto (fun S : Finset I => ∑ i ∈ S, G S i) atTop (nhds (∑' i, g i)) := by
  classical
  let F (S : Finset I) (i : I) := if i ∈ S then G S i else 0
  have hF (i : I) : Tendsto (fun S => F S i) atTop (nhds (g i)) := by
    apply (hlim i).congr'
    filter_upwards [eventually_ge_atTop ({i} : Finset I)] with S hS
    have hm : i ∈ S := hS (Finset.mem_singleton_self i)
    simp [F, hm]
  have hB : ∀ᶠ S in (atTop : Filter (Finset I)), ∀ i, ‖F S i‖ ≤ b i :=
    Eventually.of_forall fun S i => by
      by_cases hi : i ∈ S
      · simpa [F, hi, Real.norm_eq_abs] using hG S i
      · simpa [F, hi] using hbn i
  have ht := tendsto_tsum_of_dominated_convergence hb hF hB
  apply ht.congr'
  apply Eventually.of_forall
  intro S
  change (∑' i, F S i) = ∑ i ∈ S, G S i
  rw [tsum_eq_sum (s := S)]
  · apply Finset.sum_congr rfl
    intro i hi
    simp [F, hi]
  · intro i hi
    simp [F, hi]
