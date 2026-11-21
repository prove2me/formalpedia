-- Prove2me | solution 1 for MasulloRH.single_prime_height_test_without_log_loss
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T04:54:45.824077+00:00
-- url     : https://prove2.me/submissions/5fc657ca-e77c-4d1c-af62-340c7ba315f5

import Theorems.Thm_MasulloRH_finite_prime_tail_le_seven_over_three_halves_power
import Theorems.Thm_MasulloRH_cofinal_prime_slack_verifies_height_via_quartets
import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
open MasulloRH ArithmeticFunction
open Set Filter Topology MeasureTheory

theorem solution (N : ℕ) (hN : 196 ≤ N) (ε : ℝ) :
    let f := fun j : ℕ => vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ)
    let C := Real.log 2/2 + Real.pi/4 - 37/30
    let Z := {z : ZetaZerosInTraceStrip (1/2) // z.val.re = 1/2}
    let M := fun F : Finset Z => ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val.val:ℝ) *
      ((z.val.val.im^2-5)/(2*(z.val.val.im^2+25/4)*(z.val.val.im^2+4)))
    ∀ F : Finset Z, C+(∑ j ∈ Finset.range (N+1), f j) ≤ M F + ε →
      ∀ H : ℝ, (200000001/100000000 : ℝ)*(ε+7/(N:ℝ)^(3/2:ℝ))*(1+H^2) < 4 →
        ∀ z : ZetaZerosInTraceStrip (1/2), |z.val.im| ≤ H → z.val.re = 1/2 := by
  classical
  dsimp only
  intro F hc
  let τ := ε+7/(N:ℝ)^(3/2:ℝ)
  apply cofinal_prime_slack_verifies_height_via_quartets τ
  intro k
  let K := k+N+1
  refine ⟨K+1,by dsimp [K]; omega,F,?_⟩
  let f (j : ℕ) := vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ)
  have he : Finset.range (K+1) = Finset.range (N+1) ∪ Finset.Ioc N K := by
    ext i; simp only [Finset.mem_range,Finset.mem_union,Finset.mem_Ioc]; dsimp [K]; omega
  have hd : Disjoint (Finset.range (N+1)) (Finset.Ioc N K) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have := Finset.mem_range.mp hi
    have := (Finset.mem_Ioc.mp hj).1
    omega
  have ht := finite_prime_tail_le_seven_over_three_halves_power N K hN
  change (∑ j ∈ Finset.Ioc N K, f j) ≤ _ at ht
  change _ + (∑ j ∈ Finset.range (N+1),f j) ≤ _ at hc
  change _ + (∑ j ∈ Finset.range (K+1),f j) ≤ _ + τ + 1/((k:ℝ)+1)
  rw [he,Finset.sum_union hd]
  dsimp [τ]
  linarith only [hc,ht,show 0 ≤ 1/((k:ℝ)+1) by positivity]
