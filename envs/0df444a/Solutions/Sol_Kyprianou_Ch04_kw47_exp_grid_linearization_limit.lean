-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_exp_grid_linearization_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:17:21.392273+00:00
-- url     : https://prove2.me/submissions/18775fe1-a70b-4d7f-8efc-c94795611561

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_exp_grid_linearization
open Filter Set Topology
set_option autoImplicit false

/-- Continuous exponents of uniformly bounded grid variation admit
first-order linearisation along arbitrary vanishing-mesh grids. -/
theorem solution
    (a b : Real) (g : Real → Real) (hg : ContinuousOn g (Icc a b))
    (u : Nat → Nat → Real) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n → u n (i+1) - u n i ≤ delta n)
    (Z : Nat → Nat → Real) (hZ : ∀ n i, |Z n i| ≤ 1)
    (C : Real) (hC : 0 ≤ C)
    (hVar : ∀ n, (∑ i ∈ Finset.range (N n),
      |g (u n (i+1)) - g (u n i)|) ≤ C) :
    Tendsto (fun n =>
      (∑ i ∈ Finset.range (N n),
        Z n i * (1 - Real.exp (-(g (u n (i+1)) - g (u n i))))) -
      (∑ i ∈ Finset.range (N n),
        Z n i * (g (u n (i+1)) - g (u n i))))
      atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  let eta := min (1:Real) (eps/(C+1))
  have hCp : 0 < C+1 := by linarith
  have heta : 0 < eta := lt_min zero_lt_one (div_pos heps hCp)
  have heta1 : eta ≤ 1 := min_le_left _ _
  have hetaC : eta * C < eps := by
    have h := (le_div_iff₀ hCp).mp
      (show eta ≤ eps/(C+1) from min_le_right _ _)
    nlinarith
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hg
  obtain ⟨d,hd,hclose⟩ := Metric.uniformContinuousOn_iff.mp huc eta heta
  obtain ⟨k,hk⟩ := Metric.tendsto_atTop.mp hDelta d hd
  refine ⟨k, fun n hn => ?_⟩
  have hMem (i : Nat) (hi : i ≤ N n) : u n i ∈ Icc a b := by
    have hlo := hu n (Nat.zero_le i)
    have hhi := hu n hi
    rw [h0 n] at hlo
    rw [hN n] at hhi
    exact ⟨hlo,hhi⟩
  have hsmall (i : Nat) (hi : i < N n) :
      |g (u n (i+1)) - g (u n i)| ≤ eta := by
    have hmesh := hMesh n i hi
    have hdk := hk n hn
    rw [Real.dist_eq, sub_zero] at hdk
    have hdist : dist (u n (i+1)) (u n i) < d := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hu n (Nat.le_succ i)))]
      exact lt_of_le_of_lt hmesh (lt_of_le_of_lt (le_abs_self _) hdk)
    have h := hclose (u n (i+1)) (hMem (i+1) (Nat.succ_le_of_lt hi))
      (u n i) (hMem i hi.le) hdist
    exact le_of_lt (by simpa only [Real.dist_eq] using h)
  have hErr := Kyprianou.Ch04.kw47_exp_grid_linearization
    (Z n) (fun i => g (u n (i+1))-g (u n i)) (N n) eta C
    heta.le heta1 (hZ n) hsmall (hVar n)
  rw [Real.dist_eq, sub_zero]
  exact hErr.trans_lt hetaC
