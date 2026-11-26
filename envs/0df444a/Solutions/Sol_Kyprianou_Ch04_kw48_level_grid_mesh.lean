-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_level_grid_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:38:39.412128+00:00
-- url     : https://prove2.me/submissions/9d9299f9-f243-4472-9206-f979678e77de

import Mathlib
open Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- A continuous nondecreasing change of coordinates sends a
vanishing-mesh monotone grid to another vanishing-mesh grid. -/
theorem solution (a b : Real) (g : Real → Real)
    (hg : ContinuousOn g (Icc a b)) (hgm : Monotone g)
    (u : Nat → Nat → Real) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n → u n (i+1)-u n i ≤ delta n) :
    ∃ d : Nat → Real, Tendsto d atTop (nhds 0) ∧
      ∀ n i, i < N n → g (u n (i+1))-g (u n i) ≤ d n := by
  let D : Nat → NNReal := fun n => (Finset.range (N n)).sup
    (fun i => (g (u n (i+1))-g (u n i)).toNNReal)
  refine ⟨fun n => (D n:Real),?_,?_⟩
  · apply Metric.tendsto_atTop.mpr
    intro eps heps
    have hhalf : 0 < eps/2 := by linarith
    obtain ⟨r,hr,hclose⟩ := Metric.uniformContinuousOn_iff.mp
      (isCompact_Icc.uniformContinuousOn_of_continuous hg) (eps/2) hhalf
    obtain ⟨k,hk⟩ := Metric.tendsto_atTop.mp hDelta r hr
    refine ⟨k, fun n hn => ?_⟩
    have hMem (i : Nat) (hi : i ≤ N n) : u n i ∈ Icc a b := by
      have hlo := hu n (Nat.zero_le i)
      have hhi := hu n hi
      rw [h0 n] at hlo
      rw [hN n] at hhi
      exact ⟨hlo,hhi⟩
    have hD : D n ≤ (eps/2).toNNReal := by
      apply Finset.sup_le
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hm := hMesh n i hi'
      have hdk := hk n hn
      rw [Real.dist_eq, sub_zero] at hdk
      have hd : dist (u n (i+1)) (u n i) < r := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hu n (Nat.le_succ i)))]
        exact hm.trans_lt ((le_abs_self _).trans_lt hdk)
      have hc := hclose (u n (i+1)) (hMem (i+1) (Nat.succ_le_of_lt hi'))
        (u n i) (hMem i hi'.le) hd
      rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (hgm (hu n (Nat.le_succ i))))] at hc
      exact Real.toNNReal_le_toNNReal hc.le
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (NNReal.coe_nonneg _)]
    have hh := NNReal.coe_le_coe.mpr hD
    rw [Real.coe_toNNReal _ hhalf.le] at hh
    linarith
  · intro n i hi
    have h := Finset.le_sup (f := fun j =>
      (g (u n (j+1))-g (u n j)).toNNReal) (Finset.mem_range.mpr hi)
    have hc := NNReal.coe_le_coe.mpr h
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr (hgm (hu n (Nat.le_succ i))))] at hc
    exact hc
