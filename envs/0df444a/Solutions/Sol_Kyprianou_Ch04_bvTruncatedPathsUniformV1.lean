-- Prove2me | solution 1 for Kyprianou.Ch04.bvTruncatedPathsUniformV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:35:59.7358+00:00
-- url     : https://prove2.me/submissions/4fb827ad-91c5-4ead-a5c1-a01ce6239d0e

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvRightTruncationTailBoundV1
import Theorems.Thm_Kyprianou_Ch04_bvLeftTruncationTailBoundV1
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Filter
set_option autoImplicit false
open Kyprianou.Ch04

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → Real) (omega : Omega) (c : Real)
    (hRep : forall t : NNReal,
      Summable (fun s : Set.Ioc (0 : NNReal) t => |X s omega - Xleft s omega|) ∧
      X t omega = X 0 omega + c * (t : Real) +
        ∑' s : Set.Ioc (0 : NNReal) t, (X s omega - Xleft s omega))
    (hLeft : ∀ u : NNReal, 0 < u →
      Tendsto (fun v : NNReal => X v omega) (nhdsWithin u (Set.Iio u))
        (nhds (Xleft u omega)))
    (t : NNReal) :
    let j : Set.Ioc (0 : NNReal) t → ℝ := fun s => X s omega - Xleft s omega
    let P : Finset (Set.Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) + ∑ s ∈ S, if (s : NNReal) ≤ u then j s else 0
    let Q : Finset (Set.Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) + ∑ s ∈ S, if (s : NNReal) < u then j s else 0
    TendstoUniformlyOn P (fun u => X u omega) atTop (Set.Icc 0 t) ∧
      TendstoUniformlyOn Q (fun u => Xleft u omega) atTop (Set.Ioc 0 t) := by
  classical
  intro j P Q
  have hsum : Tendsto (fun S : Finset (Set.Ioc (0 : NNReal) t) =>
      (∑' s, |j s|) - ∑ s ∈ S, |j s|) atTop (nhds 0) := by
    have h := (hRep t).1.hasSum
    change Tendsto (fun S : Finset (Set.Ioc (0 : NNReal) t) =>
      ∑ s ∈ S, |j s|) atTop (nhds (∑' s, |j s|)) at h
    have hc : Tendsto (fun _ : Finset (Set.Ioc (0 : NNReal) t) => (∑' s, |j s|)) atTop (nhds (∑' s, |j s|)) := tendsto_const_nhds
    simpa only [sub_self] using hc.sub h
  constructor
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hsum.eventually (gt_mem_nhds hε)] with S hS u hu
    rw [Real.dist_eq]
    exact (Kyprianou.Ch04.bvRightTruncationTailBoundV1
      X Xleft omega c hRep t S u hu.2).trans_lt hS
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hsum.eventually (gt_mem_nhds hε)] with S hS u hu
    rw [Real.dist_eq]
    exact (Kyprianou.Ch04.bvLeftTruncationTailBoundV1
      X Xleft omega c hRep hLeft t S u hu.1 hu.2).trans_lt hS
