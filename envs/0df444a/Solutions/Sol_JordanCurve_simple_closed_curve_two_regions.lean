-- Prove2me | solution 1 for JordanCurve.simple_closed_curve_two_regions
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T00:23:56.685478+00:00
-- url     : https://prove2.me/submissions/1b7fdb53-3359-4051-87f1-a5076b078759
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Connected.LocallyConnected
import Theorems.Thm_JordanCurve_simple_closed_curve_two_components

theorem solution
    (γ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hγ : Continuous γ) (hinj : Function.Injective γ) :
    ∃ inside outside : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen inside ∧ IsOpen outside ∧
      IsConnected inside ∧ IsConnected outside ∧
      Bornology.IsBounded inside ∧ ¬ Bornology.IsBounded outside ∧
      Disjoint inside outside ∧
      inside ∪ outside = (Set.range γ)ᶜ := by
  obtain ⟨a, b, ha, hb, hdisj, hcover, hibounded, hounbounded⟩ :=
    JordanCurve.simple_closed_curve_two_components γ hγ hinj
  have hclosed : IsClosed (Set.range γ) :=
    (isCompact_range hγ).isClosed
  have hopen : IsOpen ((Set.range γ)ᶜ) := hclosed.isOpen_compl
  refine ⟨connectedComponentIn ((Set.range γ)ᶜ) a,
    connectedComponentIn ((Set.range γ)ᶜ) b,
    hopen.connectedComponentIn, hopen.connectedComponentIn,
    isConnected_connectedComponentIn_iff.mpr ha,
    isConnected_connectedComponentIn_iff.mpr hb,
    hibounded, hounbounded, hdisj, hcover⟩
