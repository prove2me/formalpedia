-- Prove2me | solution 1 for OAI.Problem356.exists_compact_small_partition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:36:46.813588+00:00
-- url     : https://prove2.me/submissions/fe9d89cd-da66-4ca5-b878-6ce211c47c37

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure

open OAI OAI.Problem356
universe uX uIndex
open Set MeasureTheory Metric


theorem solution {X : Type uX} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {K : Set X} (hK : IsCompact K)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (A : Fin n → Set X),
      (∀ i, MeasurableSet (A i)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      (⋃ i, A i) = K ∧
      (∀ i, A i ⊆ K) ∧
      (∀ i, ∀ x ∈ A i, ∀ y ∈ A i, dist x y < δ) := by
  obtain ⟨t, htK, htf, hcov⟩ := finite_cover_balls_of_compact hK (show 0 < δ / 3 by positivity)
  obtain ⟨n, c, hc⟩ := htf.fin_embedding
  let f : Fin n → Set X := fun i => K ∩ ball (c i) (δ / 3)
  have hfm : ∀ i, MeasurableSet (f i) := fun i => hK.isClosed.measurableSet.inter isOpen_ball.measurableSet
  refine ⟨n, disjointed f, ?_, disjoint_disjointed f, ?_, ?_, ?_⟩
  · intro i
    rw [disjointed_eq_inter_compl]
    exact (hfm i).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hfm j).compl)
  · rw [iUnion_disjointed]
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun i => Set.inter_subset_left
    · intro x hx
      have := hcov hx
      simp only [Set.mem_iUnion] at this
      obtain ⟨y, hy, hxy⟩ := this
      rw [← hc] at hy
      obtain ⟨i, rfl⟩ := hy
      exact Set.mem_iUnion.mpr ⟨i, hx, hxy⟩
  · intro i
    exact (disjointed_subset f i).trans Set.inter_subset_left
  · intro i x hx y hy
    have hx' := ((disjointed_subset f i) hx).2
    have hy' := ((disjointed_subset f i) hy).2
    rw [Metric.mem_ball] at hx' hy'
    have := dist_triangle_right x y (c i)
    linarith

