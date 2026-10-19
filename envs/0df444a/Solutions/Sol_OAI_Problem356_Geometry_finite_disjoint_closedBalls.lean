-- Prove2me | solution 1 for OAI.Problem356.Geometry.finite_disjoint_closedBalls
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:07:49.581868+00:00
-- url     : https://prove2.me/submissions/712a2250-2fa5-44fb-82b6-32a6f7c9476f

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
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryMap
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalBranchMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothPushforward

open OAI OAI.Problem356
universe uIndex uX
open Filter Metric Set
theorem h41_unif {ι : Type*} [Finite ι] (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ r i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
  · have := Fintype.ofFinite ι
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ r Finset.univ_nonempty
    exact ⟨r i₀, hr i₀, fun i => hi₀ i (Finset.mem_univ i)⟩

theorem h41_disj {ι : Type*} {X : Type*} [Finite ι] [MetricSpace X]
    (a : ι → X) (ha : Function.Injective a) :
    ∃ δ : ℝ, 0 < δ ∧ Pairwise (fun i j =>
      Metric.closedBall (a i) δ ∩ Metric.closedBall (a j) δ = ∅) := by
  obtain ⟨δ, hδ, hle⟩ := h41_unif (ι := {p : ι × ι // p.1 ≠ p.2})
    (fun p => dist (a p.1.1) (a p.1.2) / 3)
    (fun p => by have := dist_pos.mpr (ha.ne p.2); positivity)
  refine ⟨δ, hδ, fun i j hij => ?_⟩
  ext z
  simp only [Set.mem_inter_iff, Metric.mem_closedBall, Set.mem_empty_iff_false, iff_false, not_and]
  intro h1 h2
  have h3 := hle ⟨(i, j), hij⟩
  have h4 := dist_triangle_right (a i) (a j) z
  have h5 := dist_pos.mpr (ha.ne hij)
  simp only at h3
  rw [dist_comm (a i) z, dist_comm (a j) z] at h4
  linarith

theorem solution {ι : Type uIndex} {X : Type uX} [Finite ι] [MetricSpace X]
    (a : ι → X) (ha : Function.Injective a) :
    ∃ δ : ℝ, 0 < δ ∧ Pairwise (fun i j =>
      Disjoint (closedBall (a i) δ) (closedBall (a j) δ)) := by
  obtain ⟨δ, hδ, h⟩ := h41_disj a ha
  exact ⟨δ, hδ, fun i j hij => Set.disjoint_iff_inter_eq_empty.mpr (h hij)⟩

