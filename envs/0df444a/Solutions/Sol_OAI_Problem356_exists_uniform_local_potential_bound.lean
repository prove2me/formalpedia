-- Prove2me | solution 1 for OAI.Problem356.exists_uniform_local_potential_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:15:00.973548+00:00
-- url     : https://prove2.me/submissions/ee628914-2d18-492a-bf60-c0e91aec96fc

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
open Set Filter Metric
open scoped BigOperators


theorem solution {ι : Type uIndex} {X : Type uX} [Fintype ι]
    [PseudoMetricSpace X] (p : ι → X) (v : ι → X → ℝ)
    (hv : ∀ i, ContinuousAt (v i) (p i)) :
    ∃ M : ℝ, 0 < M ∧ ∃ r : ℝ, 0 < r ∧
      ∀ i x, x ∈ ball (p i) r → |v i x| ≤ M := by
  have hr : ∀ i, ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ ball (p i) ε, |v i x| ≤ |v i (p i)| + 1 := by
    intro i
    obtain ⟨ε, hε, h⟩ := Metric.continuousAt_iff.mp (hv i) 1 one_pos
    refine ⟨ε, hε, fun x hx => ?_⟩
    have := h (Metric.mem_ball.mp hx)
    rw [Real.dist_eq] at this
    have h2 := abs_sub_abs_le_abs_sub (v i x) (v i (p i))
    linarith
  choose ε hε hb using hr
  obtain ⟨δ, hδ, hle⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ ε i := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
    · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ ε Finset.univ_nonempty
      exact ⟨ε i₀, hε i₀, fun i => hi₀ i (Finset.mem_univ i)⟩
  refine ⟨1 + ∑ i, |v i (p i)|, by positivity, δ, hδ, fun i x hx => ?_⟩
  have h1 := hb i x (Metric.ball_subset_ball (hle i) hx)
  have h2 : |v i (p i)| ≤ ∑ j, |v j (p j)| :=
    Finset.single_le_sum (f := fun j => |v j (p j)|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  linarith

