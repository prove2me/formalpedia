-- Prove2me | solution 2 for OAI.Problem356.Geometry.exists_uniform_positive_radius
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:34:30.165277+00:00
-- url     : https://prove2.me/submissions/03ece545-b1c7-460d-b503-c527a844261b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/NeighborhoodCertificate.lean:L13-L31
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.Geometry.exists_uniform_positive_radius. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.Analysis.CoulombTransport.NeighborhoodCertificate ----
namespace OAI

universe uIndex uX

noncomputable section

open Filter Metric Set

namespace Problem356.Geometry

/-- A finite family of positive radii admits a common positive lower bound,
including when the indexing type is empty. -/
theorem exists_uniform_positive_radius {ι : Type uIndex} [Finite ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ r i := by
  classical
  let := Fintype.ofFinite ι
  let s : Finset ℝ := insert 1 (Finset.univ.image r)
  have hs : s.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨s.min' hs, ?_, ?_⟩
  · apply (Finset.lt_min'_iff s hs).2
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · norm_num
    · rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
      exact hr i
  · intro i
    exact Finset.min'_le s (r i) (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))

end Problem356.Geometry

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.Geometry
open Filter Metric Set


theorem solution.{uIndex} : type_of% @_root_.OAI.Problem356.Geometry.exists_uniform_positive_radius.{uIndex} := @_root_.OAI.Problem356.Geometry.exists_uniform_positive_radius.{uIndex}
