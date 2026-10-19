-- Prove2me | solution 2 for OAI.Problem356.finite_eventual_neighborhoods
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:43:29.202394+00:00
-- url     : https://prove2.me/submissions/bddbbb4e-8c30-4ea3-aa6b-20fc9f65b149

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/CertificateNeighborhoods.lean:L14-L36
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.finite_eventual_neighborhoods. The node keeps its source
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

-- ---- from OAI.Analysis.CoulombTransport.CertificateNeighborhoods ----
namespace OAI

universe uIndex uX uY

noncomputable section

open Set Filter Metric
open scoped ENNReal

namespace Problem356

/-- Finitely many eventual properties hold simultaneously on balls with one
common positive radius around their respective centers. -/
theorem finite_eventual_neighborhoods {ι : Type uIndex} {X : Type uX} [PseudoMetricSpace X]
    (s : Finset ι) (p : ι → X) (P : ι → X → Prop)
    (hP : ∀ i ∈ s, ∀ᶠ x in nhds (p i), P i x) :
    ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, ∀ x, dist x (p i) < r → P i x := by
  classical
  have hone : ∀ i ∈ s, ∃ r : ℝ, 0 < r ∧
      ∀ x, dist x (p i) < r → P i x := by
    intro i hi
    obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.mp (hP i hi)
    exact ⟨r, hr, fun x hx => h hx⟩
  clear hP
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s his ih =>
      obtain ⟨r, hr, hri⟩ := hone i (Finset.mem_insert_self i s)
      obtain ⟨q, hq, hqs⟩ := ih (fun j hj => hone j (Finset.mem_insert_of_mem hj))
      refine ⟨min r q, lt_min hr hq, ?_⟩
      intro j hj x hx
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hri x (lt_of_lt_of_le hx (min_le_left _ _))
      · exact hqs j hj x (lt_of_lt_of_le hx (min_le_right _ _))

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open Set Filter Metric
open scoped ENNReal


theorem solution.{uIndex,uX} : type_of% @_root_.OAI.Problem356.finite_eventual_neighborhoods.{uIndex,uX} := @_root_.OAI.Problem356.finite_eventual_neighborhoods.{uIndex,uX}
