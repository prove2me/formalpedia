-- Prove2me | solution 2 for OAI.Problem356.exists_glued_component_certificate_forward
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:05:52.632958+00:00
-- url     : https://prove2.me/submissions/3f647ee3-194f-4a03-a779-7aa620ef159b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/GluedCertificateForward.lean:L13-L56
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.exists_glued_component_certificate_forward. The node keeps its source
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
import Definitions.Def_OAI_Analysis_CoulombTransport_GluedCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_GoodTypePermutation
import Definitions.Def_OAI_Analysis_CoulombTransport_IsometryTransport
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothBranchMarginal
import Definitions.Def_OAI_Analysis_CoulombTransport_StateDual
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombSupportExistence
import Definitions.Def_OAI_Analysis_CoulombTransport_FiveComponentGeometry
import Theorems.Thm_OAI_Problem356_exists_glued_component_certificate

-- ---- from OAI.Analysis.CoulombTransport.GluedCertificateForward ----
namespace OAI

universe uIndex

noncomputable section
open Set Filter Metric
open scoped ENNReal BigOperators

namespace Problem356

/-- The finite gluing construction only needs forward contact localization.
The explicit contact candidates may be shown saturated separately, so no
converse from the chosen global contact predicate is required here. -/
theorem exists_glued_component_certificate_forward {ι : Type uIndex} [Fintype ι]
    (p : ι → E3) (hp : Function.Injective p)
    (V : ι → Set E3) (hV : ∀ i, IsOpen (V i)) (hpV : ∀ i, p i ∈ V i)
    (v : ι → E3 → ℝ) (hv : ∀ i, ContinuousOn (v i) (V i))
    (Good : (ι × (ι × ι)) → Prop) (Contact : Triple → Prop)
    (hgood : ∀ a, Good a → ∀ᶠ t in nhds (p a.1, (p a.2.1, p a.2.2)),
      ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) =
        coulombCost t → Contact t))
    (hbad : ∀ a, ¬ Good a →
      ENNReal.ofReal (v a.1 (p a.1) + v a.2.1 (p a.2.1) + v a.2.2 (p a.2.2)) <
        coulombCost (p a.1, (p a.2.1, p a.2.2))) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧
      let U := fun i => ball (p i) r
      let u := ComponentPotential.glue U v
      (∀ i, U i ⊆ V i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      Measurable u ∧ ContinuousOn u (⋃ i, U i) ∧ (∀ x, |u x| ≤ M) ∧
      (∀ x ∈ ⋃ i, U i, ∀ y ∈ ⋃ i, U i, ∀ z ∈ ⋃ i, U i,
        ENNReal.ofReal (u x + u y + u z) ≤ coulombCost (x, (y, z)) ∧
        (ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) →
          Contact (x, (y, z)))) := by
  let C : (ι × (ι × ι)) → Triple → Prop := fun a t =>
    ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) = coulombCost t ∧
      Contact t
  have hgood' : ∀ a, Good a → ∀ᶠ t in nhds (p a.1, (p a.2.1, p a.2.2)),
      ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) =
        coulombCost t ↔ C a t) := by
    intro a ha
    filter_upwards [hgood a ha] with t ht
    exact ⟨ht.1, ⟨fun heq => ⟨heq, ht.2 heq⟩, fun hc => hc.1⟩⟩
  obtain ⟨r, M, hr, hM, hUV, hdisj, hmeas, hcont, hbound, hcert⟩ :=
    exists_glued_component_certificate p hp V hV hpV v hv Good C hgood' hbad
  refine ⟨r, M, hr, hM, hUV, hdisj, hmeas, hcont, hbound, ?_⟩
  intro x hx y hy z hz
  have hc := hcert x hx y hy z hz
  refine ⟨hc.1, ?_⟩
  intro heq
  obtain ⟨a, _, _, _, _, hcontact⟩ := hc.2.mp heq
  exact hcontact.2

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open Set Filter Metric
open scoped ENNReal BigOperators


theorem solution.{uIndex} : type_of% @_root_.OAI.Problem356.exists_glued_component_certificate_forward.{uIndex} := @_root_.OAI.Problem356.exists_glued_component_certificate_forward.{uIndex}
