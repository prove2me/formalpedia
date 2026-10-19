-- Prove2me | solution 1 for OAI.Problem356.CommonBranches.exists_common_central_ball_in_components
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:45:58.33024+00:00
-- url     : https://prove2.me/submissions/f5a27a10-6558-4615-b10a-ff73594d5033

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/CommonBranches.lean:L118-L159
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.CommonBranches.exists_common_central_ball_in_components. The node keeps its source
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

-- ---- from OAI.Analysis.CoulombTransport.CommonBranches ----
namespace OAI

universe uE uM uIndex uF

/-!
# Reparametrizing local branches by their common central component

For local homeomorphisms `X,Z` on the parameter component, the central
parametrizations are `X.symm` and `X.symm.trans Z`. Their common source is
open, contains the central base point, and inherits both smooth inverses.
-/

noncomputable section
open Set Metric

namespace Problem356.CommonBranches

variable {E : Type uE} [TopologicalSpace E]

/-- Both local maps being defined at the parameter base point puts the
central image in the source of the reparametrized outer branch. -/
theorem image_mem_outer_source (X Z : OpenPartialHomeomorph E E) {a : E}
    (haX : a ∈ X.source) (haZ : a ∈ Z.source) :
    X a ∈ (outer X Z).source := by
  change X a ∈ X.symm.source ∩ X.symm ⁻¹' Z.source
  refine ⟨X.map_source haX, ?_⟩
  change X.symm (X a) ∈ Z.source
  rw [X.left_inv haX]
  exact haZ

/-- The common source permits both the inverse branch and the second outer
branch, with their expected component containment and inverse identity. -/
theorem outer_source_properties (X Z : OpenPartialHomeomorph E E) {x : E}
    (hx : x ∈ (outer X Z).source) :
    x ∈ X.target ∧ X.symm x ∈ X.source ∧ X.symm x ∈ Z.source ∧
      outer X Z x ∈ Z.target ∧ X (X.symm x) = x := by
  change x ∈ X.symm.source ∩ X.symm ⁻¹' Z.source at hx
  exact ⟨hx.1, X.symm.map_source hx.1, hx.2, Z.map_source hx.2,
    X.right_inv hx.1⟩

section Metric

variable {M : Type uM} [PseudoMetricSpace M]

/-- The central ball can simultaneously keep the inverse and composed
branches inside arbitrary prescribed outer neighborhoods. Thus shrinking the
global certificate components does not require changing either local chart. -/
theorem exists_common_central_ball_in_components {ι : Type uIndex} [Finite ι]
    (X Z : ι → OpenPartialHomeomorph M M) (a : ι → M) (x : M)
    (haX : ∀ i, a i ∈ (X i).source) (haZ : ∀ i, a i ∈ (Z i).source)
    (hcenter : ∀ i, X i (a i) = x)
    (P Q : ι → Set M) (hP : ∀ i, IsOpen (P i)) (hQ : ∀ i, IsOpen (Q i))
    (haP : ∀ i, a i ∈ P i) (haQ : ∀ i, Z i (a i) ∈ Q i)
    {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ U ∧
      ∀ i, ∀ y ∈ ball x r,
        y ∈ (outer (X i) (Z i)).source ∧
        (X i).symm y ∈ P i ∧ outer (X i) (Z i) y ∈ Q i := by
  have hbase : ∀ i, x ∈ (outer (X i) (Z i)).source := by
    intro i
    rw [← hcenter i]
    exact image_mem_outer_source (X i) (Z i) (haX i) (haZ i)
  have hinv : ∀ i, (X i).symm x = a i := by
    intro i
    rw [← hcenter i, (X i).left_inv (haX i)]
  have houter : ∀ i, outer (X i) (Z i) x = Z i (a i) := by
    intro i
    rw [outer_apply, hinv i]
  have hnear : ∀ i, ∀ᶠ y in nhds x,
      y ∈ (outer (X i) (Z i)).source ∧
      (X i).symm y ∈ P i ∧ outer (X i) (Z i) y ∈ Q i := by
    intro i
    have hys : x ∈ (X i).symm.source :=
      (outer_source_properties (X i) (Z i) (hbase i)).1
    have hyP := ((X i).symm.continuousAt hys).eventually
      ((hP i).mem_nhds (by rw [hinv i]; exact haP i))
    have hwQ := ((outer (X i) (Z i)).continuousAt (hbase i)).eventually
      ((hQ i).mem_nhds (by rw [houter i]; exact haQ i))
    have hs : ∀ᶠ y in nhds x, y ∈ (outer (X i) (Z i)).source :=
      (outer (X i) (Z i)).open_source.mem_nhds (hbase i)
    exact hs.and (hyP.and hwQ)
  have hu : ∀ᶠ y in nhds x, y ∈ U := hU.mem_nhds hxU
  have hall := hu.and (Filter.eventually_all.mpr hnear)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hall
  exact ⟨r, hr, fun y hy => (hball y hy).1,
    fun i y hy => (hball y hy).2 i⟩

end Metric

section Smooth

variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]

end Smooth
end Problem356.CommonBranches

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.CommonBranches
open Set Metric


theorem solution.{uM,uIndex} : type_of% @_root_.OAI.Problem356.CommonBranches.exists_common_central_ball_in_components.{uM,uIndex} := @_root_.OAI.Problem356.CommonBranches.exists_common_central_ball_in_components.{uM,uIndex}
