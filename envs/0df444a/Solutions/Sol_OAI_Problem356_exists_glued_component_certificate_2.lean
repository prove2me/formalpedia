-- Prove2me | solution 2 for OAI.Problem356.exists_glued_component_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:41:40.606034+00:00
-- url     : https://prove2.me/submissions/2679592e-369d-427c-832b-b5030a2285d6

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/GluedCertificate.lean:L22-L98
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.exists_glued_component_certificate. The node keeps its source
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
import Theorems.Thm_OAI_Problem356_Geometry_finite_disjoint_closedBalls_subset
import Theorems.Thm_OAI_Problem356_exists_uniform_local_potential_bound
import Theorems.Thm_OAI_Problem356_finite_component_certificate

-- ---- from OAI.Analysis.CoulombTransport.ComponentPotential ----
namespace OAI

universe uIndex

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.ComponentPotential

variable {ι : Type uIndex} [Fintype ι]

theorem glue_eq {U : ι → Set E3} {u : ι → E3 → ℝ}
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j))) {i : ι} {x : E3}
    (hx : x ∈ U i) : glue U u x = u i x := by
  classical
  unfold glue
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem hx _
  · intro j _ hji
    apply indicator_of_notMem
    intro hxj
    exact Set.disjoint_left.mp (hdisj hji) hxj hx
  · simp

theorem glue_eq_zero {U : ι → Set E3} {u : ι → E3 → ℝ} {x : E3}
    (hx : x ∉ ⋃ i, U i) : glue U u x = 0 := by
  classical
  unfold glue
  apply Finset.sum_eq_zero
  intro i _
  apply indicator_of_notMem
  intro hxi
  exact hx (mem_iUnion.mpr ⟨i, hxi⟩)

/-- Local continuity is sufficient for global Borel measurability of the extension. -/
theorem measurable_glue {U : ι → Set E3} {u : ι → E3 → ℝ}
    (hU : ∀ i, MeasurableSet (U i)) (hu : ∀ i, ContinuousOn (u i) (U i)) :
    Measurable (glue U u) := by
  classical
  unfold glue
  apply Finset.measurable_sum
  intro i _
  change Measurable ((U i).piecewise (u i) (fun _ => 0))
  exact (hu i).measurable_piecewise continuousOn_const (hU i)

/-- Gluing preserves continuity on the open union of pairwise disjoint components. -/
theorem continuousOn_glue {U : ι → Set E3} {u : ι → E3 → ℝ}
    (hU : ∀ i, IsOpen (U i))
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hu : ∀ i, ContinuousOn (u i) (U i)) :
    ContinuousOn (glue U u) (⋃ i, U i) := by
  apply ContinuousOn.iUnion_of_isOpen _ hU
  intro i
  apply (hu i).congr
  intro x hx
  exact glue_eq hdisj hx

/-- A common absolute bound passes to the glued potential, globally if it is nonnegative. -/
theorem abs_glue_le {U : ι → Set E3} {u : ι → E3 → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hu : ∀ i, ∀ x ∈ U i, |u i x| ≤ M) (x : E3) :
    |glue U u x| ≤ M := by
  by_cases hx : x ∈ ⋃ i, U i
  · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    rw [glue_eq hdisj hxi]
    exact hu i x hxi
  · rw [glue_eq_zero hx, abs_zero]
    exact hM

end Problem356.ComponentPotential

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.GluedCertificate ----
namespace OAI

universe uIndex

noncomputable section
open Set Filter Metric
open scoped ENNReal BigOperators

namespace Problem356

/-- Local good-type certificates and strict bad-center gaps produce an actual
bounded, measurable supporting potential on disjoint small component balls,
with the precise union of the prescribed contact sets. -/
theorem exists_glued_component_certificate {ι : Type uIndex} [Fintype ι]
    (p : ι → E3) (hp : Function.Injective p)
    (V : ι → Set E3) (hV : ∀ i, IsOpen (V i)) (hpV : ∀ i, p i ∈ V i)
    (v : ι → E3 → ℝ) (hv : ∀ i, ContinuousOn (v i) (V i))
    (Good : (ι × (ι × ι)) → Prop)
    (Contact : (ι × (ι × ι)) → Triple → Prop)
    (hgood : ∀ a, Good a → ∀ᶠ t in nhds (p a.1, (p a.2.1, p a.2.2)),
      ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) =
        coulombCost t ↔ Contact a t))
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
        (ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) ↔
          componentContact U Good Contact (x, (y, z)))) := by
  classical
  have hvAt : ∀ i, ContinuousAt (v i) (p i) :=
    fun i => (hv i).continuousAt ((hV i).mem_nhds (hpV i))
  obtain ⟨rC, hrC, hcert⟩ := finite_component_certificate p v Good Contact hvAt hgood hbad
  obtain ⟨M, hM, rB, hrB, hbound⟩ := exists_uniform_local_potential_bound p v hvAt
  obtain ⟨rV, hrV, hsubV, hdisjV⟩ :=
    Geometry.finite_disjoint_closedBalls_subset p hp V hV hpV
  let r : ℝ := min rC (min rB rV)
  have hr : 0 < r := lt_min hrC (lt_min hrB hrV)
  have hrC' : r ≤ rC := min_le_left _ _
  have hrB' : r ≤ rB := (min_le_right _ _).trans (min_le_left _ _)
  have hrV' : r ≤ rV := (min_le_right _ _).trans (min_le_right _ _)
  let U : ι → Set E3 := fun i => ball (p i) r
  have hUV : ∀ i, U i ⊆ V i := by
    intro i
    exact (ball_subset_closedBall.trans (closedBall_subset_closedBall hrV')).trans (hsubV i)
  have hUdisj : Pairwise (fun i j => Disjoint (U i) (U j)) := by
    intro i j hij
    exact (hdisjV hij).mono
      (ball_subset_closedBall.trans (closedBall_subset_closedBall hrV'))
      (ball_subset_closedBall.trans (closedBall_subset_closedBall hrV'))
  have huCont : ∀ i, ContinuousOn (v i) (U i) := fun i => (hv i).mono (hUV i)
  have hUbound : ∀ i, ∀ x ∈ U i, |v i x| ≤ M := by
    intro i x hx
    exact hbound i x (ball_subset_ball hrB' hx)
  refine ⟨r, M, hr, hM, hUV, hUdisj, ?_, ?_, ?_, ?_⟩
  · exact ComponentPotential.measurable_glue (fun _ => isOpen_ball.measurableSet) huCont
  · exact ComponentPotential.continuousOn_glue (fun _ => isOpen_ball) hUdisj huCont
  · exact ComponentPotential.abs_glue_le hM.le hUdisj hUbound
  · intro x hx y hy z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    obtain ⟨k, hk⟩ := mem_iUnion.mp hz
    have hc := hcert (i, (j, k)) x y z
      (ball_subset_ball hrC' hi) (ball_subset_ball hrC' hj) (ball_subset_ball hrC' hk)
    rw [ComponentPotential.glue_eq hUdisj hi, ComponentPotential.glue_eq hUdisj hj,
      ComponentPotential.glue_eq hUdisj hk]
    refine ⟨hc.1, ?_⟩
    constructor
    · intro heq
      exact ⟨(i, (j, k)), hi, hj, hk, (hc.2.mp heq).1, (hc.2.mp heq).2⟩
    · rintro ⟨a, ha₁, ha₂, ha₃, hgooda, hcontact⟩
      have heq := (hcert a x y z (ball_subset_ball hrC' ha₁)
        (ball_subset_ball hrC' ha₂) (ball_subset_ball hrC' ha₃)).2.mpr ⟨hgooda, hcontact⟩
      have hxv : v a.1 x = v i x := by
        rw [← ComponentPotential.glue_eq (u := v) hUdisj ha₁, ComponentPotential.glue_eq hUdisj hi]
      have hyv : v a.2.1 y = v j y := by
        rw [← ComponentPotential.glue_eq (u := v) hUdisj ha₂, ComponentPotential.glue_eq hUdisj hj]
      have hzv : v a.2.2 z = v k z := by
        rw [← ComponentPotential.glue_eq (u := v) hUdisj ha₃, ComponentPotential.glue_eq hUdisj hk]
      simpa only [hxv, hyv, hzv] using heq

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open Set Filter Metric
open scoped ENNReal BigOperators


theorem solution.{uIndex} : type_of% @_root_.OAI.Problem356.exists_glued_component_certificate.{uIndex} := @_root_.OAI.Problem356.exists_glued_component_certificate.{uIndex}
