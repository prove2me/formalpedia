-- Prove2me | solution 1 for OAI.ThreeManifold.ReturningPassage.truncated_return_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:57:50.705484+00:00
-- url     : https://prove2.me/submissions/e7c98925-028a-4738-9e59-a5c5a0a4be4b

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/NoConjugatePoints.lean:L24-L109
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.ReturningPassage.truncated_return_nonnegative. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning
import Definitions.Def_OAI_Geometry_ConjugatePoints_Index
import Definitions.Def_OAI_Geometry_ConjugatePoints_CompactMetric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Curvature
import Definitions.Def_OAI_Geometry_ConjugatePoints_Geodesics
import Definitions.Def_OAI_Geometry_ConjugatePoints_Continuation
import Definitions.Def_OAI_Geometry_ConjugatePoints_Distance
import Definitions.Def_OAI_Geometry_ConjugatePoints_Convexity
import Definitions.Def_OAI_Geometry_ConjugatePoints_FundamentalGroup
import Definitions.Def_OAI_Geometry_ConjugatePoints_Passages
import Definitions.Def_OAI_Geometry_ConjugatePoints_NoConjugatePoints
import Theorems.Thm_OAI_ThreeManifold_PassageDynamics_finite_turn_completion
import Theorems.Thm_OAI_ThreeManifold_PassageDynamics_reflected_closed_equations
import Theorems.Thm_OAI_ThreeManifold_PassageDynamics_reflected_closed_smooth
import Theorems.Thm_OAI_ThreeManifold_ReturningPassage_returning_arbitrary_field_nonnegative

-- ---- from OAI.Geometry.ConjugatePoints.Neck ----
namespace OAI

noncomputable section

/-!
# Tensor identities and the local and torus neck metrics.
-/

open Set Manifold Bundle Filter Topology
open scoped ContDiff

namespace ThreeManifold.Tensor
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

end ThreeManifold.Tensor

namespace ThreeManifold.Neck
open Matrix
open scoped Matrix Matrix.Norms.Elementwise

end ThreeManifold.Neck

open Set Filter
open scoped Topology ContDiff

namespace ThreeManifold.Cometric
open Matrix
open scoped Matrix.Norms.Elementwise

lemma P_smooth (δ : ℝ) : ContDiff ℝ ∞ (P δ) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> dsimp [P] <;> fun_prop

attribute [fun_prop] χ_deriv_smooth χ_deriv2_smooth

end ThreeManifold.Cometric

namespace ThreeManifold.LocalNeck

section
open Manifold Bundle Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

open Cometric Neck

end

open Manifold Bundle Set Filter Cometric Neck Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

end ThreeManifold.LocalNeck

namespace ThreeManifold.TorusNeck

section
open Set Filter Topology Manifold Bundle
open scoped ContDiff Matrix.Norms.Elementwise
open LocalNeck QuotientConstruction

open Cometric Neck
end

open Set Filter Manifold Bundle Neck Cometric LocalNeck Matrix
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.TorusNeck

end

end OAI

-- ---- from OAI.Geometry.ConjugatePoints.Returning ----
namespace OAI

noncomputable section

/-!
# Returning neck geodesics, passage dynamics, and index bounds.
-/

open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
namespace ThreeManifold.Neck
open Matrix
open scoped Matrix.Norms.Elementwise

end ThreeManifold.Neck

namespace ThreeManifold.Turning

end ThreeManifold.Turning

namespace ThreeManifold.DirectTurning

section
open Set MeasureTheory Neck Matrix
open scoped Interval Topology

end

open Neck Matrix Set MeasureTheory Turning
open scoped Interval Topology Matrix.Norms.Elementwise

end ThreeManifold.DirectTurning

open Set MeasureTheory
open scoped Interval
namespace ThreeManifold.ReturningTime

end ThreeManifold.ReturningTime

open Set MeasureTheory
open scoped Interval
namespace ThreeManifold.ReturningCoefficients
open Neck Matrix

end ThreeManifold.ReturningCoefficients

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.Cometric
open Neck Matrix

lemma coordinateCometric_smooth (right : Bool) (δ : ℝ) :
    ContDiff ℝ ∞ (coordinateCometric right δ) := by
  cases right
  · exact P_smooth δ
  · exact (congruenceCLM (C₂ δ)).contDiff.comp
      ((P_smooth δ).comp (contDiff_const.sub contDiff_id))

end ThreeManifold.Cometric

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningCoefficients
open Neck Cometric Matrix

end ThreeManifold.ReturningCoefficients

open Set Filter
open scoped Topology ContDiff
namespace ThreeManifold.PassageDynamics

end ThreeManifold.PassageDynamics

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningPassage

section
-- [generator] trimmed: open Neck Cometric ReturningCoefficients ReturningTime PassageDynamics Matrix
open Neck Cometric ReturningCoefficients PassageDynamics Matrix

lemma contDiff_pairing_const {R : ℝ → TMat} {n : WithTop ℕ∞}
    (hR : ContDiff ℝ n R) (p q : TVec) : ContDiff ℝ n (fun u => pairing (R u) p q) := by
  simp only [pairing, Matrix.mulVec, dotProduct]
  fun_prop

lemma force_smooth (right : Bool) (δ : ℝ) (p : TVec) :
    ContDiff ℝ ∞ (force right δ p) :=
  contDiff_pairing_const (contDiff_infty_iff_deriv.mp (coordinateCometric_smooth right δ)).2 p p

end

-- [generator] trimmed: open Neck Cometric ReturningCoefficients ReturningTime PassageDynamics Matrix DirectTurning Turning
open Neck Cometric ReturningCoefficients PassageDynamics Matrix DirectTurning Turning

end ThreeManifold.ReturningPassage

namespace ThreeManifold.Neck

section
open Set Matrix MeasureTheory
open scoped ContDiff Interval Topology Matrix.Norms.Elementwise

end

section
open Set Matrix Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

end

open Set Matrix Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.Neck

namespace ThreeManifold.ReturningPassage

section
open Neck Cometric Turning Set Matrix Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

end

section
open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning
open scoped ContDiff Topology Matrix.Norms.Elementwise

end

open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning ReturningCoefficients
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.ReturningPassage

namespace ThreeManifold.Neck
open Set Matrix MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.Neck

namespace ThreeManifold.ReturningPassage
open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning ReturningCoefficients
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.ReturningPassage

end

end OAI

-- ---- from OAI.Geometry.ConjugatePoints.Passages ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
namespace OAI

noncomputable section

/-!
# Passage supports, extension, and compact metric estimates.
-/

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.TwoGluing
variable {X Y : Type} [TopologicalSpace X] (O : TopologicalSpace.Opens X) (e : O ≃ₜ O)
end ThreeManifold.TwoGluing
namespace ThreeManifold.CompactMetric

section
open MetricConstruction CylinderConstruction GluedConstruction
end

section
open MetricConstruction CylinderConstruction GluedConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Cylinder_2
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopCylinder_2
end

open MetricConstruction CylinderConstruction GluedConstruction
end ThreeManifold.CompactMetric

namespace ThreeManifold.CylinderConstruction

section
open QuotientConstruction

end

attribute [local instance] OAI.ThreeManifold.CylinderConstruction.instChartedSpaceE3Cylinder_1
attribute [local instance] OAI.ThreeManifold.CylinderConstruction.instIsManifoldRealE3I3SomeENatTopCylinder_1
end ThreeManifold.CylinderConstruction
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates Cometric Neck

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates.LocalMetricIsometry
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)
end ThreeManifold.RiemannianCoordinates.LocalMetricIsometry

namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction GluedConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Cylinder_3
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopCylinder_3
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
namespace ThreeManifold.FinitePassage

end ThreeManifold.FinitePassage
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction GluedConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Cylinder_4
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopCylinder_4
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
open scoped ContDiff
namespace ThreeManifold.PassageDynamics

end ThreeManifold.PassageDynamics

namespace ThreeManifold.SupportExtension
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [NormedSpace ℝ E] in
lemma cut_germ_left {b s : ℝ} {V : ℝ → E} (hs : s < b) : cut b V =ᶠ[𝓝 s] V := by
  filter_upwards [Iio_mem_nhds hs] with r hr
  exact ite_eq_left hr.le
omit [NormedSpace ℝ E] in
lemma cut_germ_right {b s : ℝ} {V : ℝ → E} (hs : b < s) : cut b V =ᶠ[𝓝 s] 0 := by
  filter_upwards [Ioi_mem_nhds hs] with r hr
  exact ite_eq_right (not_le.mpr hr)
omit [NormedSpace ℝ E] in
lemma cut_germ_center {b : ℝ} {V : ℝ → E} (hz : V =ᶠ[𝓝 b] 0) : cut b V =ᶠ[𝓝 b] 0 := by
  filter_upwards [hz] with r hr
  simp only [cut]
  split_ifs
  · exact hr
  · rfl
lemma cut_smoothAt {b s : ℝ} {V : ℝ → E} (hz : V =ᶠ[𝓝 b] 0)
    (hc : s ≤ b → ContDiffAt ℝ ∞ V s) : ContDiffAt ℝ ∞ (cut b V) s := by
  rcases lt_trichotomy s b with h | rfl | h
  · exact (hc h.le).congr_of_eventuallyEq (cut_germ_left h)
  · exact contDiffAt_const.congr_of_eventuallyEq (cut_germ_center hz)
  · exact contDiffAt_const.congr_of_eventuallyEq (cut_germ_right h)
omit [NormedSpace ℝ E] in
lemma cut_eq {b s : ℝ} {V : ℝ → E} (hs : s ≤ b) : cut b V s = V s := ite_eq_left hs
lemma cut_deriv {b s : ℝ} {V : ℝ → E} (hz : V =ᶠ[𝓝 b] 0) (hs : s ≤ b) :
    deriv (cut b V) s = deriv V s := by
  rcases hs.eq_or_lt with rfl | h
  · exact Filter.EventuallyEq.deriv_eq ((cut_germ_center hz).trans hz.symm)
  · exact Filter.EventuallyEq.deriv_eq (cut_germ_left h)
omit [NormedSpace ℝ E] in
lemma cut_zero {b s : ℝ} {V : ℝ → E} (hs : b < s) : cut b V s = 0 := ite_eq_right (not_le.mpr hs)
lemma cut_deriv_zero {b s : ℝ} {V : ℝ → E} (hs : b < s) : deriv (cut b V) s = 0 := by
  rw [Filter.EventuallyEq.deriv_eq (cut_germ_right hs)]
  exact deriv_const s (0:E)
end ThreeManifold.SupportExtension
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric

section
open RiemannianCoordinates Cometric Neck LocalNeck
end

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage
end

section
open RiemannianCoordinates MetricConstruction Cometric Neck LocalNeck ReturningPassage

end

open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric
end

open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients
end ThreeManifold.CompactMetric

end

end OAI

-- ---- from OAI.Geometry.ConjugatePoints.NoConjugatePoints ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

/-!
# Countable passage assembly and the uniform no-conjugate-points theorem.
-/

section
open Set Filter Topology MeasureTheory Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningPassage
open Neck Cometric Turning ReturningCoefficients PassageDynamics SupportExtension

lemma normalDensity_zero (P Q A B : TMat) (T : Vec) : normalDensity P Q A B T 0 0 = 0 := by
  simp [normalDensity, gamma, curvatureJet, gammaPrime, metric, pairing]

theorem truncated_return_nonnegative {right : Bool} {δ C b c : ℝ} {p : TVec}
    {t v : ℝ → ℝ} {V : ℝ → Vec} (hC : 18 ≤ C)
    (hδ : SmallParameter (3*C) (sourceMixed C) δ)
    (hbound : ∀ u ∈ Icc 0 1, ∀ q, sqnorm q/9 ≤ qform (coordinateCometric right δ u) q ∧
      qform (coordinateCometric right δ u) q ≤ 18*sqnorm q)
    (hder : ∀ u ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) u *ᵥ e) ≤ C^2*δ^2)
    (hconc : ∀ u ∈ Icc 0 1, ∀ q, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q)
    (hdom : ∀ u ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) u *ᵥ p) ≤
      C*δ*qform (-deriv (deriv (coordinateCometric right δ)) u) p)
    (hc : c ∈ Ioo 0 b) (ht : ∀ s ∈ Icc 0 b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 b, HasDerivAt v (-force right δ p (t s)/2) s)
    (hta : ∀ s ∈ Icc 0 b, ContDiffAt ℝ ∞ t s)
    (hva : ∀ s ∈ Icc 0 b, ContDiffAt ℝ ∞ v s)
    (h0 : t 0 = 0) (hr : ∀ s ∈ Ioo 0 b, t s ∈ Ioo (0:ℝ) 1)
    (hvc : v c = 0) (hstar : 1/4 < t c)
    (henergy : ∀ s ∈ Icc 0 b, potential right δ p (t s) + v s^2 = 1)
    (hV : ∀ s ∈ Icc 0 b, ContDiffAt ℝ ∞ V s)
    (hcut : b < 2*c → V =ᶠ[𝓝 b] 0)
    (hfi : IntervalIntegrable (returnNormalDensity right δ p t v V (deriv V)) volume 0 b) :
    0 ≤ ∫ s in (0:ℝ)..b, returnNormalDensity right δ p t v V (deriv V) s := by
  have hb : 0 < b := hc.1.trans hc.2
  have hL : 0 < 2*c := by linarith [hc.1]
  have hd := reflected_closed_equations (force_smooth right δ p) hc ht hv hvc
  have hsmooth := reflected_closed_smooth (force_smooth right δ p) hc ht hv hvc hta hva
  have hcomplete := finite_turn_completion (force_smooth right δ p) hc ht hv hvc h0 hr
  simp only [sub_zero] at hd hsmooth hcomplete
  rcases hcomplete with ⟨hbL,het,hev,he0,heL,her⟩
  let te := reflectEven c t
  let ve := reflectOdd c v
  let W := if b < 2*c then cut b V else V
  have hWeq (s : ℝ) (hs : s ∈ Icc 0 b) : W s = V s := by
    dsimp only [W]
    split_ifs
    · exact cut_eq hs.2
    · rfl
  have hWdeq (s : ℝ) (hs : s ∈ Icc 0 b) : deriv W s = deriv V s := by
    dsimp only [W]
    split_ifs with hbl
    · exact cut_deriv (hcut hbl) hs.2
    · rfl
  have hWs (s : ℝ) (hs : s ∈ Icc 0 (2*c)) : ContDiffAt ℝ ∞ W s := by
    dsimp only [W]
    split_ifs with hbl
    · exact cut_smoothAt (hcut hbl) (fun hsb => hV s ⟨hs.1,hsb⟩)
    · exact hV s ⟨hs.1,hs.2.trans (le_of_not_gt hbl)⟩
  have hE (s : ℝ) (hs : s ∈ Icc 0 (2*c)) : potential right δ p (te s) + ve s^2 = 1 := by
    by_cases hsc : s ≤ c
    · simpa only [te,ve,reflectEven,reflectOdd,ite_eq_left hsc] using henergy s ⟨hs.1,hsc.trans hc.2.le⟩
    · have hh := henergy (2*c-s) ⟨by linarith [hs.2],by linarith [hc.2,lt_of_not_ge hsc]⟩
      simpa only [te,ve,reflectEven,reflectOdd,ite_eq_right hsc,neg_sq] using hh
  have hB := returning_arbitrary_field_nonnegative (right := right) (p := p) (t := te) (v := ve)
    hC hδ hbound hder hconc hdom hL
    (by simpa [te,reflectEven] using hstar)
    (fun s hs => (hd s hs).1) (fun s hs => (hd s hs).2)
    (fun s hs => (hsmooth s hs).1) (fun s hs => (hsmooth s hs).2)
    he0 heL her hE hWs
  let f := returnNormalDensity right δ p t v V (deriv V)
  let g := returnNormalDensity right δ p te ve W (deriv W)
  have heq : EqOn g f (Icc 0 b) := by
    intro s hs
    dsimp only [g,f,returnNormalDensity,momentumVelocity,te,ve]
    rw [het hs,hev hs,hWeq s hs,hWdeq s hs]
  have hzero : EqOn g 0 (Ioo b (2*c)) := by
    intro s hs
    have hbl : b < 2*c := hs.1.trans hs.2
    have hw : W = cut b V := ite_eq_left hbl
    dsimp only [g,returnNormalDensity]
    rw [hw,cut_zero hs.1,cut_deriv_zero hs.1,normalDensity_zero]
    rfl
  have hgi : IntervalIntegrable g volume 0 b := hfi.congr_uIoo (by
    rw [uIoo_of_le hb.le]; intro s hs; exact (heq (Ioo_subset_Icc_self hs)).symm)
  have hgib : IntervalIntegrable g volume b (2*c) := (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume b (2*c)).congr_uIoo (by
    rw [uIoo_of_le hbL]
    intro s hs
    exact (hzero hs).symm)
  have hgz : (∫ s in b..(2*c), g s) = 0 := by
    calc
      _ = ∫ s in b..(2*c), (0:ℝ) := intervalIntegral.integral_congr_Ioo_of_le hbL hzero
      _ = 0 := by simp
  have hgf : (∫ s in (0:ℝ)..b, g s) = ∫ s in (0:ℝ)..b, f s :=
    intervalIntegral.integral_congr (by simpa only [uIcc_of_le hb.le] using heq)
  have hi := intervalIntegral.integral_add_adjacent_intervals hgi hgib
  change (∫ s in (0:ℝ)..b, g s) + (∫ s in b..(2*c), g s) = (∫ s in (0:ℝ)..(2*c), g s) at hi
  rw [hgz,hgf,add_zero] at hi
  rw [hi]
  exact hB
end ThreeManifold.ReturningPassage
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end

open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage

end ThreeManifold.CompactMetric

namespace ThreeManifold.PassageDynamics
end ThreeManifold.PassageDynamics
namespace ThreeManifold.CompactMetric

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage
end

open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage TorusNeck
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.Neck
open Turning ReturningPassage ReturningCoefficients

end ThreeManifold.Neck
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
open CompactMetric

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage TorusNeck

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
namespace ThreeManifold.PassageDynamics
open Cometric Neck ReturningPassage

end ThreeManifold.PassageDynamics
end

section
open Set Filter Topology Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.Cometric
open Neck ReturningPassage

end ThreeManifold.Cometric
end

section
open Set Filter Topology
namespace ThreeManifold.PassageDynamics
open Cometric Neck ReturningPassage

end ThreeManifold.PassageDynamics
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage PassageDynamics

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
open CompactMetric
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric

namespace ThreeManifold.RiemannianCoordinates
open CompactMetric
end ThreeManifold.RiemannianCoordinates
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric
end

open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.ReturningPassage
open Set Filter Topology MeasureTheory Matrix
open scoped ContDiff Matrix.Norms.Elementwise
open Neck Cometric Turning ReturningCoefficients PassageDynamics SupportExtension


theorem solution : type_of% @_root_.OAI.ThreeManifold.ReturningPassage.truncated_return_nonnegative := @_root_.OAI.ThreeManifold.ReturningPassage.truncated_return_nonnegative
