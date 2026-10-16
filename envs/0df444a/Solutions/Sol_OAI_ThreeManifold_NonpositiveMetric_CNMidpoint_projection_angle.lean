-- Prove2me | solution 1 for OAI.ThreeManifold.NonpositiveMetric.CNMidpoint.projection_angle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:25:52.406114+00:00
-- url     : https://prove2.me/submissions/50a8d398-0b09-484d-acba-be1a173f839e

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Convexity.lean:L137-L152
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.NonpositiveMetric.CNMidpoint.projection_angle. The node keeps its source
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

-- ---- from OAI.Geometry.ConjugatePoints.Convexity ----
namespace OAI

noncomputable section

/-!
# Midpoint convexity, minsets, and the semisimple shear obstruction.
-/

section
open Set Filter Topology
namespace ThreeManifold.NonpositiveMetric
variable (X : Type*) [MetricSpace X]

namespace CNMidpoint
variable {X} (C : CNMidpoint X)
include C

lemma mid_dist_left (x y : X) : dist (C.mid x y) x = dist x y / 2 := by
  have hx := C.cn x y x
  have hy := C.cn x y y
  simp only [dist_self,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_add,add_zero,dist_comm y x] at hx hy
  have ht := dist_triangle x (C.mid x y) y
  rw [dist_comm x (C.mid x y)] at ht
  nlinarith [(show 0 ≤ dist (C.mid x y) x from dist_nonneg),(show 0 ≤ dist (C.mid x y) y from dist_nonneg),(show 0 ≤ dist x y from dist_nonneg),
    sq_nonneg (dist (C.mid x y) x-dist (C.mid x y) y)]
end CNMidpoint
end ThreeManifold.NonpositiveMetric
end

section
open Set Filter Topology Function
namespace ThreeManifold.NonpositiveMetric.CNMidpoint

section
variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)

include C

lemma halfSequence_mem {S : Set X} (hS : C.MidConvex S) {p q : X}
    (hp : p ∈ S) (hq : q ∈ S) (n : ℕ) : C.halfSequence p q n ∈ S := by
  induction n with
  | zero => exact hq
  | succ n ih => exact hS hp ih

lemma halfSequence_dist (p q : X) (n : ℕ) :
    dist p (C.halfSequence p q n) = (1/2:ℝ)^n * dist p q := by
  induction n with
  | zero => simp [halfSequence]
  | succ n ih =>
    rw [halfSequence,dist_comm,C.mid_dist_left,ih,pow_succ]
    ring

lemma halfSequence_CN (p q x : X) (n : ℕ) :
    dist (C.halfSequence p q n) x ^2 ≤
      (1-(1/2:ℝ)^n)*dist p x ^2 + (1/2:ℝ)^n*dist q x ^2 -
      (1/2:ℝ)^n*(1-(1/2:ℝ)^n)*dist p q ^2 := by
  induction n with
  | zero => simp [halfSequence]
  | succ n ih =>
    have hh := C.cn p (C.halfSequence p q n) x
    rw [C.halfSequence_dist] at hh
    rw [halfSequence, pow_succ (1/2:ℝ) n]
    nlinarith

lemma projection_angle {S : Set X} (hS : C.MidConvex S) {x p : X} (hp : p ∈ S)
    (hm : ∀ z ∈ S, dist x p ≤ dist x z) {q : X} (hq : q ∈ S) :
    dist x p ^2 + dist p q ^2 ≤ dist x q ^2 := by
  have hh (n : ℕ) : dist x p ^2 + (1-(1/2:ℝ)^n)*dist p q ^2 ≤ dist x q ^2 := by
    have hmin := hm _ (C.halfSequence_mem hS hp hq n)
    have hc := C.halfSequence_CN p q x n
    rw [dist_comm p x,dist_comm q x,dist_comm (C.halfSequence p q n) x] at hc
    have ht : 0 < (1/2:ℝ)^n := pow_pos (by norm_num) _
    have hs : dist x p ^2 ≤ dist x (C.halfSequence p q n)^2 :=
      sq_le_sq₀ dist_nonneg dist_nonneg |>.mpr hmin
    nlinarith
  have ht : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hl := le_of_tendsto ((tendsto_const_nhds.add ((tendsto_const_nhds.sub ht).mul_const
    (dist p q ^2)))) (Filter.Eventually.of_forall hh)
  simpa using hl

end

section
variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)
include C

end

section
variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)

include C

end

section
variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)
include C
end

section
variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)

include C
end

section
variable {X : Type*} [MetricSpace X] [ProperSpace X] (C : CNMidpoint X)

include C
end

section
variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)

include C
end

variable {X : Type*} [MetricSpace X] (C : CNMidpoint X)
include C

end ThreeManifold.NonpositiveMetric.CNMidpoint
end

open Set Filter Topology Function
namespace ThreeManifold.NonpositiveMetric.CNMidpoint
variable {X : Type*} [MetricSpace X] [ProperSpace X] (C : CNMidpoint X)
include C

end ThreeManifold.NonpositiveMetric.CNMidpoint

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.NonpositiveMetric OAI.ThreeManifold.NonpositiveMetric.CNMidpoint
open Set Filter Topology Function


theorem solution : type_of% @_root_.OAI.ThreeManifold.NonpositiveMetric.CNMidpoint.projection_angle := @_root_.OAI.ThreeManifold.NonpositiveMetric.CNMidpoint.projection_angle
