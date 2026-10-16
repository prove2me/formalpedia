-- Prove2me | solution 1 for OAI.ThreeManifold.Cometric.coordinateCometric_end_deriv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:43:32.563077+00:00
-- url     : https://prove2.me/submissions/bdbead5f-35fb-4d75-9fad-446d93f2f431

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Returning.lean:L842-L857
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.Cometric.coordinateCometric_end_deriv. The node keeps its source
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

lemma P_left_endpoint {δ τ : ℝ} (hτ : τ ≤ 1 / 4) :
    P δ τ = !![1 + δ * A τ, 0; 0, 1 + δ * A 1] := by
  have hc := χ_eq_zero (show τ ≤ 5 / 12 by linarith)
  have hA := A_plateau (show 2 / 3 ≤ 1 - τ by linarith) (show (2 / 3 : ℝ) ≤ 1 by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P, d₁, d₂, shear, hc, hA]

lemma P_right_endpoint {δ τ : ℝ} (hτ : τ ≤ 1 / 4) :
    PEnd δ τ = !![1 + δ * A τ, 0; 0, 1 + δ * A 1] := by
  have hc := χ_eq_one (show 7 / 12 ≤ 1 - τ by linarith)
  have hA := A_plateau (show 2 / 3 ≤ 1 - τ by linarith) (show (2 / 3 : ℝ) ≤ 1 by norm_num)
  have he : 1 - (1 - τ) = τ := by ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PEnd, C₂, P, d₁, d₂, shear, hc, hA, he,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;> ring

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

lemma coordinateCometric_end {right : Bool} {δ t : ℝ} (ht : t ≤ 1 / 4) :
    coordinateCometric right δ t = !![1 + δ * A t, 0; 0, 1 + δ * A 1] := by
  cases right
  · exact P_left_endpoint ht
  · exact P_right_endpoint ht

lemma coordinateCometric_end_deriv {right : Bool} {δ t : ℝ} (ht : t < 1 / 4) :
    deriv (coordinateCometric right δ) t = !![δ * a t, 0; 0, 0] := by
  have he : coordinateCometric right δ =ᶠ[𝓝 t]
      (fun u => !![1 + δ * A u, 0; 0, 1 + δ * A 1]) := by
    filter_upwards [Iio_mem_nhds ht] with u hu
    exact coordinateCometric_end hu.le
  have hd : HasDerivAt (fun u => !![1 + δ * A u, 0; 0, 1 + δ * A 1])
      !![δ * a t, 0; 0, 0] t := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;> dsimp
    · exact ((A_hasDerivAt t).const_mul δ).const_add 1
    all_goals exact hasDerivAt_const _ _
  exact (hd.congr_of_eventuallyEq he).deriv

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

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.Cometric
open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set MeasureTheory
open scoped Interval
open Set MeasureTheory
open scoped Interval
open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
open Neck Matrix


theorem solution : type_of% @_root_.OAI.ThreeManifold.Cometric.coordinateCometric_end_deriv := @_root_.OAI.ThreeManifold.Cometric.coordinateCometric_end_deriv
