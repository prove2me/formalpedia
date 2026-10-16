-- Prove2me | solution 1 for OAI.ThreeManifold.ReturningPassage.uniform_turning_parameters
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:51:46.329124+00:00
-- url     : https://prove2.me/submissions/ab04eec6-89b4-481c-9a70-467191f8e435

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Returning.lean:L1558-L1597
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.ReturningPassage.uniform_turning_parameters. The node keeps its source
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
import Theorems.Thm_OAI_ThreeManifold_Cometric_uniform_cometric_bounds

-- ---- from OAI.Geometry.ConjugatePoints.Cometric ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

/-!
# Radial profiles, cometrics, and collar estimates.
-/

section
open Set Filter Topology
open scoped ContDiff
namespace ThreeManifold.RadialProfile

end ThreeManifold.RadialProfile
end

open Set Filter
open scoped Topology ContDiff

namespace ThreeManifold.Cometric

lemma a_pos {u : ℝ} (hu : u < 2 / 3) : 0 < a u :=
  expNegInvGlue.pos_of_pos (by linarith)

end ThreeManifold.Cometric

open Set Filter
open scoped Topology ContDiff
namespace ThreeManifold.Collar
open Cometric

end ThreeManifold.Collar

end

end OAI

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

lemma sqnorm_nonneg (p : V2) : 0 ≤ sqnorm p := by unfold sqnorm; positivity

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

lemma beta_lt_one : beta < 1 := by
  have h : Real.exp (-(9 : ℝ) / 26) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  unfold beta
  linarith

lemma aZero_pos : 0 < aZero := Real.exp_pos _

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

lemma sourceMixed_pos (C : ℝ) : 0 < sourceMixed C := by
  have hp := a_pos (u := 0) (by norm_num)
  dsimp only [sourceMixed]
  positivity

theorem uniform_turning_parameters : ∃ δ₀ C : ℝ,
    0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧ 18 ≤ C ∧
    ∀ δ ∈ Ioc (0 : ℝ) δ₀,
      SmallParameter (3 * C) (sourceMixed C) δ ∧
      ∀ right : Bool, ∀ u ∈ Icc (0 : ℝ) 1, ∀ q : TVec,
        (sqnorm q / 9 ≤ qform (coordinateCometric right δ u) q ∧
          qform (coordinateCometric right δ u) q ≤ 18 * sqnorm q) ∧
        sqnorm (deriv (coordinateCometric right δ) u *ᵥ q) ≤ C ^ 2 * δ ^ 2 * sqnorm q ∧
        0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q ∧
        sqnorm (deriv (coordinateCometric right δ) u *ᵥ q) ≤
          C * δ * qform (-deriv (deriv (coordinateCometric right δ)) u) q := by
  obtain ⟨ε, D, hε, hhalf, hD, hb⟩ := uniform_cometric_bounds
  let C := 18 + D
  have hC : 18 ≤ C := by dsimp only [C]; linarith
  have hCp : 0 < C := by linarith
  have hDC : D ≤ C := by dsimp only [C]; linarith
  have hDCsq : D ^ 2 ≤ C ^ 2 := by nlinarith
  have hm := sourceMixed_pos C
  have ha := aZero_pos
  have hβ := beta_lt_one
  let ε' := min ε (min 1 (min (1 / (2 * sourceMixed C))
    ((1 - beta) / (2 * sourceMixed C + (3 * C) * aZero))))
  have hep : 0 < ε' := by dsimp only [ε']; positivity
  have hea : ε' ≤ ε := min_le_left _ _
  refine ⟨ε', C, hep, hea.trans hhalf, hC, ?_⟩
  intro δ hδ
  have hδ' : δ ∈ Ioc (0 : ℝ) ε := ⟨hδ.1, hδ.2.trans hea⟩
  have hs : SmallParameter (3 * C) (sourceMixed C) δ := by
    have hh := hδ.2.trans (min_le_right ε _)
    refine ⟨hδ.1, hh.trans (min_le_left _ _),
      (hh.trans (min_le_right _ _)).trans (min_le_left _ _),
      (hh.trans (min_le_right _ _)).trans (min_le_right _ _)⟩
  refine ⟨hs, ?_⟩
  intro right u hu q
  obtain ⟨hq, _, hd, hc, hdom⟩ := hb δ hδ' right u hu q
  refine ⟨hq, ?_, hc, ?_⟩
  · exact hd.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hDCsq (sq_nonneg _)) (sqnorm_nonneg q))
  · exact hdom.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hDC hδ.1.le) hc)

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
open OAI OAI.ThreeManifold OAI.ThreeManifold.ReturningPassage
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
open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
open Set Filter
open scoped Topology ContDiff
open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
open Neck Cometric ReturningCoefficients PassageDynamics Matrix DirectTurning Turning


theorem solution : type_of% @_root_.OAI.ThreeManifold.ReturningPassage.uniform_turning_parameters := @_root_.OAI.ThreeManifold.ReturningPassage.uniform_turning_parameters
