-- Prove2me | solution 1 for OAI.ThreeManifold.Cometric.Q_elliptic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:29:17.414552+00:00
-- url     : https://prove2.me/submissions/18012aa5-9aa1-4356-a4f5-46ddb095860a

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Neck.lean:L977-L1001
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.Cometric.Q_elliptic. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck

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

lemma A_le {u : ℝ} (hu : 0 ≤ u) : A u ≤ u := by
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hu
    (a_smooth.continuous.intervalIntegrable 0 u) (continuous_const.intervalIntegrable 0 u)
    (fun x (_hx : x ∈ Icc 0 u) => (a_lt_one x).le)
  simpa [A] using h

lemma χ_nonneg (t : ℝ) : 0 ≤ χ t := Real.smoothTransition.nonneg _
lemma χ_le_one (t : ℝ) : χ t ≤ 1 := Real.smoothTransition.le_one _

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

lemma d₁_bounds {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1) :
    1 ≤ d₁ δ t ∧ d₁ δ t ≤ 2 := by
  have hA := A_nonneg ht.1
  have hA' := A_le ht.1
  dsimp [d₁]
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg hδ.1 hA)
  · nlinarith [hδ.2, mul_nonneg hδ.1 (by linarith [ht.2] : 0 ≤ 1 - A t)]

lemma d₂_bounds {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1) :
    1 ≤ d₂ δ t ∧ d₂ δ t ≤ 2 := by
  exact d₁_bounds hδ ⟨by linarith [ht.2], by linarith [ht.1]⟩

lemma shear_bounds {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) :
    0 ≤ shear δ t ∧ shear δ t ≤ 1 := by
  have hc := χ_nonneg t
  have hc' := χ_le_one t
  dsimp [shear]
  constructor
  · positivity
  · calc
      δ ^ 2 * χ t ≤ δ ^ 2 * 1 := mul_le_mul_of_nonneg_left hc' (sq_nonneg δ)
      _ ≤ 1 := by nlinarith [hδ.1, hδ.2]

lemma shear_norm_upper (x y c : ℝ) (hc : |c| ≤ 1) :
    x ^ 2 + (y + c * x) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2) := by
  have hc' : c ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one c).mpr hc
  have hcx := mul_nonneg (sub_nonneg.mpr hc') (sq_nonneg x)
  nlinarith [sq_nonneg (y - c * x), sq_nonneg y]

lemma shear_norm_lower (x y c : ℝ) (hc : |c| ≤ 1) :
    (x ^ 2 + y ^ 2) / 3 ≤ x ^ 2 + (y + c * x) ^ 2 := by
  have h := shear_norm_upper x (y + c * x) (-c) (by simpa using hc)
  have he : y + c * x + -c * x = y := by ring
  rw [he] at h
  linarith

lemma Q_formula {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1) :
    Q δ t = !![1 / d₁ δ t, -shear δ t / d₁ δ t;
      -shear δ t / d₁ δ t, 1 / d₂ δ t + shear δ t ^ 2 / d₁ δ t] := by
  have h1 : d₁ δ t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (d₁_bounds hδ ht).1)
  have h2 : d₂ δ t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (d₂_bounds hδ ht).1)
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp; ring

lemma qform_Q {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1) (p : V2) :
    qform (Q δ t) p = (p 0 - shear δ t * p 1) ^ 2 / d₁ δ t + p 1 ^ 2 / d₂ δ t := by
  rw [Q_formula hδ ht]
  simp [qform, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

lemma Q_elliptic {δ t : ℝ} (hδ : δ ∈ Icc 0 (1 / 2)) (ht : t ∈ Icc 0 1) (p : V2) :
    sqnorm p / 6 ≤ qform (Q δ t) p ∧ qform (Q δ t) p ≤ 3 * sqnorm p := by
  have hd1 := d₁_bounds hδ ht
  have hd2 := d₂_bounds hδ ht
  have hc := shear_bounds (t := t) hδ
  have habs : |-shear δ t| ≤ 1 := by rw [abs_neg, abs_of_nonneg hc.1]; exact hc.2
  have hl := shear_norm_lower (p 1) (p 0) (-shear δ t) habs
  have hu := shear_norm_upper (p 1) (p 0) (-shear δ t) habs
  have hr1 : (1 / 2 : ℝ) ≤ (d₁ δ t)⁻¹ ∧ (d₁ δ t)⁻¹ ≤ 1 := by
    constructor
    · simpa only [one_div] using one_div_le_one_div_of_le (by linarith [hd1.1]) hd1.2
    · simpa using one_div_le_one_div_of_le zero_lt_one hd1.1
  have hr2 : (1 / 2 : ℝ) ≤ (d₂ δ t)⁻¹ ∧ (d₂ δ t)⁻¹ ≤ 1 := by
    constructor
    · simpa only [one_div] using one_div_le_one_div_of_le (by linarith [hd2.1]) hd2.2
    · simpa using one_div_le_one_div_of_le zero_lt_one hd2.1
  rw [qform_Q hδ ht]
  dsimp [sqnorm]
  rw [neg_mul, ← sub_eq_add_neg] at hl hu
  have h11 := mul_le_mul_of_nonneg_left hr1.1 (sq_nonneg (p 0 - shear δ t * p 1))
  have h12 := mul_le_mul_of_nonneg_left hr1.2 (sq_nonneg (p 0 - shear δ t * p 1))
  have h21 := mul_le_mul_of_nonneg_left hr2.1 (sq_nonneg (p 1))
  have h22 := mul_le_mul_of_nonneg_left hr2.2 (sq_nonneg (p 1))
  simp only [div_eq_mul_inv]
  constructor <;> nlinarith

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

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.Cometric
open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Matrix
open scoped Matrix.Norms.Elementwise


theorem solution : type_of% @_root_.OAI.ThreeManifold.Cometric.Q_elliptic := @_root_.OAI.ThreeManifold.Cometric.Q_elliptic
