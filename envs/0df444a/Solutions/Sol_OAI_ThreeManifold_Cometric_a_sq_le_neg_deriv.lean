-- Prove2me | solution 1 for OAI.ThreeManifold.Cometric.a_sq_le_neg_deriv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:14:02.800061+00:00
-- url     : https://prove2.me/submissions/f03ec173-2c21-4128-99c6-8210b366f625

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Cometric.lean:L187-L201
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.Cometric.a_sq_le_neg_deriv. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric

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

lemma a_hasDerivAt (u : ℝ) :
    HasDerivAt a (-a u / (2 / 3 - u) ^ 2) u := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) (2 / 3 - u)
  simp only [Polynomial.eval_one, one_mul, Polynomial.derivative_one, sub_zero,
    mul_one, Polynomial.eval_pow, Polynomial.eval_X] at h
  have hcomp := h.comp u ((hasDerivAt_const u (2 / 3)).sub (hasDerivAt_id u))
  convert! hcomp using 1
  simp [a, div_eq_mul_inv, inv_pow, mul_comm]

lemma a_deriv (u : ℝ) : deriv a u = -a u / (2 / 3 - u) ^ 2 :=
  (a_hasDerivAt u).deriv

lemma a_sq_le_neg_deriv {u : ℝ} (hu : u ∈ Icc 0 1) :
    a u ^ 2 ≤ -deriv a u := by
  by_cases hcut : u < 2 / 3
  · have hx : 0 < 2 / 3 - u := by linarith
    have hxupper : (2 / 3 - u) ^ 2 ≤ (1 : ℝ) := by nlinarith [hu.1]
    have ha := a_nonneg u
    have ha' := (a_lt_one u).le
    rw [a_deriv, neg_div, neg_neg]
    apply (le_div_iff₀ (sq_pos_of_pos hx)).mpr
    calc
      a u ^ 2 * (2 / 3 - u) ^ 2 ≤ a u ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hxupper (sq_nonneg _)
      _ ≤ a u := by nlinarith
  · rw [a_deriv, a_eq_zero (le_of_not_gt hcut)]
    simp

end ThreeManifold.Cometric

open Set Filter
open scoped Topology ContDiff
namespace ThreeManifold.Collar
open Cometric

end ThreeManifold.Collar

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.Cometric
open Set Filter
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.ThreeManifold.Cometric.a_sq_le_neg_deriv := @_root_.OAI.ThreeManifold.Cometric.a_sq_le_neg_deriv
