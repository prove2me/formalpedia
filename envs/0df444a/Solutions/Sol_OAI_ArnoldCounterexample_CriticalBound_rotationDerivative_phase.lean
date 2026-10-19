-- Prove2me | solution 1 for OAI.ArnoldCounterexample.CriticalBound.rotationDerivative_phase
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:58:57.207701+00:00
-- url     : https://prove2.me/submissions/f8545bb9-d62a-449c-a51c-7f07e9c71e37

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Coordinates.lean:L126-L143
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.CriticalBound.rotationDerivative_phase. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates

-- ---- from OAI.Geometry.Arnold.Orbit ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator

namespace ArnoldCounterexample

namespace CriticalBound
open Matrix

lemma complexMat_mul (A B : RM) : complexMat (A * B) = complexMat A * complexMat B := by
  ext i j
  simp [complexMat, Matrix.mul_apply]

lemma complexMat_star (A : RM) : complexMat (star A) = star (complexMat A) := by
  ext i j
  simp [complexMat, Matrix.star_apply]

lemma act_smul (A : RM) (a : ℂ) (z : CV) : act A (a • z) = a • act A z := by
  exact Matrix.mulVec_smul _ _ _

lemma act_preserves_hermitian (A : O5) (z w : CV) :
    star (act A z) ⬝ᵥ act A w = star z ⬝ᵥ w := by
  have hA : star (complexMat A) * complexMat A = 1 := by
    rw [← complexMat_star, ← complexMat_mul, A.property.1, complexMat_one]
  calc
    star (act A z) ⬝ᵥ act A w = (star z ᵥ* star (complexMat A)) ⬝ᵥ (complexMat A *ᵥ w) := by
      simp only [act, Matrix.star_mulVec, Matrix.star_eq_conjTranspose]
    _ = star z ⬝ᵥ (star (complexMat A) *ᵥ (complexMat A *ᵥ w)) := (Matrix.dotProduct_mulVec _ _ _).symm
    _ = star z ⬝ᵥ w := by rw [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]

lemma rotGen_skew (a b : Fin 5) : star (rotGen a b) = -rotGen a b := by
  ext i j
  simp [rotGen, Matrix.star_apply, Matrix.single_apply, sub_eq_add_neg, and_comm]

end CriticalBound
end ArnoldCounterexample

namespace ArnoldCounterexample.CriticalBound

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound

attribute [local instance] OAI.ArnoldCounterexample.CriticalBound.instTopologicalSpaceRM
lemma act_star (A : RM) (z : CV) : act A (star z) = star (act A z) := by
  ext i
  simp [act, complexMat, Matrix.mulVec, dotProduct]

lemma act_preserves_bilinear (A : O5) (z w : CV) :
    act A z ⬝ᵥ act A w = z ⬝ᵥ w := by
  simpa only [act_star, star_star] using act_preserves_hermitian A (star z) w

lemma act_preserves_quadricPolynomial (A : O5) (z : CV) :
    quadricPolynomial (act A z) = quadricPolynomial z := by
  simpa only [quadricPolynomial, dotProduct, pow_two] using act_preserves_bilinear A z z

lemma normSquared_eq_re (z : CV) : normSquared z = (star z ⬝ᵥ z).re := by
  simp [normSquared, dotProduct, Complex.normSq, Complex.mul_re]

lemma act_preserves_normSquared (A : O5) (z : CV) :
    normSquared (act A z) = normSquared z := by
  rw [normSquared_eq_re, normSquared_eq_re, act_preserves_hermitian]

lemma act_unit (A : O5) (z : UnitQuadric) : IsUnitQuadric (act A z) := by
  exact ⟨(act_preserves_normSquared A z).trans z.property.1,
    (act_preserves_quadricPolynomial A z).trans z.property.2⟩

end ArnoldCounterexample.CriticalBound

end

end OAI

-- ---- from OAI.Geometry.Arnold.Coordinates ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms

attribute [local instance] OAI.ArnoldCounterexample.CriticalBound.instTopologicalSpaceRM_1
end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms

attribute [local instance] OAI.ArnoldCounterexample.CriticalBound.instTopologicalSpaceRM_2
lemma matrix_orbit_derivative_zero (X : RM) (z : CV) :
    HasDerivAt (fun t : ℝ ↦ matrixAction (NormedSpace.exp (t • X)) z)
      (matrixAction X z) 0 := by
  have h := (matrixAction.flip z).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_exp_smul_const X 0)
  simpa only [zero_smul, NormedSpace.exp_zero, one_mul, Function.comp_def,
    ContinuousLinearMap.flip_apply] using h

lemma rotationDerivative_phase (G : CV → ℝ) (hG : ContDiff ℝ ∞ G)
    (hphase : ∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → G (a • (z : CV)) = G z)
    (z : UnitQuadric) (a : ℂ) (ha : Complex.normSq a = 1) (i j : Fin 5) :
    rotationDerivative G i j (a • (z : CV)) = rotationDerivative G i j z := by
  let c : ℝ → CV := fun t ↦ matrixAction (NormedSpace.exp (t • rotGen i j)) z
  have hc := matrix_orbit_derivative_zero (rotGen i j) (z : CV)
  have hc0 : c 0 = z := by
    simp [c, matrixAction_apply, act, complexMat_one]
  have hcu (t : ℝ) : IsUnitQuadric (c t) := act_unit (expCurve (rotGen i j) (rotGen_skew i j) t) z
  have hd := (hG.differentiable (by simp) (c 0)).hasFDerivAt.comp_hasDerivAt 0 hc
  have he := (hG.differentiable (by simp) (a • c 0)).hasFDerivAt.comp_hasDerivAt 0 (hc.const_smul a)
  have heq : (fun t : ℝ ↦ G (a • c t)) = (fun t ↦ G (c t)) :=
    funext (fun t ↦ hphase ⟨c t, hcu t⟩ a ha)
  have he' : HasDerivAt (fun t : ℝ ↦ G (a • c t))
      (fderiv ℝ G (a • c 0) (a • matrixAction (rotGen i j) z)) 0 := he
  rw [heq] at he'
  have h := he'.unique hd
  simpa only [hc0, rotationDerivative, matrixAction_apply, act_smul] using h

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms

end ArnoldCounterexample.CriticalBound

end

end OAI

-- ---- platform node ----
open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.CriticalBound
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open ArnoldCounterexample.Forms
attribute [local instance] OAI.ArnoldCounterexample.CriticalBound.instTopologicalSpaceRM_2


theorem solution : type_of% @_root_.OAI.ArnoldCounterexample.CriticalBound.rotationDerivative_phase := @_root_.OAI.ArnoldCounterexample.CriticalBound.rotationDerivative_phase
