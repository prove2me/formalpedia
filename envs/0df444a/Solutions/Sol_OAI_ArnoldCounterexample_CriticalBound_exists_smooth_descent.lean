-- Prove2me | solution 1 for OAI.ArnoldCounterexample.CriticalBound.exists_smooth_descent
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:10:58.828071+00:00
-- url     : https://prove2.me/submissions/29148375-8d86-47f8-bd8a-2b209ff6bb26

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Deformation.lean:L80-L110
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.CriticalBound.exists_smooth_descent. The node keeps its source
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
import Definitions.Def_OAI_Geometry_Arnold_Extension
import Definitions.Def_OAI_Geometry_Arnold_Deformation
import Theorems.Thm_OAI_ArnoldCounterexample_CriticalBound_local_lift_derivative_eq
import Theorems.Thm_OAI_ArnoldCounterexample_CriticalBound_rotationDerivative_phase
import Theorems.Thm_OAI_ArnoldCounterexample_Descent_adaptive_step

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
lemma rotationDerivative_contDiff (G : CV → ℝ) (hG : ContDiff ℝ ∞ G) (a b : Fin 5) :
    ContDiff ℝ ∞ (rotationDerivative G a b) :=
  (hG.fderiv_right (by simp)).clm_apply (matrixAction (rotGen a b)).contDiff

lemma negativeRotationMatrix_contDiff (G : CV → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (negativeRotationMatrix G) := by
  exact (ContDiff.sum (fun a _ ↦ ContDiff.sum (fun b _ ↦
    (rotationDerivative_contDiff G hG a b).smul contDiff_const))).neg

lemma gradientSquare_contDiff (G : CV → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (gradientSquare G) := by
  exact ContDiff.sum (fun a _ ↦ ContDiff.sum (fun b _ ↦
    (rotationDerivative_contDiff G hG a b).pow 2))

lemma gradientSquare_nonneg (G : CV → ℝ) (z : CV) : 0 ≤ gradientSquare G z :=
  Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))

lemma gradientSquare_eq_zero_iff (G : CV → ℝ) (z : CV) :
    gradientSquare G z = 0 ↔ ∀ a b, rotationDerivative G a b z = 0 := by
  simp only [gradientSquare, Finset.sum_eq_zero_iff_of_nonneg
    (fun a _ ↦ Finset.sum_nonneg (fun b _ ↦ sq_nonneg (rotationDerivative G a b z))),
    Finset.sum_eq_zero_iff_of_nonneg (fun b _ ↦ sq_nonneg (rotationDerivative G _ b z)),
    Finset.mem_univ, forall_const, sq_eq_zero_iff]

lemma negativeRotationMatrix_skew (G : CV → ℝ) (z : CV) :
    star (negativeRotationMatrix G z) = -negativeRotationMatrix G z := by
  simp only [negativeRotationMatrix, star_neg, star_sum, star_smul, star_trivial,
    rotGen_skew, smul_neg, Finset.sum_neg_distrib, neg_neg]

lemma negativeRotationMatrix_derivative (G : CV → ℝ) (z : CV) :
    fderiv ℝ G z (matrixAction (negativeRotationMatrix G z) z) = -gradientSquare G z := by
  simp only [negativeRotationMatrix, map_neg, map_sum, map_smul,
    neg_apply, sum_apply,
    smul_apply, gradientSquare, rotationDerivative, pow_two,
    smul_eq_mul]

lemma matrix_exp_contDiff : ContDiff ℝ ∞ (NormedSpace.exp : RM → RM) :=
  AnalyticOnNhd.contDiff (fun x _ ↦ NormedSpace.exp_analytic x)

lemma gradientCurve_contDiff (G : CV → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (gradientCurve G) :=
  (matrixAction.contDiff.comp (matrix_exp_contDiff.comp
    (contDiff_fst.smul ((negativeRotationMatrix_contDiff G hG).comp contDiff_snd)))).clm_apply
      contDiff_snd

lemma gradientCurve_preserves (G : CV → ℝ) (t : ℝ) (z : UnitQuadric) :
    IsUnitQuadric (gradientCurve G (t, z)) :=
  act_unit (expCurve (negativeRotationMatrix G z) (negativeRotationMatrix_skew G z) t) z

lemma gradientCurve_derivative_zero (G : CV → ℝ) (z : CV) :
    HasDerivAt (fun t ↦ gradientCurve G (t, z))
      (matrixAction (negativeRotationMatrix G z) z) 0 := by
  have h := (matrixAction.flip z).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_exp_smul_const (negativeRotationMatrix G z) 0)
  simpa only [zero_smul, NormedSpace.exp_zero, one_mul, Function.comp_def,
    ContinuousLinearMap.flip_apply, gradientCurve] using h

lemma gradientCurve_lyapunov_derivative (G : CV → ℝ) (hG : ContDiff ℝ ∞ G) (z : CV) :
    fderiv ℝ (fun p ↦ G (gradientCurve G p)) (0, z) (1, 0) = -gradientSquare G z := by
  have hc := (hG.differentiable (by simp) (gradientCurve G (0, z))).hasFDerivAt.comp_hasDerivAt 0
    (gradientCurve_derivative_zero G z)
  have hd := ((hG.comp (gradientCurve_contDiff G hG)).differentiable (by simp) (0, z)).hasFDerivAt.comp_hasDerivAt 0
    ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const 0 z))
  have heq := hd.unique hc
  convert! heq using 1; simp only [gradientCurve_zero, negativeRotationMatrix_derivative]

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms

attribute [local instance] OAI.ArnoldCounterexample.CriticalBound.instTopologicalSpaceRM_2
lemma negativeRotationMatrix_phase (G : CV → ℝ) (hG : ContDiff ℝ ∞ G)
    (hphase : ∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → G (a • (z : CV)) = G z)
    (z : UnitQuadric) (a : ℂ) (ha : Complex.normSq a = 1) :
    negativeRotationMatrix G (a • (z : CV)) = negativeRotationMatrix G z := by
  simp only [negativeRotationMatrix, rotationDerivative_phase G hG hphase z a ha]

lemma gradientSquare_phase (G : CV → ℝ) (hG : ContDiff ℝ ∞ G)
    (hphase : ∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → G (a • (z : CV)) = G z)
    (z : UnitQuadric) (a : ℂ) (ha : Complex.normSq a = 1) :
    gradientSquare G (a • (z : CV)) = gradientSquare G z := by
  simp only [gradientSquare, rotationDerivative_phase G hG hphase z a ha]

lemma gradientCurve_phase (G : CV → ℝ) (hG : ContDiff ℝ ∞ G)
    (hphase : ∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → G (a • (z : CV)) = G z)
    (t : ℝ) (z : UnitQuadric) (a : ℂ) (ha : Complex.normSq a = 1) :
    gradientCurve G (t, a • (z : CV)) = a • gradientCurve G (t, z) := by
  simp only [gradientCurve, negativeRotationMatrix_phase G hG hphase z a ha,
    matrixAction_apply, act_smul]

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms

lemma tangentMatrix_skew (z v : CV) : star (tangentMatrix z v) = -tangentMatrix z v := by
  ext i j
  simp [Matrix.star_apply, tangentMatrix, Complex.mul_re]
  ring

lemma complex_tangentMatrix (z v : CV) (i j : Fin 5) :
    complexMat (tangentMatrix z v) i j =
      v i * star (z j) + star (v i) * z j - z i * star (v j) - star (z i) * v j := by
  apply Complex.ext <;>
    simp [complexMat, tangentMatrix, Complex.mul_re, Complex.mul_im] <;> ring

lemma tangentMatrix_act (z : UnitQuadric) (v : CV) (hv : Horizontal z v) :
    act (tangentMatrix z v) z = v := by
  have hn : ∑ j, star ((z : CV) j) * (z : CV) j = (1 : ℂ) := by
    calc
      _ = ((∑ j, Complex.normSq ((z : CV) j) : ℝ) : ℂ) := by
        simp only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
        rfl
      _ = 1 := by exact_mod_cast z.property.1
  have hp : ∑ j, (z : CV) j * (z : CV) j = (0 : ℂ) := by
    simpa only [quadricPolynomial, ← pow_two] using z.property.2
  have hconj : ∑ j, star (v j) * (z : CV) j = (0 : ℂ) := by
    have h := congrArg star hv.1
    simpa only [star_sum, star_mul, star_star, star_zero, mul_comm] using h
  ext i
  simp only [act, Matrix.mulVec, dotProduct, complex_tangentMatrix]
  calc
    _ = v i * (∑ j, star ((z : CV) j) * (z : CV) j) +
      star (v i) * (∑ j, (z : CV) j * (z : CV) j) -
      (z : CV) i * (∑ j, star (v j) * (z : CV) j) -
      star ((z : CV) i) * (∑ j, (z : CV) j * v j) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = v i := by rw [hn, hp, hconj, hv.2]; ring

lemma skew_rotation_sum (M : RM) (hM : star M = -M) :
    (∑ a : Fin 5, ∑ b : Fin 5, M b a • rotGen a b) = (2 : ℝ) • M := by
  have hm (i j : Fin 5) : M j i = -M i j := by
    have h := congrFun (congrFun hM i) j
    simpa only [Matrix.star_apply, star_trivial, Matrix.neg_apply] using h
  ext i j
  change (∑ a : Fin 5, ∑ b : Fin 5, M b a * (rotGen a b) i j) = 2 * M i j
  simp [rotGen, Matrix.single_apply, mul_sub, Finset.sum_sub_distrib,
    mul_ite, ite_and]
  rw [hm]
  ring

/-- Vanishing of the finitely many rotation derivatives really implies
vanishing in every horizontal tangent direction. -/
lemma horizontal_derivative_of_rotation_zero (G : CV → ℝ) (z : UnitQuadric)
    (hzero : ∀ a b, rotationDerivative G a b z = 0)
    (v : CV) (hv : Horizontal z v) : fderiv ℝ G z v = 0 := by
  have heq := congrArg (fun M : RM ↦ fderiv ℝ G z (matrixAction M z))
    (skew_rotation_sum (tangentMatrix z v) (tangentMatrix_skew z v))
  have hzero' (a b : Fin 5) : fderiv ℝ G z (act (rotGen a b) z) = 0 := hzero a b
  simp only [map_sum, sum_apply, map_smul, smul_apply, matrixAction_apply,
    hzero', tangentMatrix_act z v hv,
    smul_eq_mul, mul_zero, Finset.sum_const_zero] at heq
  linarith

end ArnoldCounterexample.CriticalBound

end

end OAI

-- ---- from OAI.Geometry.Arnold.Deformation ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Quadric

lemma project_phase (z : UnitQuadric) (a : ℂ) (ha : Complex.normSq a = 1) :
    project ⟨a • (z : CV), unit_phase z a ha⟩ = project z := by
  apply Subtype.ext
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨a, rfl⟩

lemma project_eq_phase (z w : UnitQuadric) (heq : project w = project z) :
    ∃ a : ℂ, Complex.normSq a = 1 ∧ (w : CV) = a • (z : CV) := by
  have hp := congrArg Subtype.val heq
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hp
  have hn := w.property.1
  rw [← ha, normSquared_smul, z.property.1, mul_one] at hn
  exact ⟨a, hn, ha.symm⟩

lemma extension_phase {h : Q3 → ℝ} {G : CV → ℝ}
    (hGagree : ∀ z : UnitQuadric, G z = h (project z))
    (z : UnitQuadric) (a : ℂ) (ha : Complex.normSq a = 1) :
    G (a • (z : CV)) = G z := by
  rw [hGagree ⟨a • (z : CV), unit_phase z a ha⟩, project_phase z a ha, hGagree z]

lemma stationary_isCritical {h : Q3 → ℝ} {G : CV → ℝ}
    (hG : ContDiff ℝ ∞ G) (hGagree : ∀ z : UnitQuadric, G z = h (project z))
    (z : UnitQuadric) (hz : gradientSquare G z = 0) :
    IsCritical h (project z) := by
  intro w hw U g hg v hv
  obtain ⟨a, ha, hwa⟩ := project_eq_phase z w hw
  have hzero : gradientSquare G w = 0 := by
    rw [hwa, gradientSquare_phase G hG (extension_phase hGagree) z a ha, hz]
  rw [local_lift_derivative_eq hG hGagree w U g hg v hv]
  exact horizontal_derivative_of_rotation_zero G w
    ((gradientSquare_eq_zero_iff G w).mp hzero) v hv

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Quadric ArnoldCounterexample.Descent

/-- Smooth phase-equivariant, strictly descending discrete deformation of the
literal quadric. This supplies the deformation step for arbitrary smooth functions,
including highly degenerate ones, without assuming an ODE existence theorem. -/
theorem exists_smooth_descent {h : Q3 → ℝ} {G : CV → ℝ}
    (hG : ContDiff ℝ ∞ G) (hGagree : ∀ z : UnitQuadric, G z = h (project z)) :
    ∃ D : CV → CV, ContDiff ℝ ∞ D ∧
      (∀ z : UnitQuadric, IsUnitQuadric (D z)) ∧
      (∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → D (a • (z : CV)) = a • D z) ∧
      (∀ z : UnitQuadric, G (D z) ≤ G z) ∧
      (∀ z : UnitQuadric, G (D z) = G z → IsCritical h (project z)) := by
  obtain ⟨c, _hc, hstep⟩ := adaptive_step isCompact_unitQuadric
    (fun p ↦ G (gradientCurve G p)) (hG.comp (gradientCurve_contDiff G hG))
    (gradientSquare G) (gradientSquare_contDiff G hG).continuous
    (fun z _ ↦ gradientSquare_nonneg G z)
    (fun z _ ↦ gradientCurve_lyapunov_derivative G hG z)
  let D : CV → CV := fun z ↦ gradientCurve G (c * gradientSquare G z, z)
  have hD : ContDiff ℝ ∞ D := (gradientCurve_contDiff G hG).comp
    ((contDiff_const.mul (gradientSquare_contDiff G hG)).prodMk contDiff_id)
  refine ⟨D, hD, fun z ↦ gradientCurve_preserves G _ z, ?_, ?_, ?_⟩
  · intro z a ha
    dsimp only [D]
    rw [gradientSquare_phase G hG (extension_phase hGagree) z a ha,
      gradientCurve_phase G hG (extension_phase hGagree) _ z a ha]
  · intro z
    simpa only [gradientCurve_zero] using (hstep z z.property).2.2.1
  · intro z heq
    apply stationary_isCritical hG hGagree z
    by_contra hz
    have hlt := (hstep z z.property).2.2.2 hz
    have hlt' : G (D z) < G z := by simpa only [gradientCurve_zero] using hlt
    exact (ne_of_lt hlt') heq

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Quadric ArnoldCounterexample.Forms ArnoldCounterexample.Descent

end ArnoldCounterexample.CriticalBound

end

end OAI

-- ---- platform node ----
open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.CriticalBound
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ArnoldCounterexample.Quadric ArnoldCounterexample.Descent


theorem solution : type_of% @_root_.OAI.ArnoldCounterexample.CriticalBound.exists_smooth_descent := @_root_.OAI.ArnoldCounterexample.CriticalBound.exists_smooth_descent
