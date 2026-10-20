-- Prove2me | solution 1 for OAI.ArnoldCounterexample.Construction.fixed_factor_critical
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:19:38.910865+00:00
-- url     : https://prove2.me/submissions/8e07a204-633e-449a-a367-acc678518742

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/FixedPoints.lean:L61-L90
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.Construction.fixed_factor_critical. The node keeps its source
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
import Definitions.Def_OAI_Geometry_Arnold_Exterior
import Definitions.Def_OAI_Geometry_Arnold_Homotopy
import Definitions.Def_OAI_Geometry_Arnold_Volume
import Definitions.Def_OAI_Geometry_Arnold_Obstruction
import Definitions.Def_OAI_Geometry_Arnold_ThreePoints
import Definitions.Def_OAI_Geometry_Arnold_Factors
import Definitions.Def_OAI_Geometry_Arnold_Field
import Definitions.Def_OAI_Geometry_Arnold_CompactField
import Definitions.Def_OAI_Geometry_Arnold_Midpoint
import Definitions.Def_OAI_Geometry_Arnold_MidpointGeometry
import Definitions.Def_OAI_Geometry_Arnold_Parameter
import Definitions.Def_OAI_Geometry_Arnold_Quotient
import Definitions.Def_OAI_Geometry_Arnold_Hamiltonian
import Theorems.Thm_OAI_ArnoldCounterexample_Construction_fixed_zero_coordinate
import Theorems.Thm_OAI_ArnoldCounterexample_Field_core_homogeneous

-- ---- from OAI.Geometry.Arnold.Factors ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff

namespace ArnoldCounterexample.Factors
open ArnoldCounterexample.Quadric ArnoldCounterexample.ThreePoints

lemma sphere_norm_identity (z : CV) :
    sqNorm (leftSphere z) + (fourPolynomial z).re ^ 2 + (fourPolynomial z).im ^ 2 = fourNorm z ^ 2 ∧
    sqNorm (rightSphere z) + (fourPolynomial z).re ^ 2 + (fourPolynomial z).im ^ 2 = fourNorm z ^ 2 := by
  change (((moment 1 2 z + moment 3 4 z)^2 + (moment 1 3 z - moment 2 4 z)^2 +
    (moment 1 4 z + moment 2 3 z)^2) + _ + _ = _) ∧
    (((moment 1 2 z - moment 3 4 z)^2 + (moment 1 3 z + moment 2 4 z)^2 +
    (moment 1 4 z - moment 2 3 z)^2) + _ + _ = _)
  norm_num [ moment_real, fourPolynomial, fourNorm,
    Fin.sum_univ_succ, Fin.succ, Fin.reduceFinMk, pow_two, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  constructor <;> ring!

lemma sphereFactors_mem (z : UnitQuadric) (hz : (z : CV) 0 = 0) :
    sphereFactors z ∈ sphereProduct := by
  have hn : fourNorm z = 1 := by
    have h := z.property.1
    simpa only [normSquared, Fin.sum_univ_succ, hz, Complex.normSq_zero, zero_add, fourNorm] using h
  have hp : fourPolynomial z = 0 := by
    have h := z.property.2
    simpa only [quadricPolynomial, Fin.sum_univ_succ, hz, zero_pow (by decide : 2 ≠ 0), zero_add,
      fourPolynomial] using h
  have h := sphere_norm_identity z
  simpa only [sphereFactors, sphereProduct, Set.mem_ofPred_eq, hp, Complex.zero_re,
    Complex.zero_im, zero_pow (by decide : 2 ≠ 0), add_zero, hn, one_pow] using h

end ArnoldCounterexample.Factors

namespace ArnoldCounterexample.Factors
open ArnoldCounterexample.Quadric

end ArnoldCounterexample.Factors

end

end OAI

-- ---- from OAI.Geometry.Arnold.Field ----
namespace OAI

universe uι

noncomputable section
open scoped BigOperators ContDiff

namespace ArnoldCounterexample.Field
open ArnoldCounterexample.Quadric ArnoldCounterexample.ThreePoints ArnoldCounterexample.Factors
open scoped ContDiff Topology
open Set Filter

end ArnoldCounterexample.Field

namespace ArnoldCounterexample.Field
open ArnoldCounterexample.Quadric ArnoldCounterexample.ThreePoints ArnoldCounterexample.Factors
open scoped ContDiff Topology
open Set Filter

lemma radial_eq (s : ℝ) (hs : s ∈ Icc (1/32 : ℝ) 32) : radial s = (Real.sqrt s)⁻¹ :=
  exists_radial.choose_spec.2 s hs

lemma radial_eventually {s : ℝ} (hs : s ∈ Ioo (1/32 : ℝ) 32) :
    radial =ᶠ[𝓝 s] fun x ↦ (Real.sqrt x)⁻¹ := by
  filter_upwards [isOpen_Ioo.mem_nhds hs] with x hx
  exact radial_eq x ⟨le_of_lt hx.1, le_of_lt hx.2⟩

lemma radial_squared (r : ℝ) (hr : r ∈ Ioo (1/2 : ℝ) 2) :
    radial (r^2) = r⁻¹ ∧ deriv radial (r^2) = -(2*r^3)⁻¹ := by
  have hr0 : 0 < r := lt_trans (by norm_num) hr.1
  have hs : r^2 ∈ Ioo (1/32 : ℝ) 32 := by constructor <;> nlinarith [hr.1, hr.2, sq_nonneg (r-2), sq_nonneg (r-1/2)]
  have hsqrt : Real.sqrt (r^2) = r := Real.sqrt_sq hr0.le
  have he : radial (r^2) = r⁻¹ := by rw [radial_eq _ ⟨hs.1.le,hs.2.le⟩, hsqrt]
  refine ⟨he, ?_⟩
  have hd := (((hasDerivAt_id (r^2)).sqrt (sq_pos_of_pos hr0).ne').inv ((Real.sqrt_pos.2 (sq_pos_of_pos hr0)).ne'))
  have hb := hd.congr_of_eventuallyEq (radial_eventually hs)
  rw [hb.deriv]
  simp only [id_eq, hsqrt]
  field_simp

lemma radial_at_one : radial 1 = 1 ∧ deriv radial 1 = -(1/2 : ℝ) := by
  simpa using radial_squared 1 (by norm_num)

end ArnoldCounterexample.Field

end

end OAI

-- ---- from OAI.Geometry.Arnold.CompactField ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff

namespace ArnoldCounterexample.Field
open ArnoldCounterexample.Quadric ArnoldCounterexample.ThreePoints ArnoldCounterexample.Factors
open scoped ContDiff Topology NNReal
open Set Filter

lemma rotor_zero_coordinate (a b : Fin 5) (ha : a ≠ 0) (hb : b ≠ 0) (z : CV) : rotor a b z 0 = 0 := by
  simp [rotor_apply, Ne.symm ha, Ne.symm hb]

lemma left_zero_coordinate (i : Fin 3) (z : CV) : leftOperator i z 0 = 0 := by
  fin_cases i <;> simp [leftOperator, rotor_zero_coordinate]

lemma right_zero_coordinate (i : Fin 3) (z : CV) : rightOperator i z 0 = 0 := by
  fin_cases i <;> simp [rightOperator, rotor_zero_coordinate]

lemma core_zero_coordinate (z : CV) : core z 0 = 0 := by
  simp [core, mixedField, selfField, Finset.sum_apply, left_zero_coordinate, right_zero_coordinate]

lemma vectorField_zero_coordinate (z : CV) : vectorField z 0 = 0 := by
  simp [vectorField, core_zero_coordinate]

end ArnoldCounterexample.Field

end

end OAI

-- ---- from OAI.Geometry.Arnold.Parameter ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Construction
open ArnoldCounterexample.Quadric ArnoldCounterexample.Field
open scoped ContDiff Topology NNReal
open Set Filter

lemma parameter_one : parameter 1 = epsilon := by simp [parameter]
lemma center_identity (p : ℝ × CV) : center p = p.2 + parameter p.1 • vectorField (center p) :=
  Midpoint.resolvent_eq _ lipschitz _ _ p
lemma forwardMid_center (p : ℝ × CV) : forwardMid p = center p + parameter p.1 • vectorField (center p) :=
  Midpoint.step_center _ lipschitz _ _ p
lemma center_average (p : ℝ × CV) : (2:ℝ) • center p = p.2 + forwardMid p := by
  dsimp [forwardMid, Midpoint.step, center]
  module

lemma center_zero_coordinate (p : ℝ × CV) : center p 0 = p.2 0 := by
  have h := congrFun (center_identity p) 0
  simpa only [Pi.add_apply, Pi.smul_apply, vectorField_zero_coordinate, smul_zero, add_zero] using h
lemma forwardMid_zero_coordinate (p : ℝ × CV) : forwardMid p 0 = p.2 0 := by
  rw [forwardMid_center]
  simp only [Pi.add_apply, Pi.smul_apply, vectorField_zero_coordinate, smul_zero, add_zero,
    center_zero_coordinate]

end ArnoldCounterexample.Construction

end

end OAI

-- ---- from OAI.Geometry.Arnold.FieldAlgebra ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Field
open ArnoldCounterexample.Quadric ArnoldCounterexample.ThreePoints ArnoldCounterexample.Factors
open scoped ContDiff Topology Matrix
open Set Filter

lemma casimir_unit (z : UnitQuadric) (hz : (z:CV) 0 = 0) : casimir z = 1 := by
  have h := (sphereFactors_mem z hz).1
  simpa [casimir, sphereFactors, sqNorm, Fin.sum_univ_succ, add_assoc] using h

lemma core_unit (z : UnitQuadric) (hz : (z:CV) 0 = 0) :
    core z = leftOperator 0 z - rightOperator 2 z + mixedField z - pairing z • selfField z := by
  simp only [core, casimir_unit z hz, radial_at_one.1, radial_at_one.2, one_smul]
  module

lemma left_bracket (i j : Fin 3) (z : CV) : symplectic (leftOperator i z) (leftOperator j z) =
    2 * (![![0,leftSphere z 2,-leftSphere z 1], ![-leftSphere z 2,0,leftSphere z 0],
      ![leftSphere z 1,-leftSphere z 0,0]] i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [symplectic_apply, omega, leftOperator, rotor_apply, Pi.single_apply,
      leftSphere, moment_real, Fin.sum_univ_succ, Complex.mul_im] <;> ring

lemma right_bracket (i j : Fin 3) (z : CV) : symplectic (rightOperator i z) (rightOperator j z) =
    -2 * (![![0,rightSphere z 2,-rightSphere z 1], ![-rightSphere z 2,0,rightSphere z 0],
      ![rightSphere z 1,-rightSphere z 0,0]] i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [symplectic_apply, omega, rightOperator, rotor_apply, Pi.single_apply,
      rightSphere, moment_real, Fin.sum_univ_succ, Complex.mul_im] <;> ring

lemma mixed_bracket (i j : Fin 3) (z : CV) : symplectic (leftOperator i z) (rightOperator j z) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [symplectic_apply, omega, leftOperator, rightOperator, rotor_apply, Pi.single_apply,
      Fin.sum_univ_succ, Complex.mul_im] <;> ring

lemma left_core_derivative (z : UnitQuadric) (hz : (z:CV) 0 = 0) (i : Fin 3) :
    symplectic (leftOperator i z) (core z) = 2 * ((east + rightSphere z) ⨯₃ leftSphere z) i := by
  rw [core_unit z hz]
  simp only [mixedField, selfField, map_sub, map_add, map_sum, map_smul, smul_eq_mul,
    left_bracket, mixed_bracket, mul_zero, add_zero, sub_zero]
  fin_cases i <;> simp [Fin.sum_univ_succ, crossProduct, east] <;> ring

lemma right_core_derivative (z : UnitQuadric) (hz : (z:CV) 0 = 0) (i : Fin 3) :
    symplectic (rightOperator i z) (core z) = -2 * ((leftSphere z - pole) ⨯₃ rightSphere z) i := by
  have hmix (i j : Fin 3) : symplectic (rightOperator i z) (leftOperator j z) = 0 := by
    rw [symplectic_skew, mixed_bracket, neg_zero]
  rw [core_unit z hz]
  simp only [mixedField, selfField, map_sub, map_add, map_sum, map_smul, smul_eq_mul,
    right_bracket, hmix, mul_zero, zero_add]
  fin_cases i <;> simp [Fin.sum_univ_succ, crossProduct, pole] <;> ring

lemma cross_zero_multiplier (x a : R3) (hx : sqNorm x = 1) (ha : a ⨯₃ x = 0) :
    a = (a ⬝ᵥ x) • x := by
  have h := congrArg (fun y : R3 ↦ x ⨯₃ y) ha
  rw [cross_cross_eq_smul_sub_smul', map_zero] at h
  have hxx : x ⬝ᵥ x = 1 := by simpa [dotProduct, sqNorm, Fin.sum_univ_succ, pow_two, add_assoc] using hx
  rw [hxx, one_smul] at h
  exact sub_eq_zero.mp h

lemma core_vertical_critical (z : UnitQuadric) (hz : (z:CV) 0 = 0) (a : ℝ)
    (ha : core z = a • (Complex.I • (z:CV))) : MultiplierCritical (sphereFactors z) := by
  have hσ (v : CV) (hv : (bilinear (star (z:CV)) v).re = 0) :
      symplectic v (Complex.I • (z:CV)) = 0 := by
    rw [symplectic_apply]
    have he : omega v (Complex.I • (z:CV)) = 2 * (bilinear (star (z:CV)) v).re := by
      simp only [omega, bilinear, Pi.star_apply, Pi.smul_apply, smul_eq_mul,
        Complex.im_sum, Complex.re_sum, Complex.mul_im, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he, hv, mul_zero]
  have hi (i : Fin 3) := hσ (leftOperator i z) (left_skew i (z:CV)).1
  have hj (i : Fin 3) := hσ (rightOperator i z) (right_skew i (z:CV)).1
  have hL : (east + rightSphere z) ⨯₃ leftSphere z = 0 := by
    ext i
    have h := left_core_derivative z hz i
    rw [ha, map_smul, hi, smul_zero] at h
    simpa only [Pi.zero_apply] using (mul_eq_zero.mp h.symm).resolve_left (by norm_num)
  have hR : (leftSphere z - pole) ⨯₃ rightSphere z = 0 := by
    ext i
    have h := right_core_derivative z hz i
    rw [ha, map_smul, hj, smul_zero] at h
    simpa only [Pi.zero_apply] using (mul_eq_zero.mp h.symm).resolve_left (by norm_num)
  have hmem := sphereFactors_mem z hz
  have eL := cross_zero_multiplier (leftSphere z) (east+rightSphere z) hmem.1 hL
  have eR := cross_zero_multiplier (rightSphere z) (leftSphere z-pole) hmem.2 hR
  refine ⟨hmem, (east+rightSphere z) ⬝ᵥ leftSphere z,
    (leftSphere z-pole) ⬝ᵥ rightSphere z, ?_⟩
  have eL0 := congrFun eL 0; have eL1 := congrFun eL 1; have eL2 := congrFun eL 2
  have eR0 := congrFun eR 0; have eR1 := congrFun eR 1; have eR2 := congrFun eR 2
  simpa [sphereFactors, east, pole] using And.intro eL0 (And.intro eL1 (And.intro eL2
    (And.intro eR0 (And.intro eR1 eR2))))

lemma core_complex_vertical_critical (z : UnitQuadric) (hz : (z:CV) 0 = 0) (c : ℂ)
    (hc : core z = c • (z:CV)) : MultiplierCritical (sphereFactors z) := by
  have hr := (core_skew (z:CV)).1
  rw [hc, bilinear_smul_right, bilinear_star_self, z.property.1] at hr
  simp only [Complex.ofReal_one, mul_one] at hr
  apply core_vertical_critical z hz c.im
  rw [hc]
  have he : c = (c.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hr]
  rw [he, mul_smul]
  ext i
  simp [Complex.real_smul]

end ArnoldCounterexample.Field

end

end OAI

-- ---- from OAI.Geometry.Arnold.FixedPoints ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Construction
open ArnoldCounterexample.Quadric ArnoldCounterexample.Field ArnoldCounterexample.Factors
open ArnoldCounterexample.ThreePoints
open scoped ContDiff Topology Matrix
open Set Filter

lemma fixed_lift (z : UnitQuadric) (hz : mainEquiv (project z) = project z) :
    ∃ c : ℂ, Complex.normSq c = 1 ∧ c • (z:CV) = forward (1,z) := by
  rw [mainEquiv_project] at hz
  exact (project_eq_iff_phase _ _).mp hz

lemma fixed_mid_phase (z : UnitQuadric) (hz : mainEquiv (project z) = project z) :
    ∃ d : ℂ, Complex.normSq d = 1 ∧ forwardMid (1,z) = d • (z:CV) := by
  obtain ⟨c,hc,he⟩ := fixed_lift z hz
  refine ⟨-c, by simpa using hc, ?_⟩
  ext i
  have hei := congrFun he i
  by_cases hi : i = 0
  · subst i
    simp [forwardMid_zero_coordinate, fixed_zero_coordinate z hz]
  · simp only [Pi.smul_apply, smul_eq_mul, forward, rotationPath_finish,
      involutionLinear_apply, ite_eq_right hi] at hei ⊢
    linear_combination hei

lemma fixed_factor_critical (z : UnitQuadric) (hz : mainEquiv (project z) = project z) :
    MultiplierCritical (sphereFactors z) := by
  have hz0 := fixed_zero_coordinate z hz
  obtain ⟨d,hd,hM⟩ := fixed_mid_phase z hz
  let a : ℂ := (1+d)/2
  have hcenter : center (1,z) = a • (z:CV) := by
    have hav := center_average (1,z)
    rw [hM] at hav
    ext i
    have hi := congrFun hav i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul] at hi ⊢
    norm_num at hi
    dsimp [a]
    linear_combination hi/2
  have ha : Complex.normSq a ∈ Ioo (1/2:ℝ) 2 := by
    have h := center_bound 1 z
    simpa only [hcenter, normSquared_smul, z.property.1, mul_one] using h
  have hX : vectorField (center (1,z)) = a • core z := by
    rw [vectorField, cutoff_eq_one (le_of_lt (lt_trans (center_bound 1 z).2 (by norm_num))),
      one_smul, hcenter, core_homogeneous z hz0 a ha]
  have hId := center_identity (1,z)
  rw [hX, hcenter, parameter_one] at hId
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha; linarith
  apply core_complex_vertical_critical z hz0 ((a-1)/((epsilon:ℂ)*a))
  ext i
  have hi := congrFun hId i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul] at hi ⊢
  have he0 : (epsilon:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt epsilon_pos)
  field_simp
  linear_combination -hi

end ArnoldCounterexample.Construction

namespace ArnoldCounterexample.Construction
open ArnoldCounterexample.Quadric ArnoldCounterexample.Field ArnoldCounterexample.Factors
open ArnoldCounterexample.ThreePoints
open scoped ContDiff Topology Matrix
open Set Filter

end ArnoldCounterexample.Construction

end

end OAI

-- ---- platform node ----
open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.Construction
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter
open ArnoldCounterexample.Quadric ArnoldCounterexample.Field ArnoldCounterexample.Factors
open ArnoldCounterexample.ThreePoints
open scoped ContDiff Topology Matrix
open Set Filter


theorem solution : type_of% @_root_.OAI.ArnoldCounterexample.Construction.fixed_factor_critical := @_root_.OAI.ArnoldCounterexample.Construction.fixed_factor_critical
