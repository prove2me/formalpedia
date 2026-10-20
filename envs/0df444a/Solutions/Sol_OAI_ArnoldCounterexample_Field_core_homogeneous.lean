-- Prove2me | solution 1 for OAI.ArnoldCounterexample.Field.core_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:14:14.573235+00:00
-- url     : https://prove2.me/submissions/10921f74-30f7-4081-a7ac-a635ffda4733

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/FieldAlgebra.lean:L41-L54
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.Field.core_homogeneous. The node keeps its source
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

lemma pairing_scale (c : ℂ) (z : CV) : pairing (c • z) = Complex.normSq c ^ 2 * pairing z := by
  simp only [pairing, left_scale, right_scale, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma casimir_scale (c : ℂ) (z : CV) : casimir (c • z) = Complex.normSq c ^ 2 * casimir z := by
  simp only [casimir, left_scale, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

lemma mixed_scale (c : ℂ) (z : CV) : mixedField (c • z) = Complex.normSq c • (c • mixedField z) := by
  simp only [mixedField, left_scale, right_scale, Pi.smul_apply, smul_eq_mul, left_phase, right_phase,
    Finset.smul_sum, smul_add, smul_comm c, smul_smul]

lemma self_scale (c : ℂ) (z : CV) : selfField (c • z) = Complex.normSq c • (c • selfField z) := by
  simp only [selfField, left_scale, Pi.smul_apply, smul_eq_mul, left_phase,
    Finset.smul_sum, smul_comm c, smul_smul]

lemma core_unit (z : UnitQuadric) (hz : (z:CV) 0 = 0) :
    core z = leftOperator 0 z - rightOperator 2 z + mixedField z - pairing z • selfField z := by
  simp only [core, casimir_unit z hz, radial_at_one.1, radial_at_one.2, one_smul]
  module

lemma core_homogeneous (z : UnitQuadric) (hz : (z:CV) 0 = 0) (c : ℂ)
    (hc : Complex.normSq c ∈ Ioo (1/2:ℝ) 2) : core (c • (z:CV)) = c • core z := by
  let r := Complex.normSq c
  have hr : r ≠ 0 := ne_of_gt (lt_trans (by norm_num) hc.1)
  have he : 2 * (-(2*r^3)⁻¹) * (r^2 * pairing z) * r = -pairing z := by
    field_simp
  rw [core, casimir_scale, casimir_unit z hz, mul_one,
    (radial_squared r hc).1, (radial_squared r hc).2, pairing_scale, mixed_scale, self_scale,
    core_unit z hz]
  simp only [left_phase, right_phase, smul_add, smul_sub, smul_smul, ← smul_comm c]
  change c • leftOperator 0 z - c • rightOperator 2 z + c • ((r⁻¹*r) • mixedField z) +
    c • ((2 * (-(2*r^3)⁻¹) * (r^2 * pairing z) * r) • selfField z) = _
  rw [inv_mul_cancel₀ hr, one_smul, he, neg_smul]
  module

end ArnoldCounterexample.Field

end

end OAI

-- ---- platform node ----
open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.Field
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter
open ArnoldCounterexample.Quadric ArnoldCounterexample.ThreePoints ArnoldCounterexample.Factors
open scoped ContDiff Topology Matrix
open Set Filter


theorem solution : type_of% @_root_.OAI.ArnoldCounterexample.Field.core_homogeneous := @_root_.OAI.ArnoldCounterexample.Field.core_homogeneous
