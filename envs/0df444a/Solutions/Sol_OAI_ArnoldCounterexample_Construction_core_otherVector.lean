-- Prove2me | solution 1 for OAI.ArnoldCounterexample.Construction.core_otherVector
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:26:06.956333+00:00
-- url     : https://prove2.me/submissions/35c5bae3-0fc7-4818-8364-ef0037625cb0

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/CriticalLifts.lean:L67-L81
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.Construction.core_otherVector. The node keeps its source
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
import Definitions.Def_OAI_Geometry_Arnold_CriticalLifts

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

lemma core_unit (z : UnitQuadric) (hz : (z:CV) 0 = 0) :
    core z = leftOperator 0 z - rightOperator 2 z + mixedField z - pairing z • selfField z := by
  simp only [core, casimir_unit z hz, radial_at_one.1, radial_at_one.2, one_smul]
  module

end ArnoldCounterexample.Field

end

end OAI

-- ---- from OAI.Geometry.Arnold.CriticalLifts ----
namespace OAI

universe uα

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Construction
open ArnoldCounterexample.Quadric ArnoldCounterexample.Field ArnoldCounterexample.Factors
open ArnoldCounterexample.ThreePoints
open scoped ContDiff Topology Matrix
open Set Filter

lemma vec_five_two {α : Type uα} (a b c d e : α) : (![a,b,c,d,e] : Fin 5 → α) 2 = c := rfl
lemma vec_five_three {α : Type uα} (a b c d e : α) : (![a,b,c,d,e] : Fin 5 → α) 3 = d := rfl
lemma vec_five_four {α : Type uα} (a b c d e : α) : (![a,b,c,d,e] : Fin 5 → α) 4 = e := rfl

lemma otherVector_factors (r : ℝ) (_hr : r^2 = 3) :
    sphereFactors (otherVector r) = (![r/2,0,-1/2], ![1/2,0,-r/2]) := by
  apply Prod.ext <;> ext i <;> fin_cases i <;>
    norm_num [vec_five_two, vec_five_three, vec_five_four, Matrix.cons_val_two, Fin.ext_iff, sphereFactors, leftSphere, rightSphere, moment_real, otherVector] <;> nlinarith

lemma core_otherVector (r : ℝ) (hr : r^2 = 3) :
    core (otherVector r) = (-(3*r/2)) • (Complex.I • otherVector r) := by
  let z : UnitQuadric := ⟨otherVector r, otherVector_unit r hr⟩
  have he := core_unit z (by rfl)
  change core (otherVector r) = _ at he
  rw [he]
  have hL : leftSphere (otherVector r) = ![r/2,0,-1/2] := congrArg Prod.fst (otherVector_factors r hr)
  have hR : rightSphere (otherVector r) = ![1/2,0,-r/2] := congrArg Prod.snd (otherVector_factors r hr)
  change leftOperator 0 (otherVector r) - rightOperator 2 (otherVector r) + mixedField (otherVector r) - pairing (otherVector r) • selfField (otherVector r) = _
  simp only [mixedField, pairing, selfField, hL, hR]
  ext i
  fin_cases i <;> apply Complex.ext <;>
    norm_num [vec_five_two, vec_five_three, vec_five_four, Matrix.cons_val_two, Fin.ext_iff, leftOperator, rightOperator,
      rotor_apply, otherVector, Fin.sum_univ_succ, Pi.single_apply, Complex.real_smul,
      Complex.mul_re, Complex.mul_im] <;> nlinarith [hr, congrArg (fun s : ℝ ↦ r*s) hr]

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


theorem solution : type_of% @_root_.OAI.ArnoldCounterexample.Construction.core_otherVector := @_root_.OAI.ArnoldCounterexample.Construction.core_otherVector
