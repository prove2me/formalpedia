-- Prove2me | solution 1 for OAI.ArnoldCounterexample.Construction.fixed_zero_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:16:51.131223+00:00
-- url     : https://prove2.me/submissions/b7a8dd6f-67c2-41a7-acc1-ade03a08ebcf

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/FixedPoints.lean:L24-L46
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.Construction.fixed_zero_coordinate. The node keeps its source
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

lemma fixed_zero_coordinate (z : UnitQuadric) (hz : mainEquiv (project z) = project z) :
    (z:CV) 0 = 0 := by
  by_contra hzero
  obtain ⟨c,hc,he⟩ := fixed_lift z hz
  have he0 := congrFun he 0
  simp only [Pi.smul_apply, smul_eq_mul, forward, rotationPath_finish,
    involutionLinear_apply, forwardMid_zero_coordinate] at he0
  have hc1 : c = 1 := (mul_right_cancel₀ hzero (he0.trans (one_mul _).symm))
  rw [hc1, one_smul] at he
  have hrest (i : Fin 5) (hi : i ≠ 0) : center (1,z) i = 0 := by
    have hei := congrFun he i
    simp only [forward, rotationPath_finish, involutionLinear_apply, ite_eq_right hi] at hei
    have hav := congrFun (center_average (1,z)) i
    simp only [Pi.smul_apply, Pi.add_apply, Complex.real_smul] at hav
    rw [hei, neg_add_cancel] at hav
    exact (mul_eq_zero.mp hav).resolve_left (by norm_num)
  have hX : vectorField (center (1,z)) = 0 := vectorField_zero_rest _ hrest
  have hcenter : center (1,z) = (z:CV) := by simpa only [hX, smul_zero, add_zero] using center_identity (1,z)
  have hzrest (i : Fin 5) (hi : i ≠ 0) : (z:CV) i = 0 := by rw [← hcenter]; exact hrest i hi
  have hp := z.property.2
  simp only [quadricPolynomial, Fin.sum_univ_succ] at hp
  simp [hzrest] at hp
  exact hzero hp

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


theorem solution : type_of% @_root_.OAI.ArnoldCounterexample.Construction.fixed_zero_coordinate := @_root_.OAI.ArnoldCounterexample.Construction.fixed_zero_coordinate
