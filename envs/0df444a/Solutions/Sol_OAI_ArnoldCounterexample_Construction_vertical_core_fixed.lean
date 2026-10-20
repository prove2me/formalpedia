-- Prove2me | solution 1 for OAI.ArnoldCounterexample.Construction.vertical_core_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:23:18.143581+00:00
-- url     : https://prove2.me/submissions/e5ed3c74-f643-4da9-8282-6c9cb1385690

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/FixedPoints.lean:L106-L169
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.Construction.vertical_core_fixed. The node keeps its source
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
import Theorems.Thm_OAI_ArnoldCounterexample_Field_core_homogeneous

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
end ArnoldCounterexample.Construction

end

end OAI

-- ---- from OAI.Geometry.Arnold.FixedPoints ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

end ArnoldCounterexample.Construction

namespace ArnoldCounterexample.Construction
open ArnoldCounterexample.Quadric ArnoldCounterexample.Field ArnoldCounterexample.Factors
open ArnoldCounterexample.ThreePoints
open scoped ContDiff Topology Matrix
open Set Filter

lemma epsilon_le : epsilon ≤ 1/100 := by
  have hc := constant.coe_nonneg
  unfold epsilon
  rw [div_le_div_iff₀ (by positivity : 0 < 100*((constant:ℝ)+1)) (by norm_num : (0:ℝ)<100)]
  nlinarith

lemma vertical_core_fixed (z : UnitQuadric) (hz0 : (z:CV) 0 = 0) (b : ℝ)
    (hb : |b| ≤ 3) (hcore : core z = b • (Complex.I • (z:CV))) :
    mainEquiv (project z) = project z := by
  let s : ℝ := epsilon*b
  have hs : |s| ≤ 3/100 := by
    dsimp [s]
    rw [abs_mul, abs_of_pos epsilon_pos]
    nlinarith [mul_le_mul epsilon_le hb (abs_nonneg b) (by norm_num : (0:ℝ)≤1/100)]
  have hsq : s^2 < 1 := by
    have := abs_le.mp hs
    nlinarith [this.1,this.2]
  let a : ℂ := (1-(s:ℂ)*Complex.I)⁻¹
  have hden : (1-(s:ℂ)*Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hna : Complex.normSq a = (1+s^2)⁻¹ := by
    simp [a, Complex.normSq_apply, pow_two]
  have ha : Complex.normSq a ∈ Ioo (1/2:ℝ) 2 := by
    rw [hna]
    constructor
    · have h := (inv_lt_inv₀ (by norm_num : (0:ℝ)<2) (by positivity : (0:ℝ)<1+s^2)).mpr (by linarith : 1+s^2 < 2)
      norm_num at h ⊢
      exact h
    · have := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg s] : (1:ℝ)≤1+s^2)
      linarith
  have hn : normSquared (a • (z:CV)) < 4 := by
    rw [normSquared_smul, z.property.1, mul_one]
    linarith [ha.2]
  have hX : vectorField (a • (z:CV)) = a • core z := by
    rw [vectorField, cutoff_eq_one hn.le, one_smul, core_homogeneous z hz0 a ha]
  have haeq : a = 1 + (s:ℂ)*Complex.I*a := by
    dsimp [a]
    field_simp
    ring
  have hcenter : center (1,z) = a • (z:CV) := by
    symm
    apply Midpoint.resolvent_unique _ lipschitz _ parameter_contract
    rw [hX, hcore, parameter_one]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
    have hi := congrArg (fun c : ℂ ↦ c * (z:CV) i) haeq
    dsimp [s] at hi
    rw [Complex.ofReal_mul] at hi
    linear_combination hi
  have hM : forwardMid (1,z) = (2*a-1) • (z:CV) := by
    change (2:ℝ) • center (1,z) - (z:CV) = _
    rw [hcenter]
    ext i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.real_smul]
    norm_num
    ring
  have hF : forward (1,z) = (-(2*a-1)) • (z:CV) := by
    rw [forward, rotationPath_finish, hM]
    ext i
    by_cases hi : i = 0
    · subst i; simp [hz0]
    · simp [involutionLinear_apply, hi]
      ring
  have hphase : Complex.normSq (-(2*a-1)) = 1 := by
    have hn := (forward_preserves 1 z).1
    rwa [hF, normSquared_smul, z.property.1, mul_one] at hn
  rw [mainEquiv_project]
  exact (project_eq_iff_phase _ _).mpr ⟨_,hphase,hF.symm⟩

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


theorem solution : type_of% @_root_.OAI.ArnoldCounterexample.Construction.vertical_core_fixed := @_root_.OAI.ArnoldCounterexample.Construction.vertical_core_fixed
