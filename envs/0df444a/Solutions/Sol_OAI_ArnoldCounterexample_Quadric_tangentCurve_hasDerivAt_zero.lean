-- Prove2me | solution 1 for OAI.ArnoldCounterexample.Quadric.tangentCurve_hasDerivAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:47:11.663778+00:00
-- url     : https://prove2.me/submissions/026fbe6c-c7bf-4a6b-be30-06af7f9b57e9

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Tangent.lean:L106-L121
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.Quadric.tangentCurve_hasDerivAt_zero. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent

-- ---- from OAI.Geometry.Arnold.Tangent ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff

namespace ArnoldCounterexample.Quadric

lemma normSquared_hasFDerivAt (z : CV) :
    HasFDerivAt normSquared (normSquaredDiff z) z := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun (j : Fin 5) _ ↦
    ((realCoord j).hasFDerivAt (x := z) |>.pow 2).add
      ((imagCoord j).hasFDerivAt (x := z) |>.pow 2))
  convert! h using 1
  · ext y
    simp [normSquared, Complex.normSq_apply, pow_two]
  · simp [normSquaredDiff, two_mul]

lemma normSquaredDiff_apply (z v : CV) :
    normSquaredDiff z v = 2 * (bilinear (star z) v).re := by
  have hs : (bilinear (star z) v).re = ∑ j, (star (z j) * v j).re := by
    simpa only [bilinear, Pi.star_apply, Complex.coe_reAddGroupHom] using
      (map_sum Complex.reAddGroupHom (fun j : Fin 5 ↦ star (z j) * v j) Finset.univ)
  rw [hs]
  simp only [normSquaredDiff, sum_apply, add_apply,
    smul_apply, realCoord_apply, imagCoord_apply, smul_eq_mul,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma rawTangentCurve_hasDerivAt_zero (z v : CV) :
    HasDerivAt (rawTangentCurve z v) v 0 := by
  have h := ((hasDerivAt_const (0 : ℝ) z).add ((hasDerivAt_id 0).smul_const v)).sub
    (((hasDerivAt_id (0 : ℝ)).pow 2 |>.div_const 2).smul_const
      (quadricPolynomial v • star z))
  convert! h using 1
  simp

/-- Every declared horizontal tangent is realized by an actual differentiable
curve in the literal unit isotropic cone. -/
theorem tangentCurve_hasDerivAt_zero (z : UnitQuadric) (v : CV) (hv : Horizontal z v) :
    HasDerivAt (fun t ↦ (tangentCurve z v hv t : CV)) v 0 := by
  have hr := rawTangentCurve_hasDerivAt_zero z v
  have hn : HasDerivAt (fun t ↦ normSquared (rawTangentCurve z v t)) 0 0 := by
    have hn' := (normSquared_hasFDerivAt (rawTangentCurve z v 0)).comp_hasDerivAt 0 hr
    simpa only [rawTangentCurve_zero, normSquaredDiff_apply, show bilinear (star (z : CV)) v = 0 from hv.1,
      Complex.zero_re, mul_zero, Function.comp_def] using hn'
  have hnzero : normSquared (rawTangentCurve z v 0) = 1 := by
    rw [rawTangentCurve_zero, z.property.1]
  have hs := hn.sqrt (by rw [hnzero]; norm_num)
  have hi := hs.inv (by rw [hnzero]; norm_num)
  have h := hi.smul hr
  convert! h using 1
  simp [z.property.1]

end ArnoldCounterexample.Quadric

namespace ArnoldCounterexample.Quadric

end ArnoldCounterexample.Quadric

end

end OAI

-- ---- platform node ----
open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.Quadric
open scoped BigOperators ContDiff


theorem solution : type_of% @_root_.OAI.ArnoldCounterexample.Quadric.tangentCurve_hasDerivAt_zero := @_root_.OAI.ArnoldCounterexample.Quadric.tangentCurve_hasDerivAt_zero
