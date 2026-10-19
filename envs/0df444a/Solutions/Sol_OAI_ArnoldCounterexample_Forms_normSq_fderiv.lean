-- Prove2me | solution 1 for OAI.ArnoldCounterexample.Forms.normSq_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:57:31.233084+00:00
-- url     : https://prove2.me/submissions/f02ec5f5-d962-4fb0-8a24-f436fe339395

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Symplectic.lean:L86-L108
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.Forms.normSq_fderiv. The node keeps its source
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

-- ---- from OAI.Geometry.Arnold.Symplectic ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator

open scoped BigOperators ContDiff

namespace ArnoldCounterexample.Forms

lemma symplectic_apply (n : ℕ) (u v : CSpace n) :
    symplectic n u v = 2 * ∑ i, ((u i).re * (v i).im - (u i).im * (v i).re) := by
  simp [symplectic, _root_.sum_apply, ContinuousLinearMap.bilinearComp_apply]

lemma symplectic_I_left (n : ℕ) (z v : CSpace n) :
    symplectic n (Complex.I • z) v =
      -2 * ∑ i, ((z i).re * (v i).re + (z i).im * (v i).im) := by
  rw [symplectic_apply]
  have h (i : Fin n) :
      ((Complex.I • z) i).re * (v i).im - ((Complex.I • z) i).im * (v i).re =
        -((z i).re * (v i).re + (z i).im * (v i).im) := by
    simp only [Pi.smul_apply, smul_eq_mul, Complex.I_mul_re, Complex.I_mul_im]
    ring
  simp_rw [h]
  rw [Finset.sum_neg_distrib]
  ring

/-- The radial derivative identity making the curvature basic on unit spheres. -/
lemma normSq_fderiv (n : ℕ) (z v : CSpace n) :
    fderiv ℝ (normSq n) z v = -symplectic n (Complex.I • z) v := by
  have hderiv : HasFDerivAt (normSq n)
      (∑ i : Fin n, ((2 * (z i).re) • reCoord n i + (2 * (z i).im) • imCoord n i)) z := by
    convert! HasFDerivAt.sum (u := Finset.univ) (fun i _ ↦
      (((reCoord n i).hasFDerivAt.mul (reCoord n i).hasFDerivAt).add
        ((imCoord n i).hasFDerivAt.mul (imCoord n i).hasFDerivAt))) using 1
    · funext x
      simp [normSq, Complex.normSq_apply]
    · ext w
      simp only [_root_.sum_apply, _root_.add_apply,
        _root_.smul_apply, reCoord_apply, imCoord_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
  rw [hderiv.fderiv, symplectic_I_left]
  simp only [_root_.sum_apply, _root_.add_apply,
    _root_.smul_apply, reCoord_apply, imCoord_apply, smul_eq_mul]
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end ArnoldCounterexample.Forms

end

end OAI

-- ---- platform node ----
open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.Forms
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped BigOperators ContDiff


theorem solution : type_of% @_root_.OAI.ArnoldCounterexample.Forms.normSq_fderiv := @_root_.OAI.ArnoldCounterexample.Forms.normSq_fderiv
