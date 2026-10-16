-- Prove2me | solution 1 for OAI.ComplexCancellation.BezoutFrame.exists_frame
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:04:09.775754+00:00
-- url     : https://prove2.me/submissions/56d55d09-c5cd-4f45-b039-4036fbb49d63

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/BezoutFrame.lean:L9-L44
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.BezoutFrame.exists_frame. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity
import Definitions.Def_OAI_Algebra_AffineCancellation_Quadric
import Definitions.Def_OAI_Algebra_AffineCancellation_Degeneration
import Definitions.Def_OAI_Algebra_AffineCancellation_Rees
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesReduction
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DegenerationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveInvariant
import Definitions.Def_OAI_Algebra_AffineCancellation_RelativeClearing

-- ---- from OAI.Algebra.AffineCancellation.BezoutFrame ----
namespace OAI

noncomputable section

namespace ComplexCancellation.BezoutFrame

/-- Principalization of an SL₂/diagonal-torus point over a Euclidean domain.
This supplies the invariant-localization frame over the slice polynomial ring. -/
theorem exists_frame {R : Type*} [EuclideanDomain R] (x y z : R)
    (h : x*y = z*(z+1)) :
    ∃ a d b c : R, a*b = x ∧ d*c = y ∧ d*b = z ∧ a*c-d*b = 1 := by
  classical
  let g := EuclideanDomain.gcd x z
  by_cases hg : g = 0
  · have hxz : x = 0 ∧ z = 0 := EuclideanDomain.gcd_eq_zero_iff.mp hg
    exact ⟨1, y, 0, 1, by simp [hxz.1], by simp, by simp [hxz.2], by simp⟩
  · obtain ⟨a, ha⟩ := EuclideanDomain.gcd_dvd_left x z
    obtain ⟨d, hd⟩ := EuclideanDomain.gcd_dvd_right x z
    change x = g*a at ha
    change z = g*d at hd
    let r := EuclideanDomain.gcdA x z
    let s := EuclideanDomain.gcdB x z
    have hbez : a*r+d*s=1 := by
      apply mul_left_cancel₀ hg
      calc g * (a*r+d*s) = x*r+z*s := by rw [ha, hd]; ring
        _ = g := (EuclideanDomain.gcd_eq_gcd_ab x z).symm
        _ = g*1 := (mul_one g).symm
    have hrel : a*y=d*(z+1) := by
      apply mul_left_cancel₀ hg
      calc g*(a*y) = x*y := by rw [ha]; ring
        _ = z*(z+1) := h
        _ = g*(d*(z+1)) := by rw [hd]; ring
    refine ⟨a,d,g,r*(z+1)+s*y, ?_, ?_, ?_, ?_⟩
    · rw [mul_comm, ← ha]
    · calc d*(r*(z+1)+s*y) = r*(d*(z+1))+d*s*y := by ring
        _ = r*(a*y)+d*s*y := by rw [hrel]
        _ = (a*r+d*s)*y := by ring
        _ = y := by rw [hbez, one_mul]
    · rw [mul_comm, ← hd]
    · calc a*(r*(z+1)+s*y)-d*g = a*r*(z+1)+s*(a*y)-z := by rw [hd]; ring
        _ = (a*r+d*s)*(z+1)-z := by rw [hrel]; ring
        _ = 1 := by rw [hbez]; ring

end ComplexCancellation.BezoutFrame

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.BezoutFrame


theorem solution : type_of% @_root_.OAI.ComplexCancellation.BezoutFrame.exists_frame := @_root_.OAI.ComplexCancellation.BezoutFrame.exists_frame
