-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.eval_div_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:11:39.024981+00:00
-- url     : https://prove2.me/submissions/d0aff5ed-9e80-4d64-b770-3a31de6dd004

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJLaurentIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Polynomial
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution (P Q : ℂ[X]) {x : ℂ} (hx : Q.eval x ≠ 0) :
    (algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) Q).eval (RingHom.id ℂ) x =
      P.eval x / Q.eval x := by
  have hQ : Q ≠ 0 := by
    rintro rfl
    simp at hx
  set y := algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) Q with hydef
  have hy : (y.denom).eval₂ (RingHom.id ℂ) x ≠ 0 := by
    intro h0
    apply hx
    have := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id ℂ) x
      (RatFunc.denom_div_dvd P Q) h0
    simpa [Polynomial.eval₂_id] using this
  have hQd : ((algebraMap ℂ[X] (RatFunc ℂ) Q).denom).eval₂ (RingHom.id ℂ) x ≠ 0 := by
    rw [RatFunc.denom_algebraMap]
    simp
  have hmul := RatFunc.eval_mul (RingHom.id ℂ) x hy hQd
  have hyQ : y * algebraMap ℂ[X] (RatFunc ℂ) Q = algebraMap ℂ[X] (RatFunc ℂ) P :=
    div_mul_cancel₀ _ (RatFunc.algebraMap_ne_zero hQ)
  rw [hyQ, RatFunc.eval_algebraMap, RatFunc.eval_algebraMap] at hmul
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Polynomial.eval₂_id] at hmul
  rw [eq_div_iff hx, ← hmul]
end GroundTheory.Automorphic.GodementJacquet
