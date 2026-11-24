-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.eq_of_eval_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:21:54.756452+00:00
-- url     : https://prove2.me/submissions/08aa8626-cb54-4c5c-9709-1179b906f782

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
theorem _root_.solution {R₁ R₂ : RatFunc ℂ} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x : ℂ, x ≠ 0 → ‖x‖ < ε → R₁.eval (RingHom.id ℂ) x = R₂.eval (RingHom.id ℂ) x) :
    R₁ = R₂ := by
  set Q : ℂ[X] := R₁.num * R₂.denom - R₂.num * R₁.denom with hQdef
  have hT : {x : ℂ | x ≠ 0 ∧ ‖x‖ < ε}.Infinite := by
    refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((ε / ((k : ℝ) + 2) : ℝ) : ℂ))
      ?_ ?_
    · intro a b hab
      have ha : (0 : ℝ) < (a : ℝ) + 2 := by positivity
      have hb : (0 : ℝ) < (b : ℝ) + 2 := by positivity
      have h1 : ε / ((a : ℝ) + 2) = ε / ((b : ℝ) + 2) := Complex.ofReal_injective hab
      rw [div_eq_div_iff ha.ne' hb.ne'] at h1
      have h2 : (b : ℝ) + 2 = (a : ℝ) + 2 := mul_left_cancel₀ hε.ne' h1
      have h3 : (a : ℝ) = b := by linarith
      exact_mod_cast h3
    · intro k
      have hk : 0 < ε / ((k : ℝ) + 2) := by positivity
      refine ⟨Complex.ofReal_ne_zero.2 hk.ne', ?_⟩
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
      exact div_lt_self hε (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
  have hroots : ({x | IsRoot R₁.denom x} ∪ {x | IsRoot R₂.denom x}).Finite :=
    (Polynomial.finite_setOfPred_isRoot (RatFunc.denom_ne_zero _)).union
      (Polynomial.finite_setOfPred_isRoot (RatFunc.denom_ne_zero _))
  have hQ : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine (hT.sdiff hroots).mono ?_
    rintro x ⟨⟨hx0, hxε⟩, hxr⟩
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, Polynomial.IsRoot.def] at hxr
    have h1 := h x hx0 hxε
    simp only [RatFunc.eval, Polynomial.eval₂_id] at h1
    rw [div_eq_div_iff hxr.1 hxr.2] at h1
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, hQdef, Polynomial.eval_sub,
      Polynomial.eval_mul, h1, sub_self]
  rw [← RatFunc.num_div_denom R₁, ← RatFunc.num_div_denom R₂,
    div_eq_div_iff (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero _))
      (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero _)), ← map_mul, ← map_mul]
  congr 1
  exact sub_eq_zero.1 hQ
end GroundTheory.Automorphic.GodementJacquet
