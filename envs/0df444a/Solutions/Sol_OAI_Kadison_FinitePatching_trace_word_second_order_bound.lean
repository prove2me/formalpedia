-- Prove2me | solution 1 for OAI.Kadison.FinitePatching.trace_word_second_order_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:13:56.734651+00:00
-- url     : https://prove2.me/submissions/28a46cba-5616-4820-95d1-546602540ca9

import Mathlib
import Definitions.Def_OAIQ039C010

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteWordTelescoping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators

namespace Kadison.FinitePatching

variable {A I : Type*} [NormedRing A]

variable [NormedAlgebra ℂ A]

lemma trace_word_difference_bound (τ : A →ₗ[ℂ] ℂ) (old new : I → A)
    (l : List I) (a : A) {B : ℝ} (_hB : 0 ≤ B)
    (h : ∀ s i t, l=s++i::t →
      ‖τ (a*wordProduct old s*new i*wordProduct (fun j => old j+new j) t)‖ ≤ B) :
    ‖τ (a*wordProduct (fun j => old j+new j) l)-τ (a*wordProduct old l)‖ ≤
      (l.length:ℝ)*B := by
  induction l generalizing a with
  | nil => simp
  | cons i l ih =>
    have hi := h [] i l rfl
    simp only [wordProduct_nil,mul_one] at hi
    have ht := ih (a*old i) (by
      intro s j t he
      have hh := h (i::s) j t (by simp only [List.cons_append,he])
      simpa only [wordProduct_cons,mul_assoc] using hh)
    have he : τ (a*wordProduct (fun j => old j+new j) (i::l))-
        τ (a*wordProduct old (i::l))=
        τ (a*new i*wordProduct (fun j => old j+new j) l)+
        (τ ((a*old i)*wordProduct (fun j => old j+new j) l)-
          τ ((a*old i)*wordProduct old l)) := by
      simp only [wordProduct_cons,←mul_assoc,add_mul,mul_add,map_add]
      ring
    rw [he]
    calc
      _ ≤ ‖τ (a*new i*wordProduct (fun j => old j+new j) l)‖+
          ‖τ ((a*old i)*wordProduct (fun j => old j+new j) l)-
            τ ((a*old i)*wordProduct old l)‖ := norm_add_le _ _
      _ ≤ B+(l.length:ℝ)*B := add_le_add hi ht
      _=_ := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring

lemma trace_word_second_order_bound_oai (τ : A →ₗ[ℂ] ℂ) (old new : I → A)
    (l : List I) {S D : ℝ} (hS : 0 ≤ S) (hD : 0 ≤ D)
    (hsingle : ∀ s i t, l=s++i::t →
      ‖τ (wordProduct old s*new i*wordProduct old t)‖ ≤ S)
    (hdouble : ∀ s i t j r, l=s++i::(t++j::r) →
      ‖τ (wordProduct old s*new i*wordProduct old t*new j*
        wordProduct (fun k => old k+new k) r)‖ ≤ D) :
    ‖τ (wordProduct (fun i => old i+new i) l)-τ (wordProduct old l)‖ ≤
      (l.length:ℝ)*S+(l.length:ℝ)^2*D := by
  have hh : ∀ s i t, l=s++i::t →
      ‖τ (wordProduct old s*new i*wordProduct (fun j => old j+new j) t)‖ ≤
        S+(l.length:ℝ)*D := by
    intro s i t he
    have ht := trace_word_difference_bound τ old new t (wordProduct old s*new i) hD (by
      intro u j r ht
      exact hdouble s i u j r (by rw [he,ht]))
    have hlen : (t.length:ℝ) ≤ (l.length:ℝ) := by
      apply Nat.cast_le.mpr
      rw [he,List.length_append,List.length_cons]
      omega
    calc
      _ ≤ ‖τ (wordProduct old s*new i*wordProduct old t)‖+
          ‖τ (wordProduct old s*new i*wordProduct (fun j => old j+new j) t)-
            τ (wordProduct old s*new i*wordProduct old t)‖ := by
        simpa only [norm_sub_rev] using norm_le_insert
          (τ (wordProduct old s*new i*wordProduct old t))
          (τ (wordProduct old s*new i*wordProduct (fun j => old j+new j) t))
      _ ≤ S+(t.length:ℝ)*D := add_le_add (hsingle s i t he) ht
      _ ≤ S+(l.length:ℝ)*D := add_le_add le_rfl (mul_le_mul_of_nonneg_right hlen hD)
  have h := trace_word_difference_bound τ old new l 1
    (show 0 ≤ S+(l.length:ℝ)*D by positivity) (by
      intro s i t he
      simpa only [one_mul] using hh s i t he)
  simpa only [one_mul,mul_add,←mul_assoc,←pow_two] using h

end Kadison.FinitePatching

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.FinitePatching.trace_word_second_order_bound_oai.{u_1, u_2} := @OAI.Kadison.FinitePatching.trace_word_second_order_bound_oai.{u_1, u_2}
