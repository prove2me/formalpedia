-- Prove2me | solution 1 for GlobalTheory.normSq_place_form_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:25:46.929128+00:00
-- url     : https://prove2.me/submissions/98407a04-ff3b-43e2-973f-6334d41f2d30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
import Theorems.Thm_GlobalTheory_pairingMatrix_apply
import Theorems.Thm_GlobalTheory_formPairMatrix_apply
import Theorems.Thm_GlobalTheory_innerFormLeft_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.pairingMatrix_apply
attribute [local simp] GlobalTheory.formPairMatrix_apply
attribute [local simp] GlobalTheory.innerFormLeft_apply

set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
variable {R M T : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
namespace GlobalTheory
theorem _root_.solution (h : M →ₗ[R] M →ₗ⋆[R] R) (hh : ∀ u v, h u v = star (h v u))
    (τ : R →+* ℂ) (hτ : ∀ x, τ (star x) = starRingEnd ℂ (τ x))
    (hpos : ∀ v, 0 ≤ (τ (h v v)).re) (u v : M) :
    ‖τ (h u v)‖ ^ 2 ≤ (τ (h u u)).re * (τ (h v v)).re := by
  have him : ∀ w, (τ (h w w)).im = 0 := fun w => by
    have := congrArg Complex.im (hτ (h w w))
    rw [← hh, Complex.conj_im] at this
    linarith
  have hvu : τ (h v u) = starRingEnd ℂ (τ (h u v)) := by rw [hh v u, hτ]
  have expand : ∀ x y : R, τ (h (x • u + y • v) (x • u + y • v))
      = τ x * starRingEnd ℂ (τ x) * τ (h u u) + τ x * starRingEnd ℂ (τ y) * τ (h u v)
        + τ y * starRingEnd ℂ (τ x) * starRingEnd ℂ (τ (h u v))
        + τ y * starRingEnd ℂ (τ y) * τ (h v v) := by
    intro x y
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, starRingEnd_apply, hτ, hvu]
    ring
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  set a := (τ (h u u)).re with ha
  set c := (τ (h v v)).re with hc
  set b₁ := (τ (h u v)).re with hb₁
  set b₂ := (τ (h u v)).im with hb₂
  have ha0 : 0 ≤ a := hpos u
  have hc0 : 0 ≤ c := hpos v
  rcases hc0.eq_or_lt with hc1 | hc1
  · have hn : ∀ n : ℕ, 2 * n * (b₁ * b₁ + b₂ * b₂) ≤ a := by
      intro n
      have := hpos ((1 : R) • u + (-((n : R) * h u v)) • v)
      rw [expand] at this
      simp only [map_one, map_neg, map_mul, map_natCast, Complex.add_re, Complex.mul_re,
        Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im,
        Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im, him, ← ha, ← hc, ← hb₁,
        ← hb₂, ← hc1] at this
      nlinarith
    rw [← hc1, mul_zero]
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn'⟩ := exists_nat_gt (a / (b₁ * b₁ + b₂ * b₂))
    rw [div_lt_iff₀ hlt] at hn'
    have := hn n
    nlinarith
  · have := hpos (h v v • u + (-(h u v)) • v)
    rw [expand] at this
    simp only [map_neg, Complex.add_re, Complex.mul_re,
      Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, him, ← ha, ← hc, ← hb₁, ← hb₂] at this
    have h2 : 0 ≤ c * (a * c - (b₁ * b₁ + b₂ * b₂)) := by nlinarith
    have h3 := (mul_nonneg_iff_of_pos_left hc1).1 h2
    linarith
end GlobalTheory
