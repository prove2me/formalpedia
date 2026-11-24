-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermitianForm.re_pairing_eq_zero_of_psd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:38:12.388324+00:00
-- url     : https://prove2.me/submissions/a4cefd51-2010-4c1a-9ee2-6a2e302be67e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianPsdIsotropicRadical

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermitianForm
namespace GlobalTheory.CompanionTheory.HermitianForm
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : ∀ v w, B w v = starRingEnd ℂ (B v w))
    (hpos : ∀ v, 0 ≤ (B v v).re) (v : V) (hv : B v v = 0) (u : V) : (B v u).re = 0 := by
  have hb : 0 ≤ (B u u).re := hpos u
  have key : ∀ t : ℝ, 0 ≤ 2 * t * (B v u).re + t ^ 2 * (B u u).re := by
    intro t
    have h := hpos (v + (t : ℂ) • u)
    have e : B (v + (t : ℂ) • u) (v + (t : ℂ) • u)
        = B v v + (t : ℂ) * B v u + (t : ℂ) * B u v + (t : ℂ) * (t : ℂ) * B u u := by
      simp only [map_add, LinearMap.add_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, Complex.conj_ofReal]
      ring
    rw [e, hv, hB v u] at h
    simp only [zero_add, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.mul_im, zero_mul, sub_zero, add_zero] at h
    nlinarith [h]
  set a := (B v u).re with ha
  set b := (B u u).re with hb'
  have hb1 : 0 < b + 1 := by linarith
  have h := key (-a / (b + 1))
  have e2 : 2 * (-a / (b + 1)) * a + (-a / (b + 1)) ^ 2 * b
      = -(a ^ 2 * (b + 2)) / (b + 1) ^ 2 := by
    field_simp
    ring
  rw [e2] at h
  have h3 : 0 ≤ -(a ^ 2 * (b + 2)) := by
    by_contra hc
    push Not at hc
    have : -(a ^ 2 * (b + 2)) / (b + 1) ^ 2 < 0 := div_neg_of_neg_of_pos hc (by positivity)
    linarith
  have h4 : a ^ 2 * (b + 2) ≤ 0 := by linarith
  have h5 : a ^ 2 ≤ 0 := by
    by_contra hc
    push Not at hc
    have : 0 < a ^ 2 * (b + 2) := mul_pos hc (by linarith)
    linarith
  have h6 : a ^ 2 = 0 := le_antisymm h5 (sq_nonneg a)
  exact pow_eq_zero_iff (two_ne_zero) |>.mp h6
end GlobalTheory.CompanionTheory.HermitianForm
