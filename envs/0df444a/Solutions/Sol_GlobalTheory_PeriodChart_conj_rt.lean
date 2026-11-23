-- Prove2me | solution 1 for GlobalTheory.PeriodChart.conj_rt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:51.00363+00:00
-- url     : https://prove2.me/submissions/4918c886-7ef9-4adc-8819-8a2e5bc81232

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}
variable {D : Datum H} {ty : Fin g → (E →+* ℂ)}
namespace GlobalTheory.PeriodChart
theorem _root_.solution (H : Host E) (τ : E →+* ℂ) :
    (τ (H.rt : E) = H.rt0 ↔ ¬ ComplexEmbedding.conjugate τ (H.rt : E) = H.rt0) := by
  have hd : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
  have hw : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    have e := congrArg (τ.comp (algebraMap (𝓞 E) E)) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at e
    exact e
  have hre : H.rt0.re = 0 := by
    have e1 := congrArg Complex.re H.sqrt_neg_disc_sq
    have e2 := congrArg Complex.im H.sqrt_neg_disc_sq
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.natCast_re, Complex.natCast_im, neg_zero] at e1 e2
    have hri : H.rt0.re * H.rt0.im = 0 := by linarith
    rcases mul_eq_zero.1 hri with h | h
    · exact h
    · exfalso
      rw [h] at e1
      nlinarith [sq_nonneg H.rt0.re]
  have hconj : (starRingEnd ℂ) H.rt0 = -H.rt0 := by
    apply Complex.ext <;> simp [hre]
  have hne : H.rt0 ≠ -H.rt0 := by
    intro h
    have h0 : H.rt0 = 0 := by linear_combination h / 2
    have e := H.sqrt_neg_disc_sq
    rw [h0] at e
    have hd0 : (H.d : ℂ) = 0 := by linear_combination e
    exact H.d_prime.ne_zero (by exact_mod_cast hd0)
  have hroots : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
    have e : (τ (H.rt : E) - H.rt0) * (τ (H.rt : E) + H.rt0) = 0 := by
      linear_combination hw - H.sqrt_neg_disc_sq
    rcases mul_eq_zero.1 e with h | h
    · left; linear_combination h
    · right; linear_combination h
  rw [ComplexEmbedding.conjugate_coe_eq]
  rcases hroots with h | h <;> rw [h]
  · rw [hconj]
    exact ⟨fun _ h' => hne h'.symm, fun _ => rfl⟩
  · rw [map_neg, hconj, neg_neg]
    exact ⟨fun h' => absurd h'.symm hne, fun h' => absurd rfl h'⟩
end GlobalTheory.PeriodChart
