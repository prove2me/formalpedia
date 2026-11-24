-- Prove2me | solution 1 for GlobalTheory.Ex.form_le_exponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:44:42.157028+00:00
-- url     : https://prove2.me/submissions/a94dc206-e717-4fee-9af8-8c6588d4610c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HasSumMapPowerSeriesMkFinsum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTxEvEqMapArc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex
namespace GlobalTheory.Ex
theorem _root_.solution {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) {m : ℕ} (hm : m ^ 2 ∣ k)
    {j : ℕ} (hj : j ∣ k) (hj0 : j ≠ 0) (x z : N.X) (s : ℤ) (hs : (m : ℤ) ^ 2 * β.be z z ≤ s) :
    β.be x x ≤ 4 * (m : ℤ) ^ 2 * (β.be x x / (2 * m ^ 2) + β.be z x / j + s) := by
  have hB0 : ∀ y, 0 ≤ β.be y y := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · exact (β.pos y hy).le
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have hk : k = 0 := by simpa using hm
    have h0 : β.be x x = 0 := by
      have h := β.dvd x x
      simpa [hk] using h
    simp [h0]
  · have hmk : (2 * (m : ℤ) ^ 2) ∣ 2 * (k : ℤ) := mul_dvd_mul_left 2 (by exact_mod_cast hm)
    have hjk : (j : ℤ) ∣ 2 * (k : ℤ) := dvd_mul_of_dvd_right (by exact_mod_cast hj) 2
    obtain ⟨q, hq⟩ := dvd_trans hmk (β.dvd x x)
    obtain ⟨c, hc⟩ := dvd_trans hjk (β.dvd z x)
    have hm2 : (0 : ℤ) < 2 * (m : ℤ) ^ 2 := by positivity
    have hj1 : (1 : ℤ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj0
    have hq' : β.be x x / (2 * m ^ 2) = q := by
      rw [hq]
      exact Int.mul_ediv_cancel_left q hm2.ne'
    have hc' : β.be z x / j = c := by
      rw [hc]
      exact Int.mul_ediv_cancel_left c (by omega)
    rw [hq', hc']
    have hexp := hB0 ((j : ℤ) • x + (2 * (m : ℤ) ^ 2) • z)
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hexp
    rw [β.symm x z, hc] at hexp
    have ha := hB0 z
    have hs0 : 0 ≤ s := le_trans (mul_nonneg (by positivity) ha) hs
    have hjj : (0 : ℤ) ≤ (j : ℤ) ^ 2 - 1 := by nlinarith
    have h5 : 0 ≤ 4 * (m : ℤ) ^ 2 * (((j : ℤ) ^ 2 - 1) * s + (s - (m : ℤ) ^ 2 * β.be z z)) :=
      mul_nonneg (by positivity) (add_nonneg (mul_nonneg hjj hs0) (by linarith))
    have key : 0 ≤ (j : ℤ) ^ 2 * (β.be x x + 4 * (m : ℤ) ^ 2 * c + 4 * (m : ℤ) ^ 2 * s) := by
      nlinarith [hexp, h5]
    have hX : 0 ≤ β.be x x + 4 * (m : ℤ) ^ 2 * c + 4 * (m : ℤ) ^ 2 * s := by
      by_contra hneg
      push_neg at hneg
      have := mul_neg_of_pos_of_neg (by positivity : (0 : ℤ) < (j : ℤ) ^ 2) hneg
      linarith
    nlinarith [hX, hq]
end GlobalTheory.Ex
