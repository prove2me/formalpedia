-- Prove2me | solution 1 for GlobalTheory.MatchParts.half_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:57:13.38996+00:00
-- url     : https://prove2.me/submissions/cf9f6f79-34a9-4db3-89d8-f08b72e00a1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TxCosetCriterionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionMatchedPartsDimEq
import Theorems.Thm_P2M_GlobalTheory_MatchParts_tot__1edb3291971f
import Theorems.Thm_GlobalTheory_MatchParts_r_one
import Theorems.Thm_GlobalTheory_MatchParts_r_pow
import Theorems.Thm_GlobalTheory_MatchParts_y_pow

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
open GlobalTheory GlobalTheory.MatchParts
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ}
namespace GlobalTheory.MatchParts
theorem _root_.solution (μ : Match N N' n) (j : ℕ) (hj : 2 ≤ j) (hdiv : ∀ γ : N.Gt, ∃ γ' : N.Gt, γ' ^ n = γ)
    (hc : ‖μ.c₀‖ = 1)
    (hcos : ∀ p : N.QT ((n ^ j) ^ 2), p.1.1 = 1 → ∃ h : N.QT ((n ^ j) ^ 2), h.1.1 = 1 ∧ h.1.2 ^ n ^ (j + 1) = 1 ∧
      ‖N.tx (n ^ j) (p * h)‖ = 1)
    (hsup : ∀ p : N'.QT ((n ^ j) ^ 2), ‖N'.tx (n ^ j) p‖ = 1 → ∃ z, p.1.1.toAdd = n ^ j • z)
    (p : N.QT ((n ^ j) ^ 2)) (hp : p.1.1 = 1) :
    ∃ p', μ.r _ p p' ∧ ∃ z, p'.1.1.toAdd = n ^ j • z := by
  have hk : ∃ i, (n ^ j) ^ 2 = n ^ i := ⟨j * 2, (pow_mul _ _ _).symm⟩
  let P : N.QT ((n ^ j) ^ 2) → Prop := fun p => ∃ p', μ.r _ p p' ∧ ∃ z, p'.1.1.toAdd = n ^ j • z
  have Pmul : ∀ a b, P a → P b → P (a * b) := by
    rintro a b ⟨a', ha, z, hz⟩ ⟨b', hb, w, hw⟩
    refine ⟨a' * b', μ.mul _ _ _ _ _ ha hb, z + w, ?_⟩
    change a'.1.1.toAdd + b'.1.1.toAdd = _
    rw [hz, hw, smul_add]
  have Ppow : ∀ a (i : ℕ), P a → P (a ^ i) := by
    rintro a i ⟨a', ha, z, hz⟩
    exact ⟨a' ^ i, r_pow μ hk ha i, i • z, by rw [y_pow, hz, smul_comm]⟩
  have step : ∀ p : N.QT ((n ^ j) ^ 2), p.1.1 = 1 → ∃ s d, P s ∧ d.1.1 = 1 ∧ p = s * d ^ n := by
    intro p hp
    obtain ⟨h, h1, h2, h3⟩ := hcos p hp
    obtain ⟨s', hs'⟩ := tot' μ hk (p * h)
    obtain ⟨δ, hδ⟩ := hdiv h.1.2⁻¹
    have hδ' : δ ^ (n ^ j) ^ 2 = 1 := by
      obtain ⟨i, hi⟩ : ∃ i, j * 2 = 1 + (j + 1) + i := ⟨j - 2, by omega⟩
      rw [← pow_mul, hi, pow_add, pow_add, pow_one, pow_mul, pow_mul, hδ, inv_pow, h2, inv_one, one_pow]
    refine ⟨p * h, ofG δ hδ', ⟨s', hs', hsup s' ?_⟩, rfl, ?_⟩
    · rw [μ.tx j _ _ hs', norm_mul, hc, h3, one_mul]
    · have : ofG δ hδ' ^ n = h⁻¹ := by
        refine Subtype.ext (Prod.ext ?_ ?_)
        · simp [ofG, h1]
        · simpa [ofG] using hδ
      rw [this, mul_inv_cancel_right]
  have iter : ∀ i : ℕ, ∃ s d, P s ∧ d.1.1 = 1 ∧ p = s * d ^ n ^ i := by
    intro i
    induction i with
    | zero => exact ⟨1, p, ⟨1, r_one μ hk, 0, by simp⟩, hp, by simp⟩
    | succ i ih =>
      obtain ⟨s, d, hs, hd, e⟩ := ih
      obtain ⟨s₂, d₂, hs₂, hd₂, e₂⟩ := step d hd
      refine ⟨s * s₂ ^ n ^ i, d₂, Pmul _ _ hs (Ppow _ _ hs₂), hd₂, ?_⟩
      rw [e, e₂, mul_pow, ← pow_mul d₂, mul_assoc s, pow_succ' n i]
  obtain ⟨s, d, hs, -, e⟩ := iter j
  rw [e]
  obtain ⟨d', hd'⟩ := tot' μ hk d
  exact Pmul _ _ hs ⟨_, r_pow μ hk hd' _, _, y_pow _ _⟩
end GlobalTheory.MatchParts
