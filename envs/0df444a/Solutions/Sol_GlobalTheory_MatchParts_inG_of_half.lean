-- Prove2me | solution 1 for GlobalTheory.MatchParts.inG_of_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:13:25.598989+00:00
-- url     : https://prove2.me/submissions/e003174c-2cfa-4804-b2a7-26c621ce3dc1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TxCosetCriterionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionMatchedPartsDimEq
import Theorems.Thm_GlobalTheory_MatchParts_r_left
import Theorems.Thm_GlobalTheory_MatchParts_r_pow
import Theorems.Thm_GlobalTheory_MatchParts_pow_eq_one_of
import Theorems.Thm_GlobalTheory_MatchParts_exists_rep
import Theorems.Thm_GlobalTheory_MatchParts_y_pow
import Theorems.Thm_GlobalTheory_MatchParts_nsmul_cancel

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
theorem _root_.solution (μ : Match N N' n) {k k' K m : ℕ} (hK : K = k * k') (hm : K = m * m) (hkm : k ∣ m) (hm0 : m ≠ 0)
    (hlev : ∃ j, K = n ^ j) (hdiv : ∀ γ : N.Gt, ∃ γ' : N.Gt, γ' ^ m = γ)
    (H : ∀ p : N.QT K, p.1.1 = 1 → ∃ p', μ.r K p p' ∧ ∃ z, p'.1.1.toAdd = m • z)
    (p : N.QT k) (p' : N'.QT k) (h : μ.r k p p') (hp : N.InG p) : N'.InG p' := by
  subst hK
  have hk' : k' ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hm0 hm0 (hm.symm.trans (mul_zero _))
  obtain ⟨p₀, e, h0⟩ := exists_rep hp
  replace h := r_left μ h e
  have hx := pow_eq_one_of p₀ h0
  obtain ⟨ξ, hξ⟩ := hdiv p₀.1.2
  have hξ' : ξ ^ (k * k') = 1 := by
    obtain ⟨c, hc⟩ := hkm
    rw [hm, pow_mul, hξ, hc, pow_mul, hx, one_pow]
  obtain ⟨ξ', hr, z, hz⟩ := H (ofG ξ hξ') rfl
  let q' : N'.QT (k * k') := ⟨(p'.1.1 ^ k', p'.1.2), by
    rw [N'.mem_QT, pow_mul, N'.mem_QT.1 p'.2, toAdd_pow, N'.io_nsmul]⟩
  have hq : μ.r (k * k') (ofG ξ hξ' ^ m) q' :=
    (μ.incl k k' p₀ p' _ q' hk' (by simp [ofG, h0]) (by simpa [ofG] using hξ) rfl rfl).1 h
  obtain ⟨w, hw, -⟩ := (r_right μ (r_pow μ hlev hr m)).1 hq
  refine ⟨z + w, nsmul_cancel hk' ?_⟩
  rw [y_pow, hz, smul_smul, ← hm, ← smul_add] at hw
  rw [smul_smul, mul_comm, ← hw]
  rfl
end GlobalTheory.MatchParts
