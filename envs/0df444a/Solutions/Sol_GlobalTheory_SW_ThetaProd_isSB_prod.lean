-- Prove2me | solution 1 for GlobalTheory.SW.ThetaProd.isSB_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:44:28.721464+00:00
-- url     : https://prove2.me/submissions/04e207c5-0cc3-4d4b-a8fb-80d5176d7273

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaMulConjEqBlockTheta
import Theorems.Thm_GlobalTheory_SW_ThetaProd_hasLevel_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ThetaProd
namespace GlobalTheory.SW.ThetaProd
theorem _root_.solution {κ ι₁ ι₂ : Type} [Fintype κ] [Fintype ι₁] [Fintype ι₂]
    {φ₁ : Matrix κ ι₁ ℚ → ℂ} {φ₂ : Matrix κ ι₂ ℚ → ℂ} (h₁ : IsSB φ₁) (h₂ : IsSB φ₂) :
    IsSB (fun m : Matrix κ (ι₁ ⊕ ι₂) ℚ => φ₁ m.toCols₁ * conj (φ₂ (-m.toCols₂))) := by
  obtain ⟨R₁, hR₁, h₁⟩ := h₁
  obtain ⟨R₂, hR₂, h₂⟩ := h₂
  have g₁ := hasLevel_mul R₂ h₁
  have g₂ := hasLevel_mul R₁ h₂
  rw [mul_comm] at g₁
  refine ⟨R₁ * R₂, by positivity, fun x hx k i => ?_, fun x y hy => ?_⟩
  · have a₁ := g₁.1 _ (left_ne_zero_of_mul hx)
    have a₂ := g₂.1 _ ((map_ne_zero conj).1 (right_ne_zero_of_mul hx))
    rcases i with i | i
    · exact a₁ k i
    · have := (a₂ k i).neg
      simpa [toCols₂] using this
  · have a₁ := g₁.2 x.toCols₁ y.toCols₁ fun k i => hy k (Sum.inl i)
    have a₂ := g₂.2 (-x.toCols₂) (-y.toCols₂) fun k i => (hy k (Sum.inr i)).neg
    have e₁ : (x + ((R₁ * R₂ : ℕ) : ℚ) • y).toCols₁ =
      x.toCols₁ + ((R₁ * R₂ : ℕ) : ℚ) • y.toCols₁ := rfl
    have e₂ : -(x + ((R₁ * R₂ : ℕ) : ℚ) • y).toCols₂ =
      -x.toCols₂ + ((R₁ * R₂ : ℕ) : ℚ) • (-y.toCols₂) := by
      rw [smul_neg, ← neg_add]; rfl
    simp only [e₁, e₂, a₁, a₂]
end GlobalTheory.SW.ThetaProd
