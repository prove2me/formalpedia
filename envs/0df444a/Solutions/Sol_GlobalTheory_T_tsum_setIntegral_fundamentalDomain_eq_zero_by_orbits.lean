-- Prove2me | solution 1 for GlobalTheory.T.tsum_setIntegral_fundamentalDomain_eq_zero_by_orbits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:33:50.531482+00:00
-- url     : https://prove2.me/submissions/2e564b27-b7c4-4a1b-b94a-11afc85e072a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TsumSetIntegralFundamentalDomainEqZeroByOrbits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TsumSetIntegralFundamentalDomainEqZeroByOrbitsStatement
import Theorems.Thm_GlobalTheory_OrbitUnfold_tsum_setIntegral_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant] (Γ : Subgroup H) [Countable Γ] (Y : Type) [Countable Y] [MulAction Γ Y] (𝓕 : Set H), IsFundamentalDomain Γ 𝓕 ν → ∀ Φ : Y → H → ℂ, (∀ y, Measurable (Φ y)) → (∀ (γ : Γ) y h, Φ (γ • y) ((γ : H) * h) = Φ y h) → ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν ≠ ⊤ → (∀ y (𝓖 : Set H), IsFundamentalDomain ((MulAction.stabilizer Γ y).map Γ.subtype) 𝓖 ν → IntegrableOn (Φ y) 𝓖 ν → ∫ h in 𝓖, Φ y h ∂ν = 0) → ∑' y, ∫ h in 𝓕, Φ y h ∂ν = 0 := by
  first | exact @GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero | exact GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero | (intros; apply GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero <;> assumption)
end _root_.GlobalTheory.T
