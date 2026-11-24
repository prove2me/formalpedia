-- Prove2me | solution 1 for GlobalTheory.AdaptedDet.exists_gl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:08:11.429789+00:00
-- url     : https://prove2.me/submissions/ae49d134-f88a-40cb-81c6-e66fffa20b5a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralDetSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmUnitPowFourIdempotentModEight
import Theorems.Thm_GlobalTheory_AdaptedDet_isBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AdaptedDet
variable {E : Type} [Field E] [NumberField E] {L : Type} [AddCommGroup L] [Module (𝓞 E) L] {r : ℕ}
namespace GlobalTheory.AdaptedDet
theorem _root_.solution (φ : L →ₗ[𝓞 E] (Fin r → E)) (hf : Function.Injective φ)
    (hspan : Submodule.span E (Set.range φ) = ⊤) (gam : L ≃ₗ[𝓞 E] L) :
    ∃ γ : GL (Fin r) E, ∀ x, (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ x = φ (gam x) := by
  have hb := isBaseChange φ hf hspan
  let A := hb.lift (φ ∘ₗ gam.toLinearMap)
  let B := hb.lift (φ ∘ₗ gam.symm.toLinearMap)
  have hA : ∀ x, A (φ x) = φ (gam x) := fun x => hb.lift_eq _ x
  have hB : ∀ x, B (φ x) = φ (gam.symm x) := fun x => hb.lift_eq _ x
  have hAB : A ∘ₗ B = LinearMap.id := hb.algHom_ext _ _ fun x => by simp [hA, hB]
  have hBA : B ∘ₗ A = LinearMap.id := hb.algHom_ext _ _ fun x => by simp [hA, hB]
  refine ⟨⟨LinearMap.toMatrix' A, LinearMap.toMatrix' B, ?_, ?_⟩, fun x => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hAB, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp, hBA, LinearMap.toMatrix'_id]
  · simp [hA]
end GlobalTheory.AdaptedDet
