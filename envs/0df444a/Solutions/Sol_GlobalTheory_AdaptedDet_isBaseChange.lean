-- Prove2me | solution 1 for GlobalTheory.AdaptedDet.isBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:54:14.958821+00:00
-- url     : https://prove2.me/submissions/858acf9e-5c44-4c50-8287-3ec58d96e187

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralDetSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmUnitPowFourIdempotentModEight

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
    (hspan : Submodule.span E (Set.range φ) = ⊤) : IsBaseChange E φ := by
  rw [← isLocalizedModule_iff_isBaseChange (𝓞 E)⁰ E]
  exact
    { map_units := fun s => (isLocalizedModule_id (𝓞 E)⁰ (Fin r → E) E).map_units s
      surj := fun v => by
        have hv : v ∈ Submodule.span E (Set.range φ) := by rw [hspan]; trivial
        obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E _ v hv
        rw [← LinearMap.coe_range, Submodule.span_eq] at ht
        obtain ⟨m, hm⟩ := ht
        exact ⟨(m, t), hm.symm⟩
      exists_of_eq := fun h => ⟨1, by rw [hf h]⟩ }
end GlobalTheory.AdaptedDet
