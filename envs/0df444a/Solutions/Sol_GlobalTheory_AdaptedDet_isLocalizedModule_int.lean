-- Prove2me | solution 1 for GlobalTheory.AdaptedDet.isLocalizedModule_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:54:15.765959+00:00
-- url     : https://prove2.me/submissions/73ea4906-aaa5-4f13-b700-2bdaf5cb59e0

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
    (hspan : Submodule.span E (Set.range φ) = ⊤) :
    IsLocalizedModule ℤ⁰ (φ.restrictScalars ℤ) where
  map_units s := (isLocalizedModule_id ℤ⁰ (Fin r → E) ℚ).map_units s
  surj v := by
    have hv : v ∈ Submodule.span E (Set.range φ) := by rw [hspan]; trivial
    obtain ⟨⟨t, n, hn, rfl⟩, ht⟩ := multiple_mem_span_of_mem_localization_span
      (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E _ v hv
    rw [← LinearMap.coe_range, Submodule.span_eq] at ht
    obtain ⟨m, hm⟩ := ht
    refine ⟨(m, ⟨n, hn⟩), ?_⟩
    change n • v = φ m
    rw [hm, Submonoid.smul_def, algebraMap_smul]
  exists_of_eq h := ⟨1, by rw [hf h]⟩
end GlobalTheory.AdaptedDet
