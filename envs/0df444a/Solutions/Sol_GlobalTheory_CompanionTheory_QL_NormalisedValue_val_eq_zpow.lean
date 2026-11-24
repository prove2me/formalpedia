-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.NormalisedValue.val_eq_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:03:09.126546+00:00
-- url     : https://prove2.me/submissions/7db13dce-60ba-4dd7-b83b-d2dd5225cb62

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_val_eq_pow_of_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.NormalisedValue
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
namespace GlobalTheory.CompanionTheory.QL.NormalisedValue
theorem _root_.solution (h : LF O ϖ nrm q) {x : F} (hx : x ≠ 0) :
    ∃ e : ℤ, ValuativeRel.valuation F x = ValuativeRel.valuation F ϖ ^ e := by
  by_cases hle : ValuativeRel.valuation F x ≤ 1
  · obtain ⟨n, hn⟩ := val_eq_pow_of_int h hx hle
    exact ⟨n, by rw [hn, _root_.zpow_natCast]⟩
  · have hlt : 1 < ValuativeRel.valuation F x := lt_of_not_ge hle
    have hinv : ValuativeRel.valuation F x⁻¹ ≤ 1 := ((Valuation.one_lt_val_iff _ hx).1 hlt).le
    obtain ⟨n, hn⟩ := val_eq_pow_of_int h (inv_ne_zero hx) hinv
    refine ⟨-(n : ℤ), ?_⟩
    rw [_root_.zpow_neg, _root_.zpow_natCast, ← hn, map_inv₀, _root_.inv_inv]
end GlobalTheory.CompanionTheory.QL.NormalisedValue
