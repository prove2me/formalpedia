-- Prove2me | solution 1 for GlobalTheory.T.hasSum_heckeSeries_borelSpherical_integralCosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:35:32.54568+00:00
-- url     : https://prove2.me/submissions/38b3c32f-22a2-4cea-b402-db702e5a4321

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesBorelSphericalIntegralCosets
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesBorelSphericalIntegralCosetsStatement
import Theorems.Thm_GlobalTheory_HeckeSeries_hasSum_integral_cosets


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ), IsBorelSph k γ φ → ∀ X : ℂ, (∀ i : Fin n, ‖(resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X‖ < 1) → HasSum (fun c : {c : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (c.out : GL (Fin n) k).1 i j ∈ 𝒪[k])} => X ^ (ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat * φ c.1.out) (∏ i : Fin n, (1 - (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X)⁻¹) := by
  first | exact @GlobalTheory.HeckeSeries.hasSum_integral_cosets | exact GlobalTheory.HeckeSeries.hasSum_integral_cosets | (intros; apply GlobalTheory.HeckeSeries.hasSum_integral_cosets <;> assumption)
end _root_.GlobalTheory.T
