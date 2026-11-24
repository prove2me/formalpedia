-- Prove2me | solution 1 for GlobalTheory.T.hasSum_hecke_series_spherical_integral_inverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:42:18.039132+00:00
-- url     : https://prove2.me/submissions/8fa81409-8ec2-46a7-8a39-310aabca7426

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverse
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverseStatement
import Theorems.Thm_GlobalTheory_HeckeDual_hasSum_dual


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ), IsBorelSph k γ φ → (∀ i, γ i ≠ 0) → ∀ X : ℂ, (∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X‖ < 1) → HasSum (fun c : {c : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (c.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k])} => X ^ (-ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat * φ c.1.out) (∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X)⁻¹) := by
  first | exact @GlobalTheory.HeckeDual.hasSum_dual | exact GlobalTheory.HeckeDual.hasSum_dual | (intros; apply GlobalTheory.HeckeDual.hasSum_dual <;> assumption)
end _root_.GlobalTheory.T
