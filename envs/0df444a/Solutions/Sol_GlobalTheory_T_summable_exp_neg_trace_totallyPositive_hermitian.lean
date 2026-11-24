-- Prove2me | solution 1 for GlobalTheory.T.summable_exp_neg_trace_totallyPositive_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:56:59.825858+00:00
-- url     : https://prove2.me/submissions/a695d96f-1902-4428-8137-b6e595c80f89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableExpNegTraceTotallyPositiveHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableExpNegTraceTotallyPositiveHermitianStatement
import Theorems.Thm_GlobalTheory_SW_summable_exp_neg_trace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (N c : ℕ) (δ : ℝ), 0 < c → 0 < δ → Summable fun T : {T : Matrix (Fin N) (Fin N) E // ccT T = T ∧ Den c T ∧ ∀ τ : Ψ, (T.map τ.1).PosSemidef} => Real.exp (-(δ * ∑ τ : Ψ, (T.1.map τ.1).trace.re)) := by
  first | exact @GlobalTheory.SW.summable_exp_neg_trace | exact GlobalTheory.SW.summable_exp_neg_trace | (intros; apply GlobalTheory.SW.summable_exp_neg_trace <;> assumption)
end _root_.GlobalTheory.T
