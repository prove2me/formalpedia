-- Prove2me | solution 1 for GlobalTheory.T.fundamental_domain_L2_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:10:49.718978+00:00
-- url     : https://prove2.me/submissions/5b281896-e763-41bd-9458-1c24c5861bf6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FundamentalDomainL2Bound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FundamentalDomainL2BoundStatement
import Theorems.Thm_GlobalTheory_QuotLocInt_integrableOn_compact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ C : Set G, IsCompact C → ∀ n : ℝ, (∀ y : G, {γ : G | γ ∈ Γ ∧ γ * y ∈ C}.Finite ∧ (({γ : G | γ ∈ Γ ∧ γ * y ∈ C}.ncard : ℕ) : ℝ) ≤ n) → ∃ M : ℝ, ∀ F : Lp ℂ 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))), IntegrableOn (fun x => F (Quotient.mk _ x)) C μ ∧ ∫ x in C, ‖F (Quotient.mk _ x)‖ ∂μ ≤ M * ‖F‖ := by
  first | exact @GlobalTheory.QuotLocInt.integrableOn_compact | exact GlobalTheory.QuotLocInt.integrableOn_compact | (intros; apply GlobalTheory.QuotLocInt.integrableOn_compact <;> assumption)
end _root_.GlobalTheory.T
