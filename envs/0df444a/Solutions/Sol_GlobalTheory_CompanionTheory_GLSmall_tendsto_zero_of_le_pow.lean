-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GLSmall.tendsto_zero_of_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:33:29.209405+00:00
-- url     : https://prove2.me/submissions/029070fd-a71a-407c-979f-79dcf258a818

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsLevelInverseCongruence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Matrix Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GLSmall
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.GLSmall
theorem _root_.solution {ϖ : k} (h : valuation k ϖ < 1) {α : Type} {s : ℕ → Set α} (f : α → k)
    (hf : ∀ l, ∀ a ∈ s l, valuation k (f a) ≤ valuation k ϖ ^ l) :
    Tendsto f (⨅ l, 𝓟 (s l)) (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨l, hl⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  refine mem_iInf_of_mem l (mem_principal.2 fun a ha => ?_)
  exact lt_of_le_of_lt (hf l a ha) hl
end GlobalTheory.CompanionTheory.GLSmall
