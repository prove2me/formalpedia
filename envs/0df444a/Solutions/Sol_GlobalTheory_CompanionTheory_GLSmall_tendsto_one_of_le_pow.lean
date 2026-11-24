-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GLSmall.tendsto_one_of_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:49:40.891088+00:00
-- url     : https://prove2.me/submissions/59824d2e-c4de-4e71-a6cf-29cb714e9e30

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsLevelInverseCongruence
import Theorems.Thm_GlobalTheory_CompanionTheory_GLSmall_tendsto_zero_of_le_pow

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
theorem _root_.solution {ϖ : k} (h : valuation k ϖ < 1) {n : ℕ} {α : Type} {s : ℕ → Set α}
    (f : α → Matrix (Fin n) (Fin n) k)
    (hf : ∀ l, ∀ a ∈ s l, ∀ i j,
      valuation k (f a i j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ valuation k ϖ ^ l) :
    Tendsto f (⨅ l, 𝓟 (s l)) (𝓝 1) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h0 := (tendsto_zero_of_le_pow h
    (fun a => f a i j - (1 : Matrix (Fin n) (Fin n) k) i j)
    (fun l a ha => hf l a ha i j)).add_const ((1 : Matrix (Fin n) (Fin n) k) i j)
  simpa using h0
end GlobalTheory.CompanionTheory.GLSmall
