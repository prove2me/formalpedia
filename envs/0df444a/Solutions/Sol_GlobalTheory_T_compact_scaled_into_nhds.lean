-- Prove2me | solution 1 for GlobalTheory.T.compact_scaled_into_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:19:29.497112+00:00
-- url     : https://prove2.me/submissions/6bdfab7a-f7e5-469b-a000-8556f306bbeb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CompactScaledIntoNhds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CompactScaledIntoNhdsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CompactScaling_exists_pow_smul_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (K : Set (Fin n → k)), IsCompact K → ∀ U ∈ nhds (0 : Fin n → k), ∀ ϖ : k, valuation k ϖ < 1 → ∃ l : ℕ, ∀ x ∈ K, ϖ ^ l • x ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.CompactScaling.exists_pow_smul_mem | exact GlobalTheory.CompanionTheory.CompactScaling.exists_pow_smul_mem | (intros; apply GlobalTheory.CompanionTheory.CompactScaling.exists_pow_smul_mem <;> assumption)
end _root_.GlobalTheory.T
