-- Prove2me | solution 1 for GlobalTheory.card_filter_fin_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:33:40.000954+00:00
-- url     : https://prove2.me/submissions/2245e98e-4f3e-4aa6-aeaa-f9b7dfef65c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CardFilterFinBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    (0 : ℝ) ≤ ((univ.filter p).card : ℝ) ∧ ((univ.filter p).card : ℝ) ≤ n := by
  refine ⟨Nat.cast_nonneg _, ?_⟩
  have h : (univ.filter p).card ≤ n :=
    le_trans (Finset.card_filter_le _ _) (by simp)
  exact_mod_cast h
end GlobalTheory
