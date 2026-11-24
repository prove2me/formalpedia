-- Prove2me | solution 1 for GlobalTheory.T.leftColumns_mulVec_injective_of_rank_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:29:14.17145+00:00
-- url     : https://prove2.me/submissions/0cb1d670-3a72-45d7-85fa-909258c82e62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftColumnsMulVecInjectiveOfRankEqCard
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftColumnsMulVecInjectiveOfRankEqCardStatement
import Theorems.Thm_GlobalTheory_mulVec_firstCols_eq_zero_of_rank_eq_card


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k m a b n : Type) [Field k] [Fintype m] [Fintype a] [Fintype b] [Fintype n] (e : a ⊕ b ≃ n) (x : Matrix m n k), x.rank = Fintype.card a → (∀ i j, x i (e (Sum.inr j)) = 0) → ∀ v : a → k, (x.submatrix id (fun i => e (Sum.inl i))) *ᵥ v = 0 → v = 0 := by
  first | exact @GlobalTheory.mulVec_firstCols_eq_zero_of_rank_eq_card | exact GlobalTheory.mulVec_firstCols_eq_zero_of_rank_eq_card | (intros; apply GlobalTheory.mulVec_firstCols_eq_zero_of_rank_eq_card <;> assumption)
end _root_.GlobalTheory.T
