-- Prove2me | solution 1 for GlobalTheory.PDivGroup.natCard_pts_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:13:23.334723+00:00
-- url     : https://prove2.me/submissions/189c410a-0a04-4bc5-9fd4-26cb73363e43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
import Theorems.Thm_GlobalTheory_TateFree_natCard_pts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv TateFree
variable {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O)
variable (C : Type) [Field C] [Algebra O C] [IsIntegrallyClosedIn O C] [IsAlgClosed C]
  [CharZero C]
include C
namespace GlobalTheory.PDivGroup
theorem _root_.solution (n : ℕ) : Nat.card (G.A n →ₐ[O] O) = p ^ (n * G.height) := by
  have h := congrFun (rankAtStalk_eq_finrank_of_free (R := C) (M := C ⊗[O] G.A n)) ⊥
  rw [rankAtStalk_baseChange, G.rank_eq] at h
  rw [natCard_pts O C]
  exact h.symm
end GlobalTheory.PDivGroup
