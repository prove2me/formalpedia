-- Prove2me | solution 1 for GlobalTheory.PDivGroup.natCard_conv_pts_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:35:09.393486+00:00
-- url     : https://prove2.me/submissions/03d358f5-83dc-4fac-8b8f-4883d8d26f5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
import Theorems.Thm_GlobalTheory_PDivGroup_natCard_pts_eq

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
variable [Fact p.Prime]
namespace GlobalTheory.PDivGroup
theorem _root_.solution (n : ℕ) :
    Nat.card (WithConv (G.A n →ₐ[O] O)) = p ^ (n * G.height) :=
  (Nat.card_congr (WithConv.equiv _)).trans (G.natCard_pts_eq C n)
end GlobalTheory.PDivGroup
