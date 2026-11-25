-- Prove2me | solution 1 for GlobalTheory.PDivGroup.TateOver.pow_smul_conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:45:06.816219+00:00
-- url     : https://prove2.me/submissions/3910e998-65cb-422d-9bd2-db2629058e43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
import Theorems.Thm_GlobalTheory_PDiv_pow_digit_natCast


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
variable {B : Type} [CommRing B] [Algebra O B]
variable [Fact p.Prime] {G}
namespace GlobalTheory.PDivGroup
namespace TateOver
theorem _root_.solution (x : G.TateOver B) (k n : ℕ) :
    ((p : ℤ_[p]) ^ k • x).conv n = x.conv n ^ p ^ k := by
  rw [← Nat.cast_pow]
  exact pow_digit_natCast (G.pts_pow_self n _) _
end TateOver
end GlobalTheory.PDivGroup
