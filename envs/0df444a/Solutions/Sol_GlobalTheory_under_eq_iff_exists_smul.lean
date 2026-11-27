-- Prove2me | solution 1 for GlobalTheory.under_eq_iff_exists_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:44:16.30983+00:00
-- url     : https://prove2.me/submissions/d5018327-9583-4b82-8b53-86ca1055975d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable (A G : Type*) [CommRing A] [Group G] [MulSemiringAction G A]
namespace GlobalTheory
theorem _root_.solution [Finite G] (B : Type*) [CommRing B]
    [Algebra B A] [SMulCommClass G B A] [Algebra.IsInvariant B A G]
    (Q Q' : Ideal A) [Q.IsPrime] [Q'.IsPrime] :
    Q.under B = Q'.under B ↔ ∃ g : G, Q' = g • Q :=
  ⟨Algebra.IsInvariant.exists_smul_of_under_eq B A G Q Q',
    by rintro ⟨g, rfl⟩; exact (Ideal.under_smul B Q g).symm⟩
end GlobalTheory
