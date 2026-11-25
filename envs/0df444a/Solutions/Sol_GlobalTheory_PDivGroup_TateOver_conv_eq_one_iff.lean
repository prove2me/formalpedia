-- Prove2me | solution 1 for GlobalTheory.PDivGroup.TateOver.conv_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:53:50.752895+00:00
-- url     : https://prove2.me/submissions/405db0f0-971c-4e4b-82e2-d8a329406022

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
import Theorems.Thm_GlobalTheory_PDivGroup_TateOver_pow_smul_conv
import Theorems.Thm_GlobalTheory_PDivGroup_TateOver_exists_p_smul_eq

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
theorem _root_.solution (t : G.TateOver B) (n : ℕ) :
    t.conv n = 1 ↔ ∃ s : G.TateOver B, (p : ℤ_[p]) ^ n • s = t := by
  constructor
  · induction n generalizing t with
    | zero => exact fun _ => ⟨t, by rw [pow_zero, one_smul]⟩
    | succ n ih =>
      intro ht
      obtain ⟨s, hs, rfl⟩ := t.exists_p_smul_eq n ht
      obtain ⟨u, rfl⟩ := ih s hs
      exact ⟨u, by rw [pow_succ', mul_smul]⟩
  · rintro ⟨s, rfl⟩
    rw [TateOver.pow_smul_conv, G.pts_pow_self]
end TateOver
end GlobalTheory.PDivGroup
