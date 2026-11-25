-- Prove2me | solution 1 for GlobalTheory.PDivGroup.muRoot_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:34:32.836813+00:00
-- url     : https://prove2.me/submissions/4a563770-c67f-4832-b8f4-af31955ba38d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
import Theorems.Thm_GlobalTheory_PDivGroup_TateOver_conv_eq_one_iff

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
theorem _root_.solution (x : (mu p O).TateOver B) (n : ℕ) :
    muRoot x n = 1 ↔ ∃ y : (mu p O).TateOver B, (p : ℤ_[p]) ^ n • y = x := by
  rw [← TateOver.conv_eq_one_iff, ← muRoot_zero (p := p) (O := O) n]
  exact ⟨fun h => congrArg toConv (mu_algHom_ext h),
    fun h => DFunLike.congr_fun (congrArg ofConv h) _⟩
end GlobalTheory.PDivGroup
