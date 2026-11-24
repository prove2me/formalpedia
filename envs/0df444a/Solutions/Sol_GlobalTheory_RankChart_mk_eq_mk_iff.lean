-- Prove2me | solution 1 for GlobalTheory.RankChart.mk_eq_mk_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:51:44.002806+00:00
-- url     : https://prove2.me/submissions/1ff29e6b-ee53-4fe9-96b9-351ae37c32f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShearGLTransposeMul
import Theorems.Thm_P2M_GlobalTheory_RankChart_toRows__shear_d5dffcf9ff0a
import Theorems.Thm_P2M_GlobalTheory_RankChart_toRows__dil_a78c4f6a5c7f
import Theorems.Thm_P2M_GlobalTheory_RankChart_toRows__stack_b71dac95216e
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.RankChart.toRows₁_shear
attribute [local simp] GlobalTheory.RankChart.toRows₁_dil
attribute [local simp] GlobalTheory.RankChart.toRows₁_stack

set_option autoImplicit false
open GlobalTheory.WeilM Matrix
noncomputable section
open GlobalTheory GlobalTheory.RankChart
open GlobalTheory.SplitFlip GlobalTheory.LocMod.Inhab ValuativeRel
namespace GlobalTheory.RankChart
theorem _root_.solution {G : Type} [AddCommGroup G] (H L : AddSubgroup G) (x y : H) :
    (QuotientAddGroup.mk x : H ⧸ L.addSubgroupOf H) = QuotientAddGroup.mk y ↔ (x : G) - y ∈ L := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, ← L.neg_mem_iff]
  simp [neg_add_eq_sub]
end GlobalTheory.RankChart
