-- Prove2me | solution 1 for GlobalTheory.RankChart.out_mk_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:40.485278+00:00
-- url     : https://prove2.me/submissions/2f9b52f1-2634-4d85-acda-7cff4520ce48

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
theorem _root_.solution {G : Type} [AddCommGroup G] (H L : AddSubgroup G) (x : H) :
    (((QuotientAddGroup.mk x : H ⧸ L.addSubgroupOf H).out : H) : G) - x ∈ L := by
  have h := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk x : H ⧸ L.addSubgroupOf H))
  rw [AddSubgroup.mem_addSubgroupOf] at h
  have := L.neg_mem h
  simpa [neg_add_eq_sub] using this
end GlobalTheory.RankChart
