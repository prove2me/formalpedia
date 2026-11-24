-- Prove2me | solution 1 for GlobalTheory.RankChart.sum_ite_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:10:22.279234+00:00
-- url     : https://prove2.me/submissions/1c82a59a-8255-4f82-905c-ef5eca1d512e

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
import Theorems.Thm_GlobalTheory_RankChart_out_mk_sub_mem
import Theorems.Thm_GlobalTheory_RankChart_mk_eq_mk_iff
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
open Classical
namespace GlobalTheory.RankChart
theorem _root_.solution {G : Type} [AddCommGroup G] (H H' : AddSubgroup G) [Fintype (H' ⧸ H.addSubgroupOf H')]
    (hHH' : H ≤ H') (c : ℂ) (x : G) :
    ∑ q : H' ⧸ H.addSubgroupOf H', (if x + ((q.out : H') : G) ∈ H then c else 0) = if x ∈ H' then c else 0 := by
  split_ifs with hx
  · rw [Finset.sum_eq_single (QuotientAddGroup.mk (⟨-x, H'.neg_mem hx⟩ : H'))]
    · rw [if_pos]
      have := out_mk_sub_mem H' H (⟨-x, H'.neg_mem hx⟩ : H')
      rwa [sub_neg_eq_add, add_comm] at this
    · intro q _ hq
      rw [if_neg]
      intro hmem
      apply hq
      rw [← QuotientAddGroup.out_eq' q, mk_eq_mk_iff]
      rwa [sub_neg_eq_add, add_comm]
    · simp
  · refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg]
    intro hmem
    have := H'.sub_mem (hHH' hmem) (q.out : H').2
    rw [add_sub_cancel_right] at this
    exact hx this
end GlobalTheory.RankChart
