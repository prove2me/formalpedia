-- Prove2me | solution 1 for GlobalTheory.RankChart.sum_shift_out
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:56.127804+00:00
-- url     : https://prove2.me/submissions/6c5ced53-da4d-4f78-8c99-1862ac97e1be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShearGLTransposeMul
import Theorems.Thm_GlobalTheory_RankChart_out_mk_sub_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Matrix
noncomputable section
open GlobalTheory GlobalTheory.RankChart
open GlobalTheory.SplitFlip GlobalTheory.LocMod.Inhab ValuativeRel
open Classical
namespace GlobalTheory.RankChart
theorem _root_.solution {G : Type} [AddCommGroup G] (F : G → ℂ) (H L : AddSubgroup G)
    [Fintype (H ⧸ L.addSubgroupOf H)] (hL : ∀ x y, y - x ∈ L → F y = F x) (hH : ∀ x, F x ≠ 0 → x ∈ H) (x : G) :
    ∑ q : H ⧸ L.addSubgroupOf H, F (x + ((q.out : H) : G)) =
      if x ∈ H then ∑ q : H ⧸ L.addSubgroupOf H, F ((q.out : H) : G) else 0 := by
  split_ifs with hx
  · have key : ∀ q : H ⧸ L.addSubgroupOf H, F (x + ((q.out : H) : G)) =
        F ((((QuotientAddGroup.mk (⟨x, hx⟩ : H) : H ⧸ L.addSubgroupOf H) + q).out : H) : G) := by
      intro q
      have e : (QuotientAddGroup.mk (⟨x, hx⟩ : H) : H ⧸ L.addSubgroupOf H) + q =
          QuotientAddGroup.mk ((⟨x, hx⟩ : H) + q.out) := by
        rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
      rw [e]
      exact (hL (((⟨x, hx⟩ : H) + q.out : H) : G) _ (out_mk_sub_mem H L ((⟨x, hx⟩ : H) + q.out))).symm
    rw [Finset.sum_congr rfl fun q _ => key q]
    exact Fintype.sum_equiv (Equiv.addLeft (QuotientAddGroup.mk (⟨x, hx⟩ : H) : H ⧸ L.addSubgroupOf H))
      (fun q => F ((((QuotientAddGroup.mk (⟨x, hx⟩ : H) : H ⧸ L.addSubgroupOf H) + q).out : H) : G))
      (fun q => F ((q.out : H) : G)) fun q => rfl
  · refine Finset.sum_eq_zero fun q _ => ?_
    by_contra h
    have := H.sub_mem (hH _ h) (q.out : H).2
    rw [add_sub_cancel_right] at this
    exact hx this
end GlobalTheory.RankChart
