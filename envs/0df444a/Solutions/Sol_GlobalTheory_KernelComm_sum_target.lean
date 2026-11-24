-- Prove2me | solution 1 for GlobalTheory.KernelComm.sum_target
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:15:44.748699+00:00
-- url     : https://prove2.me/submissions/b740ff0d-68c6-4f3b-acce-a26add964eb2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndicatorIdentity
import Theorems.Thm_GlobalTheory_LatPair_cross_hasVal
import Theorems.Thm_GlobalTheory_LatPair_eq_glue_iff
import Theorems.Thm_GlobalTheory_LatPair_maps_iff_glue


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity GlobalTheory.PairOp
noncomputable section
open GlobalTheory GlobalTheory.KernelComm
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}
variable [Fintype n'] (q : Unif k) {P₁ : Pair k n'} {e₁ : n' → k} (he : P₁.HasVal e₁ 1) (Q : Pair k n)
  (x : Matrix n n' k)
include he
open Classical
namespace GlobalTheory.KernelComm
theorem _root_.solution :
    ∑ Q₁ ∈ withKer Q.lat with cross q Q₁ Q = 1, phiOne P₁ Q₁ x = midInd q P₁.ker e₁ Q x := by
  have hm : ∀ Q₁ : Pair k n, Maps P₁ Q₁ x ↔ (∀ y ∈ P₁.ker, x *ᵥ y ∈ Q₁.ker) ∧ Q₁.HasVal (x *ᵥ e₁) 1 := fun Q₁ => by
    rw [maps_iff_glue he Q₁.hasVal_vec, Pair.hasVal_one_iff Q₁.hasVal_vec]
  rw [midInd, mulVec_smul]
  split_ifs with h
  · have hg : IsGlue Q.lat (x *ᵥ e₁) := (isGlue_iff q).2 ⟨Q.isLat, fun h0 =>
      one_ne_zero (h.2.unique (Pair.mem_ker.1 (Pair.smul_mem_ker q.mem_max h0))), h.2.mem⟩
    rw [Finset.sum_eq_single_of_mem (glue hg)]
    · exact if_pos ((hm _).2 ⟨by rw [glue_ker]; exact h.1, glue_hasVal hg⟩)
    · exact Finset.mem_filter.2 ⟨mem_withKer.2 (glue_ker hg),
        (cross_hasVal q (glue_ker hg).symm (glue_hasVal hg)).unique h.2⟩
    · exact fun Q₁ h1 h2 => if_neg fun h3 =>
        h2 ((eq_glue_iff hg).2 ⟨mem_withKer.1 (Finset.mem_filter.1 h1).1, ((hm _).1 h3).2⟩)
  · refine Finset.sum_eq_zero fun Q₁ h1 => if_neg fun h3 => h ?_
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h1
    rw [mem_withKer] at h1
    exact ⟨h1 ▸ ((hm _).1 h3).1, h2 ▸ cross_hasVal q h1.symm ((hm _).1 h3).2⟩
end GlobalTheory.KernelComm
