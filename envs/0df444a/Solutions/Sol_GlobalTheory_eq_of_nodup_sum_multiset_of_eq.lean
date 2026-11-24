-- Prove2me | solution 1 for GlobalTheory.eq_of_nodup_sum_multiset_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:57:48.45483+00:00
-- url     : https://prove2.me/submissions/41124456-39e5-430c-be4e-b565d72f786a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqOfNodupSumMultisetOfEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (ι : Type) [Fintype ι] [DecidableEq ι]
    (B : ι → Multiset ℂ) (h : (∑ i, B i).Nodup) (i j : ι) (hi : B i ≠ 0) (hij : B i = B j) :
    i = j := by
  by_contra hne
  have hle : B i + B j ≤ ∑ k, B k := by
    rw [← Finset.sum_pair hne]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hnd : (B i + B j).Nodup := Multiset.nodup_of_le hle h
  rw [← hij] at hnd
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hi
  exact Multiset.disjoint_left.1 (Multiset.nodup_add.1 hnd).2.2 ha ha
end GlobalTheory
