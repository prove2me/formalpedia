-- Prove2me | solution 1 for InverseZeroSum.Candidate3.shortZero_subset_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:31:49.84713+00:00
-- url     : https://prove2.me/submissions/c7adbca1-cab0-430d-99c5-5a0498bb3a8e

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_singleton_not_shortZero
public import Theorems.Thm_InverseZeroSum_Candidate3_shortZero_card_two_or_three
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution {n : ℕ} {S : PosSeq n}
    {I J : Finset (Fin n)} (hI : ShortZero S I) (hJ : ShortZero S J)
    (hsub : I ⊆ J) : I = J := by
  classical
  rcases shortZero_card_two_or_three hI with hi | hi <;>
    rcases shortZero_card_two_or_three hJ with hj | hj
  · exact Finset.eq_of_subset_of_card_le hsub (by omega)
  · have hcard : (J \ I).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
      omega
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcard
    have hsum : posSum S I + posSum S (J \ I) = posSum S J := by
      simpa [posSum, add_comm] using (Finset.sum_sdiff hsub (f := fun i => (S i : G)))
    have hz : posSum S (J \ I) = 0 := by
      rw [hI.2.2, hJ.2.2] at hsum
      simpa using hsum
    apply False.elim
    apply singleton_not_shortZero S k
    refine ⟨by simp, by simp, ?_⟩
    simpa [hk] using hz
  · exact Finset.eq_of_subset_of_card_le hsub (by omega)
  · exact Finset.eq_of_subset_of_card_le hsub (by omega)
end InverseZeroSum.Candidate3
