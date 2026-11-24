-- Prove2me | solution 1 for InverseZeroSum.Candidate3.shortZero_disjoint_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:33:32.078265+00:00
-- url     : https://prove2.me/submissions/e72a7081-19b0-4990-a5aa-ce7f824dc3dc

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_shortZero_subset_eq
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution {n : ℕ} {S : PosSeq n}
    (hAvoid : AvoidsInnerJointPair S) {I J : Finset (Fin n)}
    (hI : ShortZero S I) (hJ : ShortZero S J) (hne : I ≠ J) :
    Disjoint I J := by
  classical
  rw [Finset.disjoint_left]
  intro x hxI hxJ
  have hnonempty : (I ∩ J).Nonempty := by
    exact ⟨x, Finset.mem_inter.mpr ⟨hxI, hxJ⟩⟩
  have hzero : posSum S (I ∩ J) = 0 := by
    simpa [innerJointSum] using hAvoid I J hI hJ
  have hInter : ShortZero S (I ∩ J) := by
    refine ⟨hnonempty, ?_, hzero⟩
    exact (Finset.card_le_card Finset.inter_subset_left).trans hI.2.1
  have hEq : I ∩ J = I :=
    shortZero_subset_eq hInter hI Finset.inter_subset_left
  have hIJ : I ⊆ J := Finset.inter_eq_left.mp hEq
  exact hne (shortZero_subset_eq hI hJ hIJ)
end InverseZeroSum.Candidate3
