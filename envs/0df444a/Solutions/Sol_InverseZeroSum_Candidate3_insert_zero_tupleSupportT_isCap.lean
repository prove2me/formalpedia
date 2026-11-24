-- Prove2me | solution 1 for InverseZeroSum.Candidate3.insert_zero_tupleSupportT_isCap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:39:36.882775+00:00
-- url     : https://prove2.me/submissions/41323c89-9cb5-44c0-94dc-147c0e8e81bf

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_tupleSupportT_isCap
public import Theorems.Thm_InverseZeroSum_Candidate3_tupleSupportT_no_pair
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution {n : ℕ} (R : PosSeq n)
    (hFree : ShortFree R) :
    IsCapT (insert 0 (tupleSupportT R)) := by
  classical
  have hCap := tupleSupportT_isCap R hFree
  have hNoPair := tupleSupportT_no_pair R hFree
  intro a ha b hb c hc hab hac hbc hsum
  simp only [Finset.mem_insert] at ha hb hc
  rcases ha with rfl | ha
  · have hbS : b ∈ tupleSupportT R := by
      rcases hb with hb0 | hbS
      · exact False.elim (hab hb0.symm)
      · exact hbS
    have hcS : c ∈ tupleSupportT R := by
      rcases hc with hc0 | hcS
      · exact False.elim (hac hc0.symm)
      · exact hcS
    apply hNoPair b hbS c hcS
    simpa using hsum
  · rcases hb with rfl | hb
    · have hcS : c ∈ tupleSupportT R := by
        rcases hc with hc0 | hcS
        · exact False.elim (hbc hc0.symm)
        · exact hcS
      apply hNoPair a ha c hcS
      simpa using hsum
    · rcases hc with rfl | hc
      · apply hNoPair a ha b hb
        simpa [add_assoc] using hsum
      · exact hCap a ha b hb c hc hab hac hbc hsum
end InverseZeroSum.Candidate3
