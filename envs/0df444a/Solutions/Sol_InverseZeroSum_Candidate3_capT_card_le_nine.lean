-- Prove2me | solution 1 for InverseZeroSum.Candidate3.capT_card_le_nine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:40:33.898509+00:00
-- url     : https://prove2.me/submissions/30c8d873-7aa2-467e-a18d-41bfbe6f31e2

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_no_ten_capT

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution {A : Finset F3T} (hA : IsCapT A) : A.card ≤ 9 := by
  by_contra hnot
  have h10 : 10 ≤ A.card := by omega
  obtain ⟨B, hBA, hBcard⟩ :=
    Finset.exists_subset_card_eq (s := A) (n := 10) h10
  have hB : IsCapT B := by
    intro a ha b hb c hc hab hac hbc
    exact hA a (hBA ha) b (hBA hb) c (hBA hc) hab hac hbc
  exact no_ten_capT hB hBcard
end InverseZeroSum.Candidate3
