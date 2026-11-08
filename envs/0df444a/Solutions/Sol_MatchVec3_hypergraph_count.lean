-- Prove2me | solution 1 for MatchVec3.hypergraph_count
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T16:55:29.775391+00:00
-- url     : https://prove2.me/submissions/cb8c4cbe-a366-44d7-bbac-62d39902b5c7

import Mathlib
import Definitions.Def_MatchVec3_matchingNumber
import Definitions.Def_MatchVec3_maxDegree

open MatchVec3 in
theorem solution {K L : ℕ} (hL : 1 ≤ L) (F : Finset (Finset (Fin K)))
    (hF : ∀ A ∈ F, A.card = L) :
    F.card ≤ L * matchingNumber F * maxDegree F := by
  classical
  set Ms := F.powerset.filter fun M => ∀ A ∈ M, ∀ B ∈ M, A ≠ B → Disjoint A B with hMs
  obtain ⟨M, hM, hMeq⟩ := Finset.exists_mem_eq_sup Ms ⟨∅, by simp [hMs]⟩ Finset.card
  have hnu : matchingNumber F = M.card := by
    unfold matchingNumber; rw [← hMs, hMeq]
  rw [hMs, Finset.mem_filter, Finset.mem_powerset] at hM
  obtain ⟨hMF, hMm⟩ := hM
  set U := M.biUnion id with hU
  have hUcard : U.card ≤ M.card * L := by
    calc U.card ≤ ∑ A ∈ M, (id A).card := Finset.card_biUnion_le
      _ = ∑ A ∈ M, L := Finset.sum_congr rfl (fun A hA => hF A (hMF hA))
      _ = M.card * L := by rw [Finset.sum_const, smul_eq_mul]
  have hcover : F ⊆ U.biUnion (fun i => F.filter (fun A => i ∈ A)) := by
    intro A hA
    rw [Finset.mem_biUnion]
    by_contra hno
    push_neg at hno
    have hdisj : ∀ i ∈ U, i ∉ A := by
      intro i hi hiA
      exact hno i hi (Finset.mem_filter.2 ⟨hA, hiA⟩)
    have hAne : A.Nonempty := by
      rw [← Finset.card_pos, hF A hA]; omega
    have hAM : A ∉ M := by
      intro hAM
      obtain ⟨i, hi⟩ := hAne
      exact hdisj i (Finset.mem_biUnion.2 ⟨A, hAM, hi⟩) hi
    have hins : insert A M ∈ Ms := by
      rw [hMs, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.insert_subset hA hMF, ?_⟩
      have hd : ∀ B ∈ M, Disjoint A B := by
        intro B hB
        rw [Finset.disjoint_left]
        intro i hiA hiB
        exact hdisj i (Finset.mem_biUnion.2 ⟨B, hB, hiB⟩) hiA
      intro X hX Y hY hXY
      rw [Finset.mem_insert] at hX hY
      rcases hX with rfl | hX <;> rcases hY with rfl | hY
      · exact absurd rfl hXY
      · exact hd Y hY
      · exact (hd X hX).symm
      · exact hMm X hX Y hY hXY
    have := Finset.le_sup (f := Finset.card) hins
    rw [hMeq, Finset.card_insert_of_notMem hAM] at this
    omega
  have hdeg : ∀ i, (F.filter (fun A => i ∈ A)).card ≤ maxDegree F := by
    intro i
    unfold maxDegree
    exact Finset.le_sup (f := fun i => (F.filter fun A => i ∈ A).card) (Finset.mem_univ i)
  calc F.card ≤ (U.biUnion (fun i => F.filter (fun A => i ∈ A))).card := Finset.card_le_card hcover
    _ ≤ ∑ i ∈ U, (F.filter (fun A => i ∈ A)).card := Finset.card_biUnion_le
    _ ≤ ∑ i ∈ U, maxDegree F := Finset.sum_le_sum (fun i _ => hdeg i)
    _ = U.card * maxDegree F := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ M.card * L * maxDegree F := Nat.mul_le_mul_right _ hUcard
    _ = L * matchingNumber F * maxDegree F := by rw [hnu]; ring
