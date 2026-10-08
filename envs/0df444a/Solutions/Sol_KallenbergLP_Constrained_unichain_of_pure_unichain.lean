-- Prove2me | solution 1 for KallenbergLP.Constrained.unichain_of_pure_unichain
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:31:21.875072+00:00
-- url     : https://prove2.me/submissions/669f7e39-2110-4d2b-822c-b97e7a4b7be4

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_KallenbergLP_Constrained_Frequencies



namespace KallenbergLP.Constrained

open MarkovDecisionProcesses

theorem uni_exists_recurrent {S : Type*} [Fintype S] (P : S → S → ℝ) (i : S) :
    ∃ k, Accessible P i k ∧ IsRecurrent P k := by
  classical
  let reach : S → Finset S := fun k => Finset.univ.filter (fun j => Accessible P k j)
  have hne : (reach i).Nonempty := ⟨i, by simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and]; exact Relation.ReflTransGen.refl⟩
  obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image (reach i) (fun k => (reach k).card) hne
  simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and] at hk
  refine ⟨k, hk, ?_⟩
  intro j hj
  have hsub : reach j ⊆ reach k := by
    intro l hl
    simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    exact Relation.ReflTransGen.trans hj hl
  have hcard : (reach k).card ≤ (reach j).card := by
    apply hmin
    simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.ReflTransGen.trans hk hj
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have : k ∈ reach k := by
    simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and]; exact Relation.ReflTransGen.refl
  rw [← heq] at this
  simpa [reach] using this

theorem uni_acc_mono {S : Type*} (P Q : S → S → ℝ) (h : ∀ i j, 0 < P i j → 0 < Q i j)
    {i j : S} (hij : Accessible P i j) : Accessible Q i j := by
  unfold Accessible at *
  exact Relation.ReflTransGen.mono (fun a b hab => h a b hab) _ _ hij

theorem unichain_core {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] (M : StationaryMDP S A) (hM : IsUnichain M)
    (π : KallenbergLP.AverageLP.Pair M → ℝ) (hπ : π ∈ StatRule M) :
    IsUnichainMatrix (policyMatrix π) := by
  classical
  -- choose an action with positive weight in every state
  have hex : ∀ s, ∃ a : M.admissible s, 0 < π ⟨(s, a.1), a.2⟩ := by
    intro s
    by_contra hno
    push_neg at hno
    have h1 := hπ.2 s
    have : ∑ a ∈ (M.admissible s).attach, π ⟨(s, a.1), a.2⟩ ≤ 0 :=
      Finset.sum_nonpos (fun a _ => hno a)
    linarith
  choose f hf using hex
  let d : S → A := fun s => (f s).1
  have hd : ∀ s, d s ∈ M.admissible s := fun s => (f s).2
  have hU := hM d hd
  have hedge : ∀ i j, 0 < transMatrix M d i j → 0 < policyMatrix π i j := by
    intro i j hij
    unfold policyMatrix
    have hterm : 0 < π ⟨(i, (f i).1), (f i).2⟩ * M.trans i (f i).1 j :=
      mul_pos (hf i) hij
    refine lt_of_lt_of_le hterm ?_
    have := Finset.single_le_sum (s := (M.admissible i).attach)
      (f := fun a : M.admissible i => π ⟨(i, a.1), a.2⟩ * M.trans i a.1 j)
      (fun a _ => mul_nonneg (hπ.1 _) (M.trans_nonneg _ _ _)) (Finset.mem_attach _ (f i))
    simpa using this
  intro i j hi hj
  obtain ⟨k1, hik1, hk1⟩ := uni_exists_recurrent (transMatrix M d) i
  obtain ⟨k2, hjk2, hk2⟩ := uni_exists_recurrent (transMatrix M d) j
  have h12 := hU k1 k2 hk1 hk2
  have a1 : Accessible (policyMatrix π) i k2 :=
    Relation.ReflTransGen.trans (uni_acc_mono _ _ hedge hik1) (uni_acc_mono _ _ hedge h12)
  have a2 : Accessible (policyMatrix π) k2 j := hj k2 (uni_acc_mono _ _ hedge hjk2)
  exact Relation.ReflTransGen.trans a1 a2

end KallenbergLP.Constrained

open KallenbergLP.Constrained
open MarkovDecisionProcesses

theorem solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] (M : StationaryMDP S A) (hM : IsUnichain M)
    (π : KallenbergLP.AverageLP.Pair M → ℝ) (hπ : π ∈ StatRule M) :
    IsUnichainMatrix (policyMatrix π) := by
  exact unichain_core M hM π hπ
