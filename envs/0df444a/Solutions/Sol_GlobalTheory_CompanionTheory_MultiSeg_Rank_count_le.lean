-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MultiSeg.Rank.count_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:42:51.071369+00:00
-- url     : https://prove2.me/submissions/e120288a-3782-47c4-8d7e-d2e0a301501a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_ZelevinskyJacquet_ZelevinskyInterleaving_Interleave
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ShuffleWeightSquareLengthLt
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_iter_inj
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_mem_word
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_dec_eq_word
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_word_nodup
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_word_split
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_con_mid
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_con_suffix
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_shuffle_split
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_shuffle_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_shuffle_unique
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_countP_le_add
import Theorems.Thm_GlobalTheory_CompanionTheory_MultiSeg_Rank_con_of_not_precedes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Zc.Comb
open Classical
universe u
namespace GlobalTheory.CompanionTheory.MultiSeg.Rank
variable {T : Type u}
private theorem exists_start_eq_iterate_of_append_eq_word {s : T → T} (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) {Γ : ASeg T} {a b : List T} {t u : T}
    {l d : ℕ} (hx : a ++ b = word s t l) (ha : ∀ y ∈ a, y ∈ Γ.dec s) (hc : Con s u d (a ++ b))
    (hv : s^[d] u ∈ a) (hu : u ∉ Γ.dec s) :
    ∃ j0, j0 ≤ d ∧ Γ.start = s^[j0 + 1] u ∧ s^[d] u ∈ Γ.dec s := by
  have itc : ∀ (m k : ℕ) (x : T), m = k → s^[m] x = s^[k] x := by
    intro m k x h
    subst h
    rfl
  obtain ⟨l', _, hb, ha0⟩ := word_split s t l a b hx.symm
  have hc' : u ∈ a ++ b ∧ s^[d] u ∈ a ++ b := hc
  have hu2 : u ∈ b := by
    rcases List.mem_append.1 hc'.1 with h | h
    · exact absurd (ha u h) hu
    · exact h
  rw [hb, mem_word] at hu2
  obtain ⟨i, hi, rfl⟩ := hu2
  obtain ⟨i', hi1, hi2, hi3⟩ := ha0 _ hv
  rw [← Function.iterate_add_apply] at hi3
  have hi' := iter_inj hs hp hi3
  have hl'a : s^[l'] t ∈ a := by
    have hin : s^[l'] t ∈ a ++ b := by
      rw [hx, mem_word]
      exact ⟨l', by omega, rfl⟩
    rcases List.mem_append.1 hin with h | h
    · exact h
    · exfalso
      rw [hb, mem_word] at h
      obtain ⟨k, hk, hk'⟩ := h
      have := iter_inj hs hp hk'
      omega
  have hmem := ha _ hl'a
  rw [dec_eq_word, mem_word] at hmem
  obtain ⟨k1, hk1, hk1'⟩ := hmem
  have hk1le : k1 + i < l' := by
    by_contra hcon
    apply hu
    rw [dec_eq_word, mem_word]
    refine ⟨k1 - (l' - i), by omega, ?_⟩
    apply hs.iterate (l' - i)
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
      show l' - i + (k1 - (l' - i)) = k1 by omega, hk1']
    exact itc _ _ _ (by omega)
  refine ⟨l' - 1 - i - k1, by omega, ?_, ha _ hv⟩
  apply hs.iterate k1
  rw [hk1', ← Function.iterate_add_apply, ← Function.iterate_add_apply]
  exact itc _ _ _ (by omega)
end GlobalTheory.CompanionTheory.MultiSeg.Rank
end

set_option autoImplicit false
open Zc.Comb
open Classical
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MultiSeg GlobalTheory.CompanionTheory.MultiSeg.Rank
variable {T : Type u}
namespace GlobalTheory.CompanionTheory.MultiSeg.Rank
theorem _root_.solution (s : T → T) (hs : Function.Injective s)
    (hp : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) : ∀ (B : List (ASeg T)),
    B.Pairwise (fun a b => ¬ APrecedes s b a) →
    ∀ (us : List (List T)), Shuffle us (B.map (ASeg.dec s)).flatten →
    (∀ x ∈ us, ∃ t l, x = word s t l) → ∀ (u : T) (d : ℕ),
    us.countP (fun x => decide (Con s u d x)) ≤
      B.countP (fun Γ => decide (Con s u d (Γ.dec s))) := by
  intro B
  induction B with
  | nil =>
    intro _ us hus _ u d
    have h0 : us.countP (fun x => decide (Con s u d x)) = 0 := by
      rw [List.countP_eq_zero]
      intro x hx hc
      have hc0 : Con s u d x := of_decide_eq_true hc
      have hc' : u ∈ x ∧ s^[d] u ∈ x := hc0
      have := shuffle_mem hus hx hc'.1
      simp at this
    rw [h0]
    exact Nat.zero_le _
  | cons Γ1 rest ih =>
    intro hB us hus hw u d
    obtain ⟨hB1, hB2⟩ := List.pairwise_cons.1 hB
    obtain ⟨P, hPus, hP1, hP2⟩ :=
      shuffle_split us (Γ1.dec s) ((rest.map (ASeg.dec s)).flatten) hus
    subst hPus
    have hwP : ∀ p ∈ P, ∃ t l, p.1 ++ p.2 = word s t l := by
      intro p hpm
      obtain ⟨t, l, h⟩ := hw _ (List.mem_map.2 ⟨p, hpm, rfl⟩)
      exact ⟨t, l, h⟩
    have hsnd : ∀ x ∈ P.map Prod.snd, ∃ t l, x = word s t l := by
      intro x hx
      obtain ⟨p, hpm, rfl⟩ := List.mem_map.1 hx
      obtain ⟨t, l, h⟩ := hwP p hpm
      obtain ⟨l', _, hb, _⟩ := word_split s t l p.1 p.2 h.symm
      exact ⟨t, l', hb⟩
    have h2 : ∀ e, P.countP (fun p => decide (Con s u e p.2)) ≤
        rest.countP (fun Γ => decide (Con s u e (Γ.dec s))) := by
      intro e
      have := ih hB2 (P.map Prod.snd) hP2 hsnd u e
      rw [List.countP_map] at this
      exact this
    have hfst : ∀ p ∈ P, ∀ y ∈ p.1, y ∈ Γ1.dec s := fun p hpm y hy =>
      shuffle_mem hP1 (List.mem_map.2 ⟨p, hpm, rfl⟩) hy
    have hnd1 : (Γ1.dec s).Nodup := by
      rw [dec_eq_word]
      exact word_nodup hs hp _ _
    have hRle : rest.countP (fun Γ => decide (Con s u d (Γ.dec s))) ≤
        (Γ1 :: rest).countP (fun Γ => decide (Con s u d (Γ.dec s))) := by
      rw [List.countP_cons]
      exact Nat.le_add_right _ _
    rw [List.countP_map]
    by_cases hΓ : Con s u d (Γ1.dec s)
    · have huniq : P.countP (fun p => decide (s^[d] u ∈ p.1)) ≤ 1 := by
        have := shuffle_unique hP1 hnd1 (s^[d] u)
        rw [List.countP_map] at this
        exact this
      have h1 : P.countP (fun p => decide (Con s u d (p.1 ++ p.2))) ≤
          P.countP (fun p => decide (Con s u d p.2)) +
            P.countP (fun p => decide (s^[d] u ∈ p.1)) := by
        apply countP_le_add
        intro p hpm hc
        by_cases hv : s^[d] u ∈ p.1
        · exact Or.inr (decide_eq_true hv)
        · left
          obtain ⟨t, l, hx⟩ := hwP p hpm
          exact decide_eq_true (con_suffix hs hp hx (of_decide_eq_true hc) hv)
      have hR : rest.countP (fun Γ => decide (Con s u d (Γ.dec s))) + 1 =
          (Γ1 :: rest).countP (fun Γ => decide (Con s u d (Γ.dec s))) := by
        rw [List.countP_cons_of_pos]
        exact decide_eq_true hΓ
      have h2d := h2 d
      refine le_trans h1 ?_
      rw [← hR]
      omega
    · by_cases hj : ∃ j0, j0 ≤ d ∧ Γ1.start = s^[j0 + 1] u ∧ s^[d] u ∈ Γ1.dec s
      · obtain ⟨j0, hj0d, hst, hvΓ⟩ := hj
        have notin : ∀ e, e ≤ j0 → s^[e] u ∉ Γ1.dec s := by
          intro e he h
          rw [dec_eq_word, mem_word, hst] at h
          obtain ⟨k, _, hk⟩ := h
          rw [← Function.iterate_add_apply] at hk
          have := iter_inj hs hp hk
          omega
        have hu1 : u ∉ Γ1.dec s := notin 0 (Nat.zero_le _)
        have step1 : P.countP (fun p => decide (Con s u d (p.1 ++ p.2))) ≤
            P.countP (fun p => decide (Con s u j0 p.2)) := by
          apply List.countP_mono_left
          intro p hpm hc
          obtain ⟨t, l, hx⟩ := hwP p hpm
          have hc1 : Con s u d (p.1 ++ p.2) := of_decide_eq_true hc
          have hcj : Con s u j0 (p.1 ++ p.2) := by
            rw [hx] at hc1 ⊢
            exact con_mid hs hp hc1 hj0d
          exact decide_eq_true
            (con_suffix hs hp hx hcj (fun h => notin j0 le_rfl (hfst p hpm _ h)))
        have step3 : rest.countP (fun Γ => decide (Con s u j0 (Γ.dec s))) ≤
            rest.countP (fun Γ => decide (Con s u d (Γ.dec s))) := by
          apply List.countP_mono_left
          intro Θ hΘ hc
          exact decide_eq_true
            (con_of_not_precedes hs hp hst hu1 hvΓ (of_decide_eq_true hc) (hB1 Θ hΘ))
        exact le_trans (step1.trans ((h2 j0).trans step3)) hRle
      · have step : P.countP (fun p => decide (Con s u d (p.1 ++ p.2))) ≤
            P.countP (fun p => decide (Con s u d p.2)) := by
          apply List.countP_mono_left
          intro p hpm hc
          obtain ⟨t, l, hx⟩ := hwP p hpm
          have hc1 : Con s u d (p.1 ++ p.2) := of_decide_eq_true hc
          refine decide_eq_true (con_suffix hs hp hx hc1 ?_)
          intro hv
          have hu : u ∉ Γ1.dec s := fun hu =>
            hΓ (show u ∈ Γ1.dec s ∧ s^[d] u ∈ Γ1.dec s from ⟨hu, hfst p hpm _ hv⟩)
          exact hj (exists_start_eq_iterate_of_append_eq_word hs hp hx (hfst p hpm) hc1 hv hu)
        exact le_trans (step.trans (h2 d)) hRle
end GlobalTheory.CompanionTheory.MultiSeg.Rank
