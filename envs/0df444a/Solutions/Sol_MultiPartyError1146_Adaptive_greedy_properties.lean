-- Prove2me | solution 1 for MultiPartyError1146.Adaptive.greedy_properties
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:36:50.508702+00:00
-- url     : https://prove2.me/submissions/b8a859dc-4a73-4d90-ad43-f096d7fed0d7

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Attack

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MultiPartyError1146.Adaptive

lemma greedyStep_cases {n T : ℕ} (P : Protocol n 1 T) (k : ℕ)
    (z : GreedyState n T) :
    greedyStep P k z = z ∨
      ∃ i b, i ∉ z.chosen ∧
        (T : ℝ) / k < (intersectionSize P z i b : ℝ) ∧
        greedyStep P k z =
          ⟨insert i z.chosen, Function.update z.input i b,
            fun t => if t ∈ silentSpeaking P i b then z.copies t - 1 else z.copies t⟩ := by
  classical
  unfold greedyStep
  dsimp only
  split
  · left
    rfl
  · right
    rename_i i b hfind
    have hp := List.find?_some hfind
    simp only [decide_eq_true_eq] at hp
    exact ⟨i, b, hp.1, hp.2, rfl⟩

lemma terminated_of_greedyStep_eq {n T : ℕ} (P : Protocol n 1 T) (k : ℕ)
    (z : GreedyState n T) (hz : greedyStep P k z = z) (i : Fin n) (b : Bool)
    (hi : i ∉ z.chosen) : ¬ (T : ℝ) / k < (intersectionSize P z i b : ℝ) := by
  classical
  intro hlarge
  unfold greedyStep at hz
  dsimp only at hz
  split at hz
  · rename_i hfind
    have hmem : (i, b) ∈ (List.finRange n).flatMap
        (fun i => [(i, false), (i, true)]) := by
      cases b <;> simp
    have hn := List.find?_eq_none.mp hfind (i, b) hmem
    simp [hi, hlarge] at hn
  · rename_i i' b' hfind
    have hp := List.find?_some hfind
    simp only [decide_eq_true_eq] at hp
    have hchosen := congrArg GreedyState.chosen hz
    apply hp.1
    rw [← hchosen]
    exact Finset.mem_insert_self i' z.chosen

lemma copySum_success {n T : ℕ} (P : Protocol n 1 T) (z : GreedyState n T)
    (i : Fin n) (b : Bool) :
    (∑ t : Fin T, (if t ∈ silentSpeaking P i b then z.copies t - 1 else z.copies t)) +
        intersectionSize P z i b = ∑ t : Fin T, z.copies t := by
  classical
  unfold intersectionSize
  calc
    (∑ t : Fin T, (if t ∈ silentSpeaking P i b then z.copies t - 1 else z.copies t)) +
          ∑ t ∈ silentSpeaking P i b, min 1 (z.copies t) =
        ∑ t : Fin T, ((if t ∈ silentSpeaking P i b then z.copies t - 1 else z.copies t) +
          if t ∈ silentSpeaking P i b then min 1 (z.copies t) else 0) := by
      rw [Finset.sum_add_distrib]
      congr 1
      symm
      calc
        (∑ t : Fin T, if t ∈ silentSpeaking P i b then min 1 (z.copies t) else 0) =
            ∑ t ∈ Finset.univ ∩ silentSpeaking P i b, min 1 (z.copies t) :=
          Finset.sum_ite_mem Finset.univ (silentSpeaking P i b) (fun t => min 1 (z.copies t))
        _ = ∑ t ∈ silentSpeaking P i b, min 1 (z.copies t) := by simp
    _ = ∑ t : Fin T, z.copies t := by
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hs : t ∈ silentSpeaking P i b
      · simp only [hs, if_true]
        by_cases hz : z.copies t = 0
        · simp [hz]
        · have hp : 0 < z.copies t := Nat.pos_of_ne_zero hz
          have hc : 1 ≤ z.copies t := hp
          rw [min_eq_left hc]
          omega
      · simp [hs]

lemma greedy_copy_bound {n T : ℕ} (P : Protocol n 1 T) (k : ℕ)
    (hT : 0 < T) (hk : 0 < k) (j : ℕ) :
    (((∑ t : Fin T, ((greedyStep P k)^[j]
      ⟨∅, fun _ => false, fun _ => 2⟩ : GreedyState n T).copies t : ℕ) : ℝ) +
      (((greedyStep P k)^[j]
        ⟨∅, fun _ => false, fun _ => 2⟩ : GreedyState n T).chosen.card : ℝ) *
        ((T : ℝ) / k) ≤ 2 * T) ∧
      ((((greedyStep P k)^[j]
        ⟨∅, fun _ => false, fun _ => 2⟩ : GreedyState n T).chosen.card = 0) ∨
        ((∑ t : Fin T, ((greedyStep P k)^[j]
          ⟨∅, fun _ => false, fun _ => 2⟩ : GreedyState n T).copies t : ℕ) : ℝ) +
        (((greedyStep P k)^[j]
          ⟨∅, fun _ => false, fun _ => 2⟩ : GreedyState n T).chosen.card : ℝ) *
          ((T : ℝ) / k) < 2 * T) := by
  classical
  induction j with
  | zero =>
      simp
      ring_nf
      exact le_rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      let z : GreedyState n T := (greedyStep P k)^[j]
        ⟨∅, fun _ => false, fun _ => 2⟩
      change (((∑ t : Fin T, (greedyStep P k z).copies t : ℕ) : ℝ) +
        ((greedyStep P k z).chosen.card : ℝ) * ((T : ℝ) / k) ≤ 2 * T) ∧
        (((greedyStep P k z).chosen.card = 0) ∨
          ((∑ t : Fin T, (greedyStep P k z).copies t : ℕ) : ℝ) +
          ((greedyStep P k z).chosen.card : ℝ) * ((T : ℝ) / k) < 2 * T)
      rcases greedyStep_cases P k z with hz | ⟨i, b, hi, hlarge, hstep⟩
      · rw [hz]
        exact ih
      · rw [hstep]
        have hacc := copySum_success P z i b
        have hcard : (insert i z.chosen).card = z.chosen.card + 1 :=
          Finset.card_insert_of_notMem hi
        have haccR : ((∑ t : Fin T,
            (if t ∈ silentSpeaking P i b then z.copies t - 1 else z.copies t) : ℕ) : ℝ) +
            (intersectionSize P z i b : ℝ) =
            ((∑ t : Fin T, z.copies t : ℕ) : ℝ) := by
          exact_mod_cast hacc
        have hq : 0 < (T : ℝ) / k := by positivity
        have hbound := ih.1
        change ((∑ t : Fin T, z.copies t : ℕ) : ℝ) +
          (z.chosen.card : ℝ) * ((T : ℝ) / k) ≤ 2 * T at hbound
        rw [hcard, Nat.cast_add, Nat.cast_one]
        dsimp only
        change (((∑ t : Fin T,
          (if t ∈ silentSpeaking P i b then z.copies t - 1 else z.copies t) : ℕ) : ℝ) +
            ((z.chosen.card : ℝ) + 1) * ((T : ℝ) / k) ≤ 2 * T) ∧
          ((z.chosen.card + 1 = 0) ∨
            ((∑ t : Fin T,
              (if t ∈ silentSpeaking P i b then z.copies t - 1 else z.copies t) : ℕ) : ℝ) +
              ((z.chosen.card : ℝ) + 1) * ((T : ℝ) / k) < 2 * T)
        constructor
        · nlinarith
        · right
          nlinarith

lemma greedy_termination {n T : ℕ} (P : Protocol n 1 T) (k : ℕ) :
    greedyStep P k (greedy P k) = greedy P k := by
  classical
  let z0 : GreedyState n T := ⟨∅, fun _ => false, fun _ => 2⟩
  have haux : ∀ j : ℕ,
      (((greedyStep P k)^[j] z0).chosen.card = j) ∨
      greedyStep P k ((greedyStep P k)^[j] z0) = (greedyStep P k)^[j] z0 := by
    intro j
    induction j with
    | zero => left; rfl
    | succ j ih =>
        rw [Function.iterate_succ_apply']
        rcases ih with hcard | hterm
        · rcases greedyStep_cases P k ((greedyStep P k)^[j] z0) with hterm | ⟨i,b,hi,hl,hstep⟩
          · right
            rw [hterm]
            exact hterm
          · left
            rw [hstep]
            simp [Finset.card_insert_of_notMem hi, hcard]
        · right
          rw [hterm]
          exact hterm
  rcases haux n with hcard | hterm
  · have hno : ∀ i : Fin n, i ∉ (greedy P k).chosen → False := by
      intro i hi
      have huniv : (greedy P k).chosen = Finset.univ := by
        apply Finset.eq_univ_of_card
        simpa [greedy, z0] using hcard
      rw [huniv] at hi
      exact hi (Finset.mem_univ i)
    by_contra hne
    rcases greedyStep_cases P k (greedy P k) with h | ⟨i,b,hi,hl,hstep⟩
    · exact hne h
    · exact hno i hi
  · exact hterm

lemma intersectionSize_eq_card {n T : ℕ} (P : Protocol n 1 T)
    (z : GreedyState n T) (i : Fin n) (b : Bool) :
    intersectionSize P z i b =
      (silentSpeaking P i b ∩ Finset.univ.filter (fun t => 0 < z.copies t)).card := by
  classical
  unfold intersectionSize
  have hset : silentSpeaking P i b ∩ Finset.univ.filter (fun t => 0 < z.copies t) =
      (silentSpeaking P i b).filter (fun t => 0 < z.copies t) := by
    ext t
    simp
  rw [hset, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hp : 0 < z.copies t
  · have hc : 1 ≤ z.copies t := hp
    rw [if_pos hp, min_eq_left hc]
  · have hz : z.copies t = 0 := Nat.eq_zero_of_not_pos hp
    simp [hz]

lemma greedy_multiplicity {n T : ℕ} (P : Protocol n 1 T) (k : ℕ) (j : ℕ)
    (t : Fin T) :
    ((greedyStep P k)^[j]
      ⟨∅, fun _ => false, fun _ => 2⟩ : GreedyState n T).copies t +
      min 2 (∑ i ∈ ((greedyStep P k)^[j]
        ⟨∅, fun _ => false, fun _ => 2⟩ : GreedyState n T).chosen,
        if t ∈ silentSpeaking P i (((greedyStep P k)^[j]
          ⟨∅, fun _ => false, fun _ => 2⟩ : GreedyState n T).input i) then 1 else 0) = 2 := by
  classical
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      let z : GreedyState n T := (greedyStep P k)^[j]
        ⟨∅, fun _ => false, fun _ => 2⟩
      change (greedyStep P k z).copies t + min 2 (∑ i ∈ (greedyStep P k z).chosen,
        if t ∈ silentSpeaking P i ((greedyStep P k z).input i) then 1 else 0) = 2
      change z.copies t + min 2 (∑ i ∈ z.chosen,
        if t ∈ silentSpeaking P i (z.input i) then 1 else 0) = 2 at ih
      rcases greedyStep_cases P k z with hz | ⟨i,b,hi,hlarge,hstep⟩
      · rw [hz]
        exact ih
      · rw [hstep]
        simp only [Finset.sum_insert hi, Function.update_self]
        have hold : (∑ j ∈ z.chosen,
            if t ∈ silentSpeaking P j (Function.update z.input i b j) then 1 else 0) =
            ∑ j ∈ z.chosen, if t ∈ silentSpeaking P j (z.input j) then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          have hji : j ≠ i := by
            intro h
            subst j
            exact hi hj
          rw [Function.update_of_ne hji]
        change (if t ∈ silentSpeaking P i b then z.copies t - 1 else z.copies t) +
          min 2 ((if t ∈ silentSpeaking P i b then 1 else 0) +
            ∑ j ∈ z.chosen, if t ∈ silentSpeaking P j
              (Function.update z.input i b j) then 1 else 0) = 2
        rw [hold]
        by_cases ht : t ∈ silentSpeaking P i b
        · simp only [ht, if_true]
          change z.copies t - 1 + min 2 (1 + ∑ j ∈ z.chosen,
            if t ∈ silentSpeaking P j (z.input j) then 1 else 0) = 2
          change z.copies t + min 2 (∑ j ∈ z.chosen,
            if t ∈ silentSpeaking P j (z.input j) then 1 else 0) = 2 at ih
          by_cases hzero : z.copies t = 0
          · simp only [hzero, Nat.zero_sub]
            omega
          · omega
        · simpa [ht] using ih

end MultiPartyError1146.Adaptive

open MultiPartyError1146.Adaptive

theorem solution (n T k : ℕ) (hn : 1 ≤ n) (hT : 1 ≤ T)
    (hk : 1 ≤ k ∧ 2 * k < n) (P : Protocol n 1 T) :
    ∃ i : Fin n, target P k = some i ∧ i ∉ (greedy P k).chosen ∧
      (erasedParties P k).card ≤ 2 * k ∧
      (∀ b : Bool, ((silentSpeaking P i b ∩ remainingRounds P k).card : ℝ) ≤ (T : ℝ) / k) ∧
      (∀ t : Fin T, t ∉ remainingRounds P k →
        ∃ j₁ ∈ (greedy P k).chosen, ∃ j₂ ∈ (greedy P k).chosen,
          j₁ ≠ j₂ ∧ t ∈ silentSpeaking P j₁ ((greedy P k).input j₁) ∧
          t ∈ silentSpeaking P j₂ ((greedy P k).input j₂)) := by
  classical
  have hb := greedy_copy_bound P k hT hk.1 n
  change (((∑ t : Fin T, (greedy P k).copies t : ℕ) : ℝ) +
    ((greedy P k).chosen.card : ℝ) * ((T : ℝ) / k) ≤ 2 * T) ∧
    (((greedy P k).chosen.card = 0) ∨
      ((∑ t : Fin T, (greedy P k).copies t : ℕ) : ℝ) +
      ((greedy P k).chosen.card : ℝ) * ((T : ℝ) / k) < 2 * T) at hb
  have hchosen : (greedy P k).chosen.card < 2 * k := by
    rcases hb.2 with hzero | hstrict
    · rw [hzero]
      omega
    · have hsum : (0 : ℝ) ≤ ((∑ t : Fin T, (greedy P k).copies t : ℕ) : ℝ) := by positivity
      have hlt : ((greedy P k).chosen.card : ℝ) * ((T : ℝ) / k) < 2 * T := by
        nlinarith
      have hTR : (0 : ℝ) < T := by exact_mod_cast hT
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk.1
      have hq : 0 < (T : ℝ) / k := div_pos hTR hkR
      have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
      have heq : (2 * (k : ℝ)) * ((T : ℝ) / k) = 2 * (T : ℝ) := by
        field_simp [hkne]
        <;> ring
      have hreal : ((greedy P k).chosen.card : ℝ) < 2 * (k : ℝ) := by
        by_contra hnot
        have hge : 2 * (k : ℝ) ≤ ((greedy P k).chosen.card : ℝ) := le_of_not_gt hnot
        have hmul := mul_le_mul_of_nonneg_right hge hq.le
        have hle : 2 * (T : ℝ) ≤ ((greedy P k).chosen.card : ℝ) * ((T : ℝ) / k) := by
          rw [← heq]
          exact hmul
        exact (not_lt_of_ge hle) hlt
      exact_mod_cast hreal
  have hex : ∃ i : Fin n, i ∉ (greedy P k).chosen := by
    by_contra h
    push_neg at h
    have huniv : (greedy P k).chosen = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      exact h
    rw [huniv] at hchosen
    simp at hchosen
    omega
  obtain ⟨i, hi⟩ := hex
  have htarget : ∃ i : Fin n, target P k = some i := by
    unfold target
    cases hf : (List.finRange n).find?
        (fun i => decide (i ∉ (greedy P k).chosen)) with
    | none =>
        have hn := List.find?_eq_none.mp hf i (List.mem_finRange i)
        simp [hi] at hn
    | some a => exact ⟨a, rfl⟩
  obtain ⟨i, ht⟩ := htarget
  have hraw : (List.finRange n).find?
      (fun i => decide (i ∉ (greedy P k).chosen)) = some i := by
    simpa [target] using ht
  have hpred := List.find?_some
    (p := fun j => decide (j ∉ (greedy P k).chosen))
    (a := i) (l := List.finRange n) hraw
  have hi : i ∉ (greedy P k).chosen := of_decide_eq_true hpred
  refine ⟨i, ht, hi, ?_, ?_, ?_⟩
  · have he : erasedParties P k = insert i (greedy P k).chosen := by
      ext j
      simp [erasedParties, ht]
    rw [he, Finset.card_insert_of_notMem hi]
    omega
  · intro b
    have hnot := terminated_of_greedyStep_eq P k (greedy P k)
      (greedy_termination P k) i b hi
    have heq : intersectionSize P (greedy P k) i b =
        (silentSpeaking P i b ∩ remainingRounds P k).card := by
      simpa [remainingRounds] using intersectionSize_eq_card P (greedy P k) i b
    rw [← heq]
    exact le_of_not_gt hnot
  · intro t ht
    have hzero : (greedy P k).copies t = 0 := by
      have hnpos : ¬ 0 < (greedy P k).copies t := by
        simpa [remainingRounds] using ht
      exact Nat.eq_zero_of_not_pos hnpos
    have hm := greedy_multiplicity P k n t
    change (greedy P k).copies t + min 2 (∑ j ∈ (greedy P k).chosen,
      if t ∈ silentSpeaking P j ((greedy P k).input j) then 1 else 0) = 2 at hm
    rw [hzero] at hm
    simp only [Nat.zero_add] at hm
    have hsum : 2 ≤ ∑ j ∈ (greedy P k).chosen,
        if t ∈ silentSpeaking P j ((greedy P k).input j) then 1 else 0 := by
      omega
    let speakers := (greedy P k).chosen.filter
      (fun j => t ∈ silentSpeaking P j ((greedy P k).input j))
    have hcard : 2 ≤ speakers.card := by
      dsimp [speakers]
      rw [Finset.card_filter]
      exact hsum
    have hlarge : 1 < speakers.card := by omega
    obtain ⟨j₁, hj₁, j₂, hj₂, hne⟩ := Finset.one_lt_card.mp hlarge
    have hj₁' := Finset.mem_filter.mp hj₁
    have hj₂' := Finset.mem_filter.mp hj₂
    exact ⟨j₁, hj₁'.1, j₂, hj₂'.1, hne, hj₁'.2, hj₂'.2⟩
