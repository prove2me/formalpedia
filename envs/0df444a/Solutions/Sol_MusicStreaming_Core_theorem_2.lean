-- Prove2me | solution 1 for MusicStreaming.Core.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-15T17:37:37.241889+00:00
-- url     : https://prove2.me/submissions/fb9f396e-9edc-465f-b2a5-8ed671c85a59

import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MusicStreaming_Core_Setting

namespace MusicStreaming.Core.MusicAux

open Finset

variable {n : ℕ}

/-- Weighted supply-demand feasibility condition. -/
def Cond (M : Finset ℕ) (L : ℕ → Finset (Fin n)) (w : ℕ → ℝ) (x : Fin n → ℝ) : Prop :=
  (∀ j ∈ M, 0 ≤ w j) ∧ (∑ i, x i = ∑ j ∈ M, w j) ∧
    ∀ S : Finset (Fin n), ∑ j ∈ M.filter (fun j => L j ⊆ S), w j ≤ ∑ i ∈ S, x i

/-- A decomposition of `x` into nonnegative user vectors supported on `L j` with mass `w j`. -/
def Sol (M : Finset ℕ) (L : ℕ → Finset (Fin n)) (w : ℕ → ℝ) (x : Fin n → ℝ) : Prop :=
  ∃ y : ℕ → Fin n → ℝ, (∀ j ∈ M, (∀ i, i ∉ L j → y j i = 0) ∧ (∀ i, 0 ≤ y j i) ∧
    ∑ i, y j i = w j) ∧ x = ∑ j ∈ M, y j

def mu (M : Finset ℕ) (L : ℕ → Finset (Fin n)) : ℕ := ∑ j ∈ M, ((L j).card + 1)

lemma x_nonneg {M : Finset ℕ} {L : ℕ → Finset (Fin n)} {w : ℕ → ℝ} {x : Fin n → ℝ}
    (h : Cond M L w x) (i : Fin n) : 0 ≤ x i := by
  have h1 := h.2.2 {i}
  have h2 : 0 ≤ ∑ j ∈ M.filter (fun j => L j ⊆ {i}), w j :=
    sum_nonneg (fun j hj => h.1 j (mem_filter.1 hj).1)
  have h3 := h2.trans h1
  simpa using h3

lemma sol_empty {L : ℕ → Finset (Fin n)} {w : ℕ → ℝ} {x : Fin n → ℝ}
    (h : Cond ∅ L w x) : Sol ∅ L w x := by
  refine ⟨0, by simp, ?_⟩
  have hs : ∑ i, x i = 0 := by simpa using h.2.1
  have := (sum_eq_zero_iff_of_nonneg (fun i _ => x_nonneg h i)).1 hs
  funext i
  simp [this i]

lemma dropCond {M : Finset ℕ} {L : ℕ → Finset (Fin n)} {w : ℕ → ℝ} {x : Fin n → ℝ}
    {j0 : ℕ} (h : Cond M L w x) (hw : w j0 = 0) : Cond (M.erase j0) L w x := by
  refine ⟨fun j hj => h.1 j (mem_of_mem_erase hj), ?_, fun S => ?_⟩
  · rw [sum_erase _ hw]; exact h.2.1
  · rw [filter_erase, sum_erase _ hw]; exact h.2.2 S

lemma dropSol {M : Finset ℕ} {L : ℕ → Finset (Fin n)} {w : ℕ → ℝ} {x : Fin n → ℝ}
    {j0 : ℕ} (hw : w j0 = 0) (h : Sol (M.erase j0) L w x) : Sol M L w x := by
  obtain ⟨y, hy, hx⟩ := h
  refine ⟨fun j => if j = j0 then 0 else y j, fun j hj => ?_, ?_⟩
  · by_cases hj0 : j = j0
    · subst hj0; simp [hw]
    · simp only [hj0, if_false]
      exact hy j (mem_erase.2 ⟨hj0, hj⟩)
  · rw [← sum_erase (f := fun j => if j = j0 then (0 : Fin n → ℝ) else y j) (a := j0) M (by simp), hx]
    refine sum_congr rfl (fun j hj => ?_)
    rw [if_neg (ne_of_mem_erase hj)]

lemma moveCond {M : Finset ℕ} {L : ℕ → Finset (Fin n)} {w : ℕ → ℝ} {x : Fin n → ℝ}
    {j0 : ℕ} {i0 : Fin n} {δ : ℝ} (h : Cond M L w x) (hj0 : j0 ∈ M) (hi0 : i0 ∈ L j0)
    (hδ : 0 ≤ δ) (hδw : δ ≤ w j0)
    (hgap : ∀ S : Finset (Fin n), i0 ∈ S → ¬ L j0 ⊆ S →
      δ ≤ ∑ i ∈ S, x i - ∑ j ∈ M.filter (fun j => L j ⊆ S), w j) :
    Cond M L (w - Pi.single j0 δ) (x - Pi.single i0 δ) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun j hj => ?_, ?_, fun S => ?_⟩
  · by_cases hjj : j = j0
    · subst hjj; simp; linarith
    · simp [hjj, h1 j hj]
  · simp only [Pi.sub_apply, sum_sub_distrib, sum_pi_single', mem_univ, if_true, hj0, h2]
  · simp only [Pi.sub_apply, sum_sub_distrib, sum_pi_single', mem_filter]
    have hS := h3 S
    by_cases hiS : i0 ∈ S
    · by_cases hLS : L j0 ⊆ S
      · simp only [hiS, hLS, hj0, and_self, if_true]; linarith
      · have := hgap S hiS hLS
        simp only [hiS, hLS, and_false, if_true, if_false]; linarith
    · have hLS : ¬ L j0 ⊆ S := fun hh => hiS (hh hi0)
      simp only [hiS, hLS, and_false, if_false]; linarith

lemma moveSol {M : Finset ℕ} {L : ℕ → Finset (Fin n)} {w : ℕ → ℝ} {x : Fin n → ℝ}
    {j0 : ℕ} {i0 : Fin n} {δ : ℝ} (hj0 : j0 ∈ M) (hi0 : i0 ∈ L j0) (hδ : 0 ≤ δ)
    (h : Sol M L (w - Pi.single j0 δ) (x - Pi.single i0 δ)) : Sol M L w x := by
  obtain ⟨y, hy, hx⟩ := h
  refine ⟨y + Pi.single j0 (Pi.single i0 δ), fun j hj => ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hy j hj
    by_cases hjj : j = j0
    · subst hjj
      refine ⟨fun i hi => ?_, fun i => ?_, ?_⟩
      · have : i ≠ i0 := fun e => hi (e ▸ hi0)
        simp [h1 i hi, this]
      · by_cases hii : i = i0
        · subst hii; simp; linarith [h2 i]
        · simp [hii, h2 i]
      · simp only [Pi.add_apply, Pi.single_eq_same, sum_add_distrib, h3, sum_pi_single',
          mem_univ, if_true, Pi.sub_apply]
        ring
    · refine ⟨fun i hi => ?_, fun i => ?_, ?_⟩
      · simp [hjj, h1 i hi]
      · simp [hjj, h2 i]
      · simp [hjj, h3]
  · simp only [Pi.add_apply]
    rw [sum_add_distrib, sum_pi_single', if_pos hj0, ← hx]
    simp

/-- The first piece of a split along a tight set `T`. -/
lemma splitCond1 {M : Finset ℕ} {L : ℕ → Finset (Fin n)} {w : ℕ → ℝ} {x : Fin n → ℝ}
    {T : Finset (Fin n)} (h : Cond M L w x)
    (ht : ∑ i ∈ T, x i = ∑ j ∈ M.filter (fun j => L j ⊆ T), w j) :
    Cond (M.filter (fun j => L j ⊆ T)) L w (fun i => if i ∈ T then x i else 0) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun j hj => h1 j (mem_filter.1 hj).1, ?_, fun S => ?_⟩
  · rw [sum_ite_mem, univ_inter, ht]
  · rw [sum_ite_mem, filter_filter]
    have : M.filter (fun j => L j ⊆ T ∧ L j ⊆ S) = M.filter (fun j => L j ⊆ S ∩ T) := by
      apply filter_congr
      intro j _
      rw [subset_inter_iff, and_comm]
    rw [this]
    exact h3 _

lemma splitCond2 {M : Finset ℕ} {L : ℕ → Finset (Fin n)} {w : ℕ → ℝ} {x : Fin n → ℝ}
    {T : Finset (Fin n)} (h : Cond M L w x)
    (ht : ∑ i ∈ T, x i = ∑ j ∈ M.filter (fun j => L j ⊆ T), w j) :
    Cond (M.filter (fun j => ¬ L j ⊆ T)) (fun j => L j \ T) w
      (fun i => x i - if i ∈ T then x i else 0) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun j hj => h1 j (mem_filter.1 hj).1, ?_, fun S => ?_⟩
  · rw [sum_sub_distrib, sum_ite_mem, univ_inter, ht, h2,
      ← sum_filter_add_sum_filter_not M (fun j => L j ⊆ T)]
    ring
  · rw [sum_sub_distrib, sum_ite_mem]
    have hsplit := sum_filter_add_sum_filter_not (M.filter (fun j => L j ⊆ S ∪ T))
      (fun j => L j ⊆ T) w
    have e1 : (M.filter (fun j => L j ⊆ S ∪ T)).filter (fun j => L j ⊆ T)
        = M.filter (fun j => L j ⊆ T) := by
      ext j
      simp only [mem_filter]
      constructor
      · rintro ⟨⟨hj, _⟩, h'⟩; exact ⟨hj, h'⟩
      · rintro ⟨hj, h'⟩; exact ⟨⟨hj, h'.trans subset_union_right⟩, h'⟩
    have e2 : (M.filter (fun j => L j ⊆ S ∪ T)).filter (fun j => ¬ L j ⊆ T)
        = (M.filter (fun j => ¬ L j ⊆ T)).filter (fun j => L j \ T ⊆ S) := by
      ext j
      have key : L j \ T ⊆ S ↔ L j ⊆ S ∪ T := by
        simp only [subset_iff, mem_sdiff, mem_union]
        constructor
        · intro hh a ha
          by_cases haT : a ∈ T
          · exact Or.inr haT
          · exact Or.inl (hh ⟨ha, haT⟩)
        · intro hh a ⟨ha, haT⟩
          rcases hh ha with h' | h'
          · exact h'
          · exact absurd h' haT
      simp only [mem_filter, key]
      tauto
    rw [e1, e2] at hsplit
    have hU := h3 (S ∪ T)
    have hui := sum_union_inter (s₁ := S) (s₂ := T) (f := x)
    linarith

lemma splitSol {M : Finset ℕ} {L : ℕ → Finset (Fin n)} {w : ℕ → ℝ} {x : Fin n → ℝ}
    {T : Finset (Fin n)}
    (h1 : Sol (M.filter (fun j => L j ⊆ T)) L w (fun i => if i ∈ T then x i else 0))
    (h2 : Sol (M.filter (fun j => ¬ L j ⊆ T)) (fun j => L j \ T) w
      (fun i => x i - if i ∈ T then x i else 0)) : Sol M L w x := by
  obtain ⟨y1, hy1, hx1⟩ := h1
  obtain ⟨y2, hy2, hx2⟩ := h2
  refine ⟨fun j => if L j ⊆ T then y1 j else y2 j, fun j hj => ?_, ?_⟩
  · by_cases hjT : L j ⊆ T
    · simp only [hjT, if_true]
      exact hy1 j (mem_filter.2 ⟨hj, hjT⟩)
    · simp only [hjT, if_false]
      obtain ⟨a, b, c⟩ := hy2 j (mem_filter.2 ⟨hj, hjT⟩)
      refine ⟨fun i hi => a i (fun hh => hi (mem_sdiff.1 hh).1), b, c⟩
  · rw [← sum_filter_add_sum_filter_not M (fun j => L j ⊆ T)]
    have e1 : ∑ j ∈ M.filter (fun j => L j ⊆ T), (if L j ⊆ T then y1 j else y2 j)
        = ∑ j ∈ M.filter (fun j => L j ⊆ T), y1 j :=
      sum_congr rfl (fun j hj => if_pos (mem_filter.1 hj).2)
    have e2 : ∑ j ∈ M.filter (fun j => ¬ L j ⊆ T), (if L j ⊆ T then y1 j else y2 j)
        = ∑ j ∈ M.filter (fun j => ¬ L j ⊆ T), y2 j :=
      sum_congr rfl (fun j hj => if_neg (mem_filter.1 hj).2)
    rw [e1, e2, ← hx1, ← hx2]
    funext i
    simp

theorem main (k : ℕ) : ∀ (M : Finset ℕ) (L : ℕ → Finset (Fin n)) (w : ℕ → ℝ)
    (x : Fin n → ℝ), mu M L = k → Cond M L w x → Sol M L w x := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro M L w x hk h
  subst hk
  rcases M.eq_empty_or_nonempty with rfl | ⟨j0, hj0⟩
  · exact sol_empty h
  have muErase : mu (M.erase j0) L < mu M L := by
    unfold mu; exact sum_erase_lt_of_pos hj0 (Nat.succ_pos _)
  rcases (L j0).eq_empty_or_nonempty with hL | ⟨i0, hi0⟩
  · have hw : w j0 = 0 := by
      have h1 := h.2.2 ∅
      have h2 := single_le_sum (f := w) (s := M.filter (fun j => L j ⊆ ∅))
        (fun j hj => h.1 j (mem_filter.1 hj).1) (mem_filter.2 ⟨hj0, by simp [hL]⟩)
      have := h.1 j0 hj0
      simp only [sum_empty] at h1
      linarith
    exact dropSol hw (ih _ muErase _ L w x rfl (dropCond h hw))
  by_cases hall : ∀ S : Finset (Fin n), i0 ∈ S → ¬ L j0 ⊆ S →
      w j0 ≤ ∑ i ∈ S, x i - ∑ j ∈ M.filter (fun j => L j ⊆ S), w j
  · have hc := moveCond h hj0 hi0 (h.1 j0 hj0) le_rfl hall
    have hw0 : ((w - Pi.single j0 (w j0) : ℕ → ℝ) j0) = 0 := by simp
    apply moveSol hj0 hi0 (h.1 j0 hj0)
    exact dropSol hw0 (ih _ muErase _ L _ _ rfl (dropCond hc hw0))
  · push Not at hall
    obtain ⟨S1, hS1i, hS1L, hS1g⟩ := hall
    let gap : Finset (Fin n) → ℝ :=
      fun S => ∑ i ∈ S, x i - ∑ j ∈ M.filter (fun j => L j ⊆ S), w j
    let F := (univ : Finset (Finset (Fin n))).filter (fun S => i0 ∈ S ∧ ¬ L j0 ⊆ S)
    have hF : F.Nonempty := ⟨S1, by simp [F, hS1i, hS1L]⟩
    obtain ⟨T, hTF, hTmin⟩ := F.exists_min_image gap hF
    simp only [F, mem_filter, mem_univ, true_and] at hTF hTmin
    have hδ0 : 0 ≤ gap T := by simp only [gap]; linarith [h.2.2 T]
    have hδw : gap T < w j0 := lt_of_le_of_lt (hTmin S1 ⟨hS1i, hS1L⟩) hS1g
    have hc := moveCond h hj0 hi0 hδ0 hδw.le (fun S h1 h2 => hTmin S ⟨h1, h2⟩)
    apply moveSol hj0 hi0 hδ0
    set w' := w - Pi.single j0 (gap T) with hw'
    set x' := x - Pi.single i0 (gap T) with hx'
    have htight : ∑ i ∈ T, x' i = ∑ j ∈ M.filter (fun j => L j ⊆ T), w' j := by
      simp only [hw', hx', Pi.sub_apply, sum_sub_distrib, sum_pi_single', mem_filter, hTF.1,
        hTF.2, and_false, if_true, if_false, gap]
      ring
    have hm1 : mu (M.filter (fun j => L j ⊆ T)) L < mu M L := by
      unfold mu
      exact sum_lt_sum_of_subset (filter_subset _ _) hj0
        (fun hh => hTF.2 (mem_filter.1 hh).2) (Nat.succ_pos _) (fun _ _ _ => Nat.zero_le _)
    have hm2 : mu (M.filter (fun j => ¬ L j ⊆ T)) (fun j => L j \ T) < mu M L := by
      unfold mu
      calc ∑ j ∈ M.filter (fun j => ¬ L j ⊆ T), ((L j \ T).card + 1)
          < ∑ j ∈ M.filter (fun j => ¬ L j ⊆ T), ((L j).card + 1) := by
            apply sum_lt_sum
            · intro j _
              have := card_le_card (sdiff_subset (s := L j) (t := T))
              omega
            · refine ⟨j0, mem_filter.2 ⟨hj0, hTF.2⟩, ?_⟩
              have : L j0 \ T ⊂ L j0 :=
                (ssubset_iff_of_subset sdiff_subset).2 ⟨i0, hi0, fun hh => (mem_sdiff.1 hh).2 hTF.1⟩
              have := card_lt_card this
              omega
        _ ≤ ∑ j ∈ M, ((L j).card + 1) :=
            sum_le_sum_of_subset (filter_subset _ _)
    exact splitSol (ih _ hm1 _ _ _ _ rfl (splitCond1 hc htight))
      (ih _ hm2 _ _ _ _ rfl (splitCond2 hc htight))

end MusicStreaming.Core.MusicAux

namespace MusicStreaming.Core

open Finset MusicStreaming.Core.MusicAux

theorem theorem_2 {n : ℕ} (t : MusicStreaming.Axioms.Problem n) :
    Supermodularity.Cooperative.Core Finset.univ (game t) = allocSet t := by
  ext x
  simp only [Supermodularity.Cooperative.Core, Set.mem_setOf_eq, allocSet]
  constructor
  · rintro ⟨hsum, hS⟩
    have hc : Cond t.support (MusicStreaming.Axioms.listened t) (fun _ => (1 : ℝ)) x := by
      refine ⟨fun _ _ => zero_le_one, ?_, fun S => ?_⟩
      · rw [hsum]
        simp [game]
      · have := hS S (subset_univ _)
        simp only [game] at this
        simpa using this
    obtain ⟨y, hy, hx⟩ := main _ _ _ _ _ rfl hc
    exact ⟨y, fun j hj => ⟨(hy j hj).1, fun i _ => (hy j hj).2.1 i, (hy j hj).2.2⟩, hx⟩
  · rintro ⟨y, hy, rfl⟩
    have hnn : ∀ j ∈ t.support, ∀ i, 0 ≤ y j i := by
      intro j hj i
      by_cases hi : i ∈ MusicStreaming.Axioms.listened t j
      · exact (hy j hj).2.1 i hi
      · rw [(hy j hj).1 i hi]
    have key : ∀ S : Finset (Fin n), ∑ i ∈ S, (∑ j ∈ t.support, y j) i
        = ∑ j ∈ t.support, ∑ i ∈ S, y j i := by
      intro S
      simp only [Finset.sum_apply]
      exact Finset.sum_comm
    refine ⟨?_, fun S _ => ?_⟩
    · rw [key]
      simp only [game, subset_univ, filter_true_of_mem (fun _ _ => subset_univ _)]
      rw [sum_congr rfl (fun j hj => (hy j hj).2.2)]
      simp
    · rw [key]
      simp only [game]
      have hfull : ∀ j ∈ t.support.filter (fun j => MusicStreaming.Axioms.listened t j ⊆ S),
          ∑ i ∈ S, y j i = 1 := by
        intro j hj
        obtain ⟨hj, hjS⟩ := mem_filter.1 hj
        rw [← (hy j hj).2.2]
        refine sum_subset (subset_univ _) (fun i _ hiS => (hy j hj).1 i (fun hh => hiS (hjS hh)))
      calc (((t.support.filter (fun j => MusicStreaming.Axioms.listened t j ⊆ S)).card : ℕ) : ℝ)
          = ∑ j ∈ t.support.filter (fun j => MusicStreaming.Axioms.listened t j ⊆ S),
              ∑ i ∈ S, y j i := by
            rw [sum_congr rfl hfull]; simp
        _ ≤ ∑ j ∈ t.support, ∑ i ∈ S, y j i :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
              (fun j hj _ => sum_nonneg (fun i _ => hnn j hj i))

end MusicStreaming.Core


-- Platform entry point: restates the target verbatim.
namespace MusicStreaming.Core

/-- **Theorem 2** (p. 14). For every streaming problem `t`, the core `C(N, v)` of the streaming
game `v(S) = |{j ∈ M : L^j ⊆ S}|` equals the set `A(N, M, t)` of allocations that split each
user's payment of `1` among the artists that user played. -/
theorem _root_.solution {n : ℕ} (t : MusicStreaming.Axioms.Problem n) :
    Supermodularity.Cooperative.Core Finset.univ (game t) = allocSet t := by
  apply @MusicStreaming.Core.theorem_2 <;> assumption

end MusicStreaming.Core
