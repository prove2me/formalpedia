-- Prove2me | solution 1 for MNLStability.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:01:51.367999+00:00
-- url     : https://prove2.me/submissions/2463b643-74e9-4d8f-aa80-d1c159ce1e34

import Mathlib
import Definitions.Def_MNLStability_IsLaw
import Definitions.Def_MNLStability_expX
import Definitions.Def_MNLStability_opt
import Definitions.Def_MNLStability_IsPriceOrder
import Definitions.Def_MNLStability_IsSpaced
import Definitions.Def_MNLStability_Lam
import Definitions.Def_MNLStability_greedyLengths

namespace Aux_MNL8
open MNLStability

variable {n : ℕ}

lemma find_range (p : ℕ → Bool) (m : ℕ) (hm : p m = true) : ∀ N, m < N →
    ∃ k, (List.range N).find? p = some k ∧ k ≤ m := by
  intro N
  induction N with
  | zero => intro h; omega
  | succ N ih =>
    intro h
    rw [List.range_succ, List.find?_append]
    by_cases hmN : m < N
    · obtain ⟨k, hk, hkm⟩ := ih hmN
      exact ⟨k, by simp [hk], hkm⟩
    · have hmeq : m = N := by omega
      cases hf : (List.range N).find? p with
      | none =>
        refine ⟨N, ?_, by omega⟩
        subst hmeq
        simp [List.find?, hm]
      | some k =>
        refine ⟨k, by simp, ?_⟩
        have := List.mem_of_find?_eq_some hf
        rw [List.mem_range] at this
        omega

lemma leastPrefix_le (rs : List ℝ) (τ : ℝ) (m : ℕ) (hm : m ≤ rs.length)
    (hτ : τ ≤ (rs.take m).sum) : ∃ k, leastPrefix rs τ = some k ∧ k ≤ m := by
  unfold leastPrefix
  exact find_range _ m (decide_eq_true hτ) _ (by omega)

lemma take_sum_tail (ys : List ℝ) (hys : ys.Pairwise (fun a b => b ≤ a)) :
    ∀ m, m < ys.length → (ys.tail.take m).sum ≤ (ys.take m).sum := by
  induction ys with
  | nil => intro m h; simp at h
  | cons a t ih =>
    intro m hm
    rw [List.pairwise_cons] at hys
    cases m with
    | zero => simp
    | succ m =>
      cases t with
      | nil => simp at hm
      | cons b t' =>
        have hab : b ≤ a := hys.1 b (by simp)
        have h1 := ih hys.2 m (by simp only [List.length_cons] at hm ⊢; omega)
        simp only [List.tail_cons] at h1
        simp only [List.tail_cons, List.take_succ_cons, List.sum_cons]
        linarith

lemma drop_take_mono (xs : List ℝ) (hxs : xs.Pairwise (fun a b => b ≤ a)) (m s : ℕ) :
    ∀ d, s + d + m ≤ xs.length →
      ((xs.drop (s + d)).take m).sum ≤ ((xs.drop s).take m).sum := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro h
    have h1 := ih (by omega)
    have h2 : ((xs.drop (s + (d + 1))).take m).sum ≤ ((xs.drop (s + d)).take m).sum := by
      have hp : (xs.drop (s + d)).Pairwise (fun a b => b ≤ a) :=
        hxs.sublist (List.drop_sublist _ _)
      have := take_sum_tail (xs.drop (s + d)) hp m (by rw [List.length_drop]; omega)
      rwa [List.tail_drop, show s + d + 1 = s + (d + 1) by omega] at this
    linarith

lemma count_le (p q s : Fin n → Bool) (hpq : ∀ x, p x = true → q x = true → False)
    (hs : ∀ x, p x = true ∨ q x = true → s x = true) : ∀ L : List (Fin n),
    (L.filter p).length + (L.filter q).length ≤ (L.filter s).length
  | [] => by simp
  | a :: L => by
    have ih := count_le p q s hpq hs L
    have h1 := hpq a
    have h2 := hs a
    simp only [List.filter_cons]
    split_ifs <;> (try simp only [List.length_cons]) <;> first | omega | (exfalso; tauto)

lemma decomp (U : Fin n → ℕ) (h : ℕ) : ∀ L : List (Fin n), L.Pairwise (fun i j => U j ≤ U i) →
    L.filter (fun i => h < U i) ++ (L.filter (fun i => U i = h) ++ L.filter (fun i => U i < h))
      = L
  | [], _ => rfl
  | a :: L, hL => by
    rw [List.pairwise_cons] at hL
    have ih := decomp U h L hL.2
    have hle : ∀ b ∈ L, U b ≤ U a := hL.1
    rcases lt_trichotomy h (U a) with h1 | h1 | h1
    · have e1 : ¬ U a = h := by omega
      have e2 : ¬ U a < h := by omega
      rw [List.filter_cons_of_pos (p := fun i => decide (h < U i)) (a := a) (l := L)
          (by simpa using h1),
        List.filter_cons_of_neg (p := fun i => decide (U i = h)) (a := a) (l := L)
          (by simpa using e1),
        List.filter_cons_of_neg (p := fun i => decide (U i < h)) (a := a) (l := L)
          (by simpa using e2),
        List.cons_append, ih]
    · have e0 : ¬ h < U a := by omega
      have e2 : ¬ U a < h := by omega
      have hP : L.filter (fun i => h < U i) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb
        have := hle b hb
        simp only [decide_eq_true_eq]
        omega
      rw [List.filter_cons_of_neg (p := fun i => decide (h < U i)) (a := a) (l := L)
          (by simpa using e0),
        List.filter_cons_of_pos (p := fun i => decide (U i = h)) (a := a) (l := L)
          (by simpa using h1.symm),
        List.filter_cons_of_neg (p := fun i => decide (U i < h)) (a := a) (l := L)
          (by simpa using e2)]
      rw [hP, List.nil_append] at ih
      rw [hP, List.nil_append, List.cons_append, ih]
    · have e0 : ¬ h < U a := by omega
      have e1 : ¬ U a = h := by omega
      have hP : L.filter (fun i => h < U i) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb
        have := hle b hb
        simp only [decide_eq_true_eq]
        omega
      have hM : L.filter (fun i => U i = h) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb
        have := hle b hb
        simp only [decide_eq_true_eq]
        omega
      rw [List.filter_cons_of_neg (p := fun i => decide (h < U i)) (a := a) (l := L)
          (by simpa using e0),
        List.filter_cons_of_neg (p := fun i => decide (U i = h)) (a := a) (l := L)
          (by simpa using e1),
        List.filter_cons_of_pos (p := fun i => decide (U i < h)) (a := a) (l := L)
          (by simpa using h1)]
      rw [hP, hM, List.nil_append, List.nil_append] at ih
      rw [hP, hM, List.nil_append, List.nil_append, ih]

/-- Number of entries of `L` strictly above level `h`. -/
def Acnt (L : List (Fin n)) (U : Fin n → ℕ) (h : ℕ) : ℕ := (L.filter (fun i => h < U i)).length

/-- Number of entries of `L` at level `h`. -/
def Mcnt (L : List (Fin n)) (U : Fin n → ℕ) (h : ℕ) : ℕ := (L.filter (fun i => U i = h)).length

lemma greedy (L : List (Fin n)) (U : Fin n → ℕ) (ρ : Fin n → ℝ) (τ : ℕ → ℝ)
    (hL : L.Pairwise (fun i j => U j ≤ U i)) (hρ : (L.map ρ).Pairwise (fun a b => b ≤ a)) :
    ∀ levels : List ℕ, levels.Pairwise (fun a b => b < a) →
    (∀ h ∈ levels, τ h ≤ ((L.filter (fun i => U i = h)).map ρ).sum) →
    ∀ s, (∀ h ∈ levels, s ≤ Acnt L U h) →
    ∃ ks, greedyLengths ((L.map ρ).drop s) (levels.map τ) = some ks ∧
      List.Forall₂ (fun k h => k ≤ Mcnt L U h) ks levels := by
  intro levels
  induction levels with
  | nil => intro _ _ s _; exact ⟨[], rfl, List.Forall₂.nil⟩
  | cons h rest ih =>
    intro hlev hτ s hs
    rw [List.pairwise_cons] at hlev
    have hsA : s ≤ Acnt L U h := hs h (by simp)
    have hdec := decomp U h L hL
    have hlen : Acnt L U h + Mcnt L U h ≤ L.length := by
      have := congrArg List.length hdec
      simp only [List.length_append] at this
      unfold Acnt Mcnt
      omega
    have hpre : ((L.map ρ).drop (Acnt L U h)).take (Mcnt L U h) =
        (L.filter (fun i => U i = h)).map ρ := by
      have e : L.map ρ = (L.filter (fun i => h < U i)).map ρ ++
          ((L.filter (fun i => U i = h)).map ρ ++ (L.filter (fun i => U i < h)).map ρ) := by
        conv_lhs => rw [← hdec]
        simp only [List.map_append]
      rw [e, List.drop_left' (l₁ := (L.filter (fun i => h < U i)).map ρ) (i := Acnt L U h)
          (by rw [List.length_map]; rfl),
        List.take_left' (l₁ := (L.filter (fun i => U i = h)).map ρ) (i := Mcnt L U h)
          (by rw [List.length_map]; rfl)]
    have hmono := drop_take_mono (L.map ρ) hρ (Mcnt L U h) s (Acnt L U h - s)
      (by rw [List.length_map]; omega)
    rw [show s + (Acnt L U h - s) = Acnt L U h by omega, hpre] at hmono
    obtain ⟨k, hk, hkm⟩ := leastPrefix_le ((L.map ρ).drop s) (τ h) (Mcnt L U h)
      (by rw [List.length_drop, List.length_map]; omega)
      ((hτ h (by simp)).trans hmono)
    have hs' : ∀ h' ∈ rest, s + k ≤ Acnt L U h' := by
      intro h' hh'
      have hlt : h' < h := hlev.1 h' hh'
      have := count_le (fun i => decide (h < U i)) (fun i => decide (U i = h))
        (fun i => decide (h' < U i))
        (fun x h1 h2 => by simp only [decide_eq_true_eq] at h1 h2; omega)
        (fun x hx => by simp only [decide_eq_true_eq] at hx ⊢; omega) L
      simp only [Acnt, Mcnt] at hlen hsA hkm ⊢
      omega
    obtain ⟨ks, hks, hF⟩ := ih hlev.2 (fun h' hh' => hτ h' (by simp [hh'])) (s + k) hs'
    refine ⟨k :: ks, ?_, List.Forall₂.cons hkm hF⟩
    simp only [List.map_cons, greedyLengths, hk, List.drop_drop, hks] <;> rfl

end Aux_MNL8

open MNLStability Aux_MNL8 in
theorem solution {n : ℕ} (hn : 1 ≤ n) (wts : Weights n) (hw : wts.Pos) (r : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i)
    (pM : ℕ →₀ ℝ) (hM : IsLaw pM) (I : Finset (Fin n)) (hI : wts.UniformOn I)
    (ord : List (Fin n)) (hord : IsPriceOrder r I ord) (C : ℕ) (ε : ℝ) (hε : 0 < ε)
    (H : Finset ℕ) (hH : IsSpaced ε C H) (Ustep : Fin n → ℕ) (hval : ∀ i ∈ I, Ustep i ∈ H)
    (hmono : NonincAlong ord Ustep) (hnorm : norm1 Ustep ≤ C)
    (hpos : ∃ h ∈ H, 0 < Rlev wts r pM I Ustep h)
    (Rt Et : ℕ → ℝ) (hRt : ∀ h ∈ Lam wts r pM I H Ustep ε, Rt h ≤ Rlev wts r pM I Ustep h)
    (hEt : ∀ h ∈ Lam wts r pM I H Ustep ε, ∀ i ∈ lev I Ustep h, expX wts pM Ustep i ≤ Et h) :
    ∃ ks : List ℕ,
      greedyLengths (ord.map r) ((lamList wts r pM I H Ustep ε).map fun h => Rt h / Et h) =
        some ks ∧
      List.Forall₂ (fun k h => k ≤ (lev I Ustep h).card) ks (lamList wts r pM I H Ustep ε) := by
  obtain ⟨hnd, hmem, hpr⟩ := hord
  -- levels as filters of `ord`
  have hlev : ∀ h, lev I Ustep h = (ord.filter (fun i => Ustep i = h)).toFinset := by
    intro h
    ext i
    simp only [lev, Finset.mem_filter, List.mem_toFinset, List.mem_filter, decide_eq_true_eq,
      hmem i]
  have hcard : ∀ h, (lev I Ustep h).card = Mcnt ord Ustep h := by
    intro h
    rw [hlev h, List.toFinset_card_of_nodup (hnd.filter _)]
    rfl
  have hsumlev : ∀ h, ∑ i ∈ lev I Ustep h, r i =
      ((ord.filter (fun i => Ustep i = h)).map r).sum := by
    intro h
    rw [hlev h, List.sum_toFinset _ (hnd.filter _)]
  -- the minimal positive level has positive contribution
  have hRmin : 0 < Rlev wts r pM I Ustep (hMin wts r pM I H Ustep) := by
    obtain ⟨h0, hh0, hR0⟩ := hpos
    have hne : (H.filter (fun h => 0 < Rlev wts r pM I Ustep h)).Nonempty :=
      ⟨h0, Finset.mem_filter.2 ⟨hh0, hR0⟩⟩
    obtain ⟨hm, hmmem, hmeq⟩ := Finset.exists_mem_eq_sup _ hne id
    have e : hMin wts r pM I H Ustep = hm := hmeq
    rw [e]
    exact (Finset.mem_filter.1 hmmem).2
  have hHc : (0 : ℝ) < H.card := Nat.cast_pos.2 (Finset.card_pos.2 ⟨0, hH.1⟩)
  have hX : ∀ i, 0 ≤ expX wts pM Ustep i := fun i =>
    Finset.sum_nonneg (fun m _ => mul_nonneg (hM.1 m) ENNReal.toReal_nonneg)
  have hmemlam : ∀ h, h ∈ lamList wts r pM I H Ustep ε ↔ h ∈ Lam wts r pM I H Ustep ε := by
    intro h
    unfold lamList
    rw [List.mem_reverse, Finset.mem_sort]
  have hτ : ∀ h ∈ lamList wts r pM I H Ustep ε,
      Rt h / Et h ≤ ((ord.filter (fun i => Ustep i = h)).map r).sum := by
    intro h hh
    rw [hmemlam] at hh
    rw [← hsumlev h]
    have hRl : 0 < Rlev wts r pM I Ustep h := by
      have h1 := (Finset.mem_filter.1 hh).2
      have h2 : 0 < ε / H.card * Rlev wts r pM I Ustep (hMin wts r pM I H Ustep) :=
        mul_pos (div_pos hε hHc) hRmin
      linarith
    have hne : (lev I Ustep h).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      unfold Rlev at hRl
      rw [he, Finset.sum_empty] at hRl
      exact lt_irrefl _ hRl
    obtain ⟨i0, hi0⟩ := hne
    have hEt0 : 0 ≤ Et h := (hX i0).trans (hEt h hh i0 hi0)
    rcases eq_or_lt_of_le hEt0 with h0 | hEp
    · rw [← h0, div_zero]
      exact Finset.sum_nonneg (fun i _ => hr i)
    · rw [div_le_iff₀ hEp]
      calc Rt h ≤ Rlev wts r pM I Ustep h := hRt h hh
        _ = ∑ i ∈ lev I Ustep h, r i * expX wts pM Ustep i := rfl
        _ ≤ ∑ i ∈ lev I Ustep h, r i * Et h :=
            Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hEt h hh i hi) (hr i))
        _ = (∑ i ∈ lev I Ustep h, r i) * Et h := by rw [Finset.sum_mul]
  have hsorted : (lamList wts r pM I H Ustep ε).Pairwise (fun a b => b < a) := by
    unfold lamList
    rw [List.pairwise_reverse]
    have h1 : ((Lam wts r pM I H Ustep ε).sort (· ≤ ·)).Pairwise (· ≤ ·) :=
      Finset.pairwise_sort _ _
    have h2 : ((Lam wts r pM I H Ustep ε).sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
    exact (h1.and h2).imp (fun h => lt_of_le_of_ne h.1 h.2)
  obtain ⟨ks, hks, hF⟩ := greedy ord Ustep r (fun h => Rt h / Et h) hmono
    (List.pairwise_map.2 hpr) (lamList wts r pM I H Ustep ε) hsorted hτ 0
    (fun h _ => Nat.zero_le _)
  refine ⟨ks, ?_, hF.imp (fun k h hk => by rw [hcard h]; exact hk)⟩
  rw [List.drop_zero] at hks
  exact hks
