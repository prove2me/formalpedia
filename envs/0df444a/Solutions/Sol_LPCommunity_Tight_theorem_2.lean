-- Prove2me | solution 1 for LPCommunity.Tight.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T06:54:39.949655+00:00
-- url     : https://prove2.me/submissions/7f4add39-0382-44a0-9fcb-8413979a4ee6

import Mathlib
import Definitions.Def_LPCommunity_MinBisect_Setting

set_option autoImplicit false

namespace LPCommunityTightAux

open Finset LPCommunity.MinBisect

lemma card_val_lt (k T : ℕ) (hT : T ≤ k) :
    (univ.filter fun z : Fin k => z.val < T).card = T := by
  have h : (univ.filter fun z : Fin k => z.val < T).map Fin.valEmbedding = range T := by
    ext m
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
    constructor
    · rintro ⟨z, hz, rfl⟩; exact hz
    · intro hm; exact ⟨⟨m, by omega⟩, hm, rfl⟩
  rw [← card_map, h, card_range]

lemma card_add_lt (k : ℕ) [NeZero k] (x : Fin k) (T : ℕ) (hT : T ≤ k) :
    (univ.filter fun y : Fin k => (x + y).val < T).card = T := by
  refine (Finset.card_equiv (Equiv.addLeft x) ?_).trans (card_val_lt k T hT)
  intro y
  simp

lemma card_fiber_sum (k : ℕ) [NeZero k] (T : Fin 4 → ℕ) (hT : ∀ q, T q ≤ k)
    (C : Fin 4 → Prop) [DecidablePred C] (r : Fin k) :
    (univ.filter fun p : Fin 4 × Fin k => (r + p.2).val < T p.1 ∧ C p.1).card
      = ∑ q, if C q then T q else 0 := by
  rw [card_filter, ← univ_product_univ, sum_product]
  refine sum_congr rfl fun q _ => ?_
  by_cases hq : C q
  · simp only [hq, and_true, if_true]
    rw [← card_filter]
    exact card_add_lt k r (T q) (hT q)
  · simp [hq]

lemma card_count (k : ℕ) [NeZero k] (T : Fin 4 → ℕ) (hT : ∀ q, T q ≤ k)
    (C : Fin 4 → Prop) [DecidablePred C] (x : Fin 4 × Fin k) :
    (univ.filter fun p : Fin 4 × Fin k => p ≠ x ∧ (x.2 + p.2).val < T p.1 ∧ C p.1).card
      + (if (x.2 + x.2).val < T x.1 ∧ C x.1 then 1 else 0)
      = ∑ q, if C q then T q else 0 := by
  rw [← card_fiber_sum k T hT C x.2]
  by_cases hx : (x.2 + x.2).val < T x.1 ∧ C x.1
  · rw [if_pos hx]
    have : (univ.filter fun p : Fin 4 × Fin k => p ≠ x ∧ (x.2 + p.2).val < T p.1 ∧ C p.1)
        = (univ.filter fun p : Fin 4 × Fin k => (x.2 + p.2).val < T p.1 ∧ C p.1).erase x := by
      ext p; simp
    rw [this, card_erase_add_one]
    simp [hx]
  · rw [if_neg hx, add_zero]
    congr 1
    ext p
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; refine ⟨?_, h⟩; rintro rfl; exact hx h

lemma card_quarter (k : ℕ) (C : Fin 4 → Prop) [DecidablePred C] :
    (univ.filter fun p : Fin 4 × Fin k => C p.1).card = ∑ q, if C q then k else 0 := by
  rw [card_filter, ← univ_product_univ, sum_product]
  refine sum_congr rfl fun q _ => ?_
  by_cases hq : C q <;> simp [hq]

def thr (a b c e : ℕ) (q q' : Fin 4) : ℕ :=
  if q = q' then a + 1 else if (q.val < 2 ↔ q'.val < 2) then b
  else if q.val % 2 = q'.val % 2 then c else e

lemma thr_symm (a b c e : ℕ) (q q' : Fin 4) : thr a b c e q q' = thr a b c e q' q := by
  unfold thr
  by_cases h1 : q = q'
  · subst h1; rfl
  · rw [if_neg h1, if_neg (Ne.symm h1)]
    by_cases h2 : (q.val < 2 ↔ q'.val < 2)
    · rw [if_pos h2, if_pos h2.symm]
    · have h2' : ¬(q'.val < 2 ↔ q.val < 2) := fun h => h2 h.symm
      rw [if_neg h2, if_neg h2']
      by_cases h3 : q.val % 2 = q'.val % 2
      · have h3' : q'.val % 2 = q.val % 2 := h3.symm
        rw [if_pos h3, if_pos h3']
      · have h3' : ¬(q'.val % 2 = q.val % 2) := fun h => h3 h.symm
        rw [if_neg h3, if_neg h3']

def E (k n : ℕ) (hk : 4 * k = n) : Fin 4 × Fin k ≃ Fin n :=
  finProdFinEquiv.trans (finCongr hk)

def TG (k n : ℕ) (hk : 4 * k = n) (T : Fin 4 → Fin 4 → ℕ)
    (hTs : ∀ q q', T q q' = T q' q) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (((E k n hk).symm u).2 + ((E k n hk).symm v).2).val
      < T ((E k n hk).symm u).1 ((E k n hk).symm v).1
  symm := ⟨fun u v h => ⟨h.1.symm, by
    have hc : ((E k n hk).symm v).2 + ((E k n hk).symm u).2
        = ((E k n hk).symm u).2 + ((E k n hk).symm v).2 :=
      Fin.ext (by simp only [Fin.val_add]; rw [Nat.add_comm])
    rw [hc, hTs]; exact h.2⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

lemma TG_adj (k n : ℕ) (hk : 4 * k = n) (T : Fin 4 → Fin 4 → ℕ)
    (hTs : ∀ q q', T q q' = T q' q) (u v : Fin n) :
    (TG k n hk T hTs).Adj u v ↔ u ≠ v ∧ (((E k n hk).symm u).2 + ((E k n hk).symm v).2).val
      < T ((E k n hk).symm u).1 ((E k n hk).symm v).1 := Iff.rfl

lemma deg_formula (k n : ℕ) [NeZero k] (hk : 4 * k = n) (T : Fin 4 → Fin 4 → ℕ)
    (hTs : ∀ q q', T q q' = T q' q) (hT : ∀ q q', T q q' ≤ k)
    (C : Fin 4 → Prop) [DecidablePred C] (v : Fin n) (s : Finset (Fin n))
    (hs : ∀ u, u ∈ s ↔ (TG k n hk T hTs).Adj v u ∧ C ((E k n hk).symm u).1) :
    s.card + (if (((E k n hk).symm v).2 + ((E k n hk).symm v).2).val
        < T ((E k n hk).symm v).1 ((E k n hk).symm v).1 ∧ C ((E k n hk).symm v).1 then 1 else 0)
      = ∑ q, if C q then T ((E k n hk).symm v).1 q else 0 := by
  rw [← card_count k (T ((E k n hk).symm v).1) (hT _) C ((E k n hk).symm v)]
  congr 1
  apply Finset.card_equiv (E k n hk).symm
  intro u
  rw [hs u, TG_adj]
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨fun h => h1 ((E k n hk).symm.injective h).symm, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨fun h => h1 (by rw [h]), h2⟩, h3⟩

open scoped Classical in
lemma two_cut {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    2 * cutCost G S = ∑ v, (univ.filter fun u => G.Adj v u ∧ ¬ sameSide S v u).card := by
  set A := univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.Adj p.1 p.2 ∧ ¬ sameSide S p.1 p.2
    with hA
  set B := univ.filter fun p : Fin n × Fin n => p.2 < p.1 ∧ G.Adj p.1 p.2 ∧ ¬ sameSide S p.1 p.2
    with hB
  have hcA : cutCost G S = A.card := by
    unfold cutCost; rw [hA]
  have hAB : B.card = A.card := by
    apply Finset.card_equiv (Equiv.prodComm _ _)
    rintro ⟨x, y⟩
    simp only [hB, hA, mem_filter, mem_univ, true_and, Equiv.prodComm_apply, Prod.swap_prod_mk]
    unfold sameSide
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2.symm, fun h => h3 h.symm⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2.symm, fun h => h3 h.symm⟩
  have hU : univ.filter (fun p : Fin n × Fin n => G.Adj p.1 p.2 ∧ ¬ sameSide S p.1 p.2)
      = A ∪ B := by
    ext ⟨x, y⟩
    simp only [hA, hB, mem_union, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_trichotomy x y with h | h | h
      · exact Or.inl ⟨h, h1, h2⟩
      · exact absurd h (G.ne_of_adj h1)
      · exact Or.inr ⟨h, h1, h2⟩
    · rintro (⟨_, h1, h2⟩ | ⟨_, h1, h2⟩) <;> exact ⟨h1, h2⟩
  have hD : Disjoint A B := by
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    simp only [hA, hB, mem_filter, mem_univ, true_and] at h1 h2
    exact absurd h1.1 (not_lt.mpr h2.1.le)
  have hsum : (univ.filter (fun p : Fin n × Fin n => G.Adj p.1 p.2 ∧ ¬ sameSide S p.1 p.2)).card
      = ∑ v, (univ.filter fun u => G.Adj v u ∧ ¬ sameSide S v u).card := by
    rw [card_filter, ← univ_product_univ, sum_product]
    refine sum_congr rfl fun v _ => ?_
    rw [card_filter]
  rw [← hsum, hU, card_union_of_disjoint hD, hAB, hcA]; ring

theorem main (n k din dout : ℕ) (hk : 4 * k = n) (hk0 : 0 < k)
    (h1 : din + 1 ≤ 2 * k) (h2 : dout ≤ 2 * k) (h3 : din + 1 ≤ dout + k) :
    ∃ (G : SimpleGraph (Fin n)) (V1 : Finset (Fin n)),
      IsBisection n V1 ∧ dIn G V1 = din ∧ dOut G V1 = dout ∧ ¬ MinBisectRecovers G V1 := by
  classical
  have : NeZero k := ⟨by omega⟩
  have : NeZero n := ⟨by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, b = din - (k - 1) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = din - b := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = min k dout := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = dout - c := ⟨_, rfl⟩
  have hc1 : c ≤ k := hc ▸ min_le_left _ _
  have hc2 : c ≤ dout := hc ▸ min_le_right _ _
  have hc3 : c = k ∨ c = dout := hc ▸ min_choice _ _
  have hak : a + 1 ≤ k := by omega
  have hbk : b ≤ k := by omega
  have hek : e ≤ k := by omega
  have hbc : b ≤ c := by omega
  have hab : a + b = din := by omega
  have hce : c + e = dout := by omega
  have hTs : ∀ q q', thr a b c e q q' = thr a b c e q' q := thr_symm a b c e
  have hT : ∀ q q', thr a b c e q q' ≤ k := by
    intro q q'; unfold thr; split_ifs <;> omega
  have sIn : ∀ x : Fin 4,
      (∑ q, if (x.val < 2 ↔ q.val < 2) then thr a b c e x q else 0) = a + 1 + b := by
    intro x; fin_cases x <;> simp [Fin.sum_univ_four, thr] <;> omega
  have sOut : ∀ x : Fin 4,
      (∑ q, if ¬(x.val < 2 ↔ q.val < 2) then thr a b c e x q else 0) = c + e := by
    intro x; fin_cases x <;> simp [Fin.sum_univ_four, thr] <;> omega
  have sS : ∀ x : Fin 4,
      (∑ q, if ¬(x.val % 2 = 0 ↔ q.val % 2 = 0) then thr a b c e x q else 0) = b + e := by
    intro x; fin_cases x <;> simp [Fin.sum_univ_four, thr] <;> omega
  set V1 : Finset (Fin n) := univ.filter fun v => ((E k n hk).symm v).1.val < 2 with hV1
  set S : Finset (Fin n) := univ.filter fun v => ((E k n hk).symm v).1.val % 2 = 0 with hS
  have inDeg_ge : ∀ v, a + b ≤ inDeg (TG k n hk (thr a b c e) hTs) V1 v ∧ (v = (E k n hk) (0, 0) → inDeg (TG k n hk (thr a b c e) hTs) V1 v = a + b) := by
    intro v
    have hf := deg_formula k n hk (thr a b c e) hTs hT
      (fun q => (((E k n hk).symm v).1.val < 2 ↔ q.val < 2)) v
      (univ.filter fun u => (TG k n hk (thr a b c e) hTs).Adj v u ∧ sameSide V1 v u) (by intro u; simp [hV1, sameSide])
    rw [sIn] at hf
    have hdeg : inDeg (TG k n hk (thr a b c e) hTs) V1 v = (univ.filter fun u => (TG k n hk (thr a b c e) hTs).Adj v u ∧ sameSide V1 v u).card := by
      unfold inDeg; rfl
    rw [hdeg]
    constructor
    · split_ifs at hf <;> omega
    · rintro rfl
      rw [if_pos (by simp [thr])] at hf
      omega
  have outDeg_eq : ∀ v, outDeg (TG k n hk (thr a b c e) hTs) V1 v = dout := by
    intro v
    have hf := deg_formula k n hk (thr a b c e) hTs hT
      (fun q => ¬(((E k n hk).symm v).1.val < 2 ↔ q.val < 2)) v
      (univ.filter fun u => (TG k n hk (thr a b c e) hTs).Adj v u ∧ ¬ sameSide V1 v u) (by intro u; simp [hV1, sameSide])
    rw [sOut, if_neg (by simp)] at hf
    have hdeg : outDeg (TG k n hk (thr a b c e) hTs) V1 v = (univ.filter fun u => (TG k n hk (thr a b c e) hTs).Adj v u ∧ ¬ sameSide V1 v u).card := by
      unfold outDeg; rfl
    omega
  have hdin : dIn (TG k n hk (thr a b c e) hTs) V1 = din := by
    unfold dIn
    rw [dif_pos univ_nonempty]
    apply le_antisymm
    · calc univ.inf' _ (inDeg (TG k n hk (thr a b c e) hTs) V1) ≤ inDeg (TG k n hk (thr a b c e) hTs) V1 ((E k n hk) (0, 0)) := inf'_le _ (mem_univ _)
        _ = din := by rw [(inDeg_ge _).2 rfl, hab]
    · exact le_inf' _ _ fun v _ => hab ▸ (inDeg_ge v).1
  have hdout : dOut (TG k n hk (thr a b c e) hTs) V1 = dout := by
    unfold dOut
    apply le_antisymm
    · exact Finset.sup_le fun v _ => (outDeg_eq v).le
    · exact (outDeg_eq ((E k n hk) (0, 0))).symm.le.trans (Finset.le_sup (mem_univ _))
  have hcardQ : ∀ (C : Fin 4 → Prop) [DecidablePred C],
      (univ.filter fun v : Fin n => C ((E k n hk).symm v).1).card = ∑ q, if C q then k else 0 := by
    intro C _
    rw [← card_quarter k C]
    apply Finset.card_equiv (E k n hk).symm
    intro u; simp
  have hV1b : IsBisection n V1 := by
    unfold IsBisection
    have h : V1.card = ∑ q : Fin 4, if q.val < 2 then k else 0 := hcardQ (fun q => q.val < 2)
    have h' : (∑ q : Fin 4, if q.val < 2 then k else 0) = k + k := by
      simp [Fin.sum_univ_four]
    rw [h, h']; omega
  have hSb : IsBisection n S := by
    unfold IsBisection
    have h : S.card = ∑ q : Fin 4, if q.val % 2 = 0 then k else 0 := hcardQ (fun q => q.val % 2 = 0)
    have h' : (∑ q : Fin 4, if q.val % 2 = 0 then k else 0) = k + k := by
      simp [Fin.sum_univ_four]
    rw [h, h']; omega
  have hcut : cutCost (TG k n hk (thr a b c e) hTs) S ≤ cutCost (TG k n hk (thr a b c e) hTs) V1 := by
    have e1 := two_cut (TG k n hk (thr a b c e) hTs) S
    have e2 := two_cut (TG k n hk (thr a b c e) hTs) V1
    have hle : ∀ v, (univ.filter fun u => (TG k n hk (thr a b c e) hTs).Adj v u ∧ ¬ sameSide S v u).card
        ≤ (univ.filter fun u => (TG k n hk (thr a b c e) hTs).Adj v u ∧ ¬ sameSide V1 v u).card := by
      intro v
      have f1 := deg_formula k n hk (thr a b c e) hTs hT
        (fun q => ¬(((E k n hk).symm v).1.val % 2 = 0 ↔ q.val % 2 = 0)) v
        (univ.filter fun u => (TG k n hk (thr a b c e) hTs).Adj v u ∧ ¬ sameSide S v u) (by intro u; simp [hS, sameSide])
      have f2 := deg_formula k n hk (thr a b c e) hTs hT
        (fun q => ¬(((E k n hk).symm v).1.val < 2 ↔ q.val < 2)) v
        (univ.filter fun u => (TG k n hk (thr a b c e) hTs).Adj v u ∧ ¬ sameSide V1 v u) (by intro u; simp [hV1, sameSide])
      rw [sS, if_neg (by simp)] at f1
      rw [sOut, if_neg (by simp)] at f2
      omega
    have := sum_le_sum fun v (_ : v ∈ (univ : Finset (Fin n))) => hle v
    omega
  refine ⟨(TG k n hk (thr a b c e) hTs), V1, hV1b, hdin, hdout, fun hrec => ?_⟩
  rcases hrec S hSb hcut with h | h
  · have hm : (E k n hk) (1, 0) ∈ S := by rw [h, hV1]; simp
    rw [hS] at hm
    simp at hm
  · have hm : (E k n hk) (0, 0) ∈ S := by rw [hS]; simp
    rw [h, mem_compl, hV1] at hm
    exact hm (by simp)

end LPCommunityTightAux

theorem solution (n din dout : ℕ) (hn : 0 < n) (h8 : 8 ∣ n)
    (hin : (din : ℝ) ≤ (n : ℝ) / 2 - 1)
    (hout : (dout : ℝ) ≤ (n : ℝ) / 2)
    (h : (din : ℝ) - (dout : ℝ) ≤ (n : ℝ) / 4 - 1) :
    ∃ (G : SimpleGraph (Fin n)) (V1 : Finset (Fin n)),
      LPCommunity.MinBisect.IsBisection n V1 ∧ LPCommunity.MinBisect.dIn G V1 = din ∧ LPCommunity.MinBisect.dOut G V1 = dout ∧
      ¬ LPCommunity.MinBisect.MinBisectRecovers G V1 := by
  obtain ⟨m, rfl⟩ := h8
  have hm : 0 < m := by omega
  have h1 : din + 1 ≤ 2 * (2 * m) := by
    have : ((din : ℝ) + 1) ≤ ((2 * (2 * m) : ℕ) : ℝ) := by push_cast at hin ⊢; linarith
    exact_mod_cast this
  have h2 : dout ≤ 2 * (2 * m) := by
    have : (dout : ℝ) ≤ ((2 * (2 * m) : ℕ) : ℝ) := by push_cast at hout ⊢; linarith
    exact_mod_cast this
  have h3 : din + 1 ≤ dout + 2 * m := by
    have : ((din : ℝ) + 1) ≤ ((dout + 2 * m : ℕ) : ℝ) := by push_cast at h ⊢; linarith
    exact_mod_cast this
  exact LPCommunityTightAux.main (8 * m) (2 * m) din dout (by ring) (by omega) h1 h2 h3
