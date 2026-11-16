-- Prove2me | solution 1 for NestedCRP.last_customer_rule
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-11-15T18:13:51.013332+00:00
-- url     : https://prove2.me/submissions/4d85893e-c54a-4c1e-9dec-54be899ffd18

import Mathlib
import Definitions.Def_NestedCRP_Tree
import Definitions.Def_NestedCRP_ncrpMass

namespace NcrpExchange
open NestedCRP
noncomputable section
open Classical
variable {D : ℕ}

def count (T : Tree D) (l : ℕ) (d : Fin D) (A : Finset (Fin D)) : ℕ :=
  (A.filter fun e => T.Rel l e d).card

lemma count_eq (T : Tree D) (l : ℕ) {a b : Fin D} (hab : T.Rel l a b) (A : Finset (Fin D)) :
    count T l a A = count T l b A := by
  apply congrArg Finset.card
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, h⟩
    exact ⟨he, (T.part l).trans h hab⟩
  · rintro ⟨he, h⟩
    exact ⟨he, (T.part l).trans h ((T.part l).symm hab)⟩

lemma count_insert (T : Tree D) (l : ℕ) (a b : Fin D) (A : Finset (Fin D))
    (ha : a ∉ A) :
    count T l b (insert a A) = count T l b A + if T.Rel l a b then 1 else 0 := by
  by_cases h : T.Rel l a b
  · simp [count, Finset.filter_insert, h, ha, Nat.add_comm]
  · simp [count, Finset.filter_insert, h]

lemma seat_eq (γ : ℝ) (T : Tree D) (d : Fin D) (l : ℕ) (A : Finset (Fin D)) :
    seat γ T d l A =
      (if 0 < count T (l+1) d A then (count T (l+1) d A : ℝ) else γ) /
        (γ + count T l d A) := rfl

lemma seat_swap (γ : ℝ) (T : Tree D) (l : ℕ) (a b : Fin D)
    (A : Finset (Fin D)) (ha : a ∉ A) (hb : b ∉ A) :
    seat γ T a l A * seat γ T b l (insert a A) =
      seat γ T b l A * seat γ T a l (insert b A) := by
  have hp : T.Rel l b a ↔ T.Rel l a b :=
    ⟨(T.part l).symm, (T.part l).symm⟩
  have hc : T.Rel (l+1) b a ↔ T.Rel (l+1) a b :=
    ⟨(T.part (l+1)).symm, (T.part (l+1)).symm⟩
  simp only [seat_eq, count_insert T l a b A ha,
    count_insert T (l+1) a b A ha, count_insert T l b a A hb,
    count_insert T (l+1) b a A hb, hp, hc]
  by_cases hparent : T.Rel l a b
  · have hn := count_eq T l hparent A
    by_cases hchild : T.Rel (l+1) a b
    · have hm := count_eq T (l+1) hchild A
      simp [hparent, hchild, hn, hm]
    · simp only [hparent, hchild, if_true, if_false, add_zero, hn]
      simp only [div_eq_mul_inv]
      ring
  · have hchild : ¬T.Rel (l+1) a b := fun h =>
      hparent (T.antitone (Nat.le_succ l) h)
    simp [hparent,hchild,mul_comm]

def seq (γ : ℝ) (T : Tree D) (l : ℕ) :
    List (Fin D) → Finset (Fin D) → ℝ
  | [], _ => 1
  | d :: ds, A => seat γ T d l A * seq γ T l ds (insert d A)

lemma seq_perm (γ : ℝ) (T : Tree D) (l : ℕ)
    {xs ys : List (Fin D)} (h : xs.Perm ys) (hn : xs.Nodup)
    (A : Finset (Fin D)) (hA : ∀ a ∈ xs, a ∉ A) :
    seq γ T l xs A = seq γ T l ys A := by
  induction h generalizing A with
  | nil => rfl
  | @cons a xs ys h ih =>
      simp only [List.nodup_cons] at hn
      simp only [seq]
      congr 1
      apply ih hn.2
      intro b hb
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun h => hn.1 (h ▸ hb), hA b (List.mem_cons_of_mem a hb)⟩
  | swap a b xs =>
      have ha := hA a (by simp)
      have hb := hA b (by simp)
      simp only [seq]
      rw [Finset.insert_comm a b A]
      rw [← mul_assoc, ← mul_assoc]
      congr 1
      exact seat_swap γ T l b a A hb ha
  | @trans xs ys zs hxy hyz ihxy ihyz =>
      exact (ihxy hn A hA).trans (ihyz (hxy.nodup_iff.mp hn) A
        (fun a ha => hA a (hxy.mem_iff.mpr ha)))


lemma seq_sorted (γ : ℝ) (T : Tree D) (l : ℕ) (xs : List (Fin D))
    (hs : xs.Pairwise (· < ·)) (A : Finset (Fin D)) :
    seq γ T l xs A = ∏ d ∈ xs.toFinset,
      seat γ T d l (A ∪ xs.toFinset.filter (· < d)) := by
  induction xs generalizing A with
  | nil => simp [seq]
  | cons a xs ih =>
    obtain ⟨ha, hs⟩ := List.pairwise_cons.mp hs
    have hnot : a ∉ xs.toFinset := by
      simp only [List.mem_toFinset]
      exact fun h => (lt_irrefl a) (ha a h)
    rw [seq, List.toFinset_cons, Finset.prod_insert hnot, ih hs]
    have hfirst : (insert a xs.toFinset).filter (· < a) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro e he hlt
      rcases Finset.mem_insert.mp he with rfl | he
      · exact (lt_irrefl _) hlt
      · exact (lt_asymm (ha e (List.mem_toFinset.mp he))) hlt
    rw [hfirst, Finset.union_empty]
    congr 1
    apply Finset.prod_congr rfl
    intro d hd
    congr 1
    ext e
    have had := ha d (List.mem_toFinset.mp hd)
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_filter]
    constructor
    · rintro ((rfl | he) | he)
      · exact Or.inr ⟨Or.inl rfl, had⟩
      · exact Or.inl he
      · exact Or.inr ⟨Or.inr he.1, he.2⟩
    · rintro (he | ⟨rfl | he, hlt⟩)
      · exact Or.inl (Or.inr he)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr ⟨he,hlt⟩

lemma count_relabel (σ : Equiv.Perm (Fin D)) (T : Tree D) (l : ℕ)
    (d : Fin D) (A : Finset (Fin D)) :
    count (T.relabel σ) l d A = count T l (σ d) (A.map σ.toEmbedding) := by
  have hf : (A.filter (fun e => (T.relabel σ).Rel l e d)).map σ.toEmbedding =
      (A.map σ.toEmbedding).filter (fun e => T.Rel l e (σ d)) := by
    ext e
    simp only [Finset.mem_map, Finset.mem_filter, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨a, ⟨ha, h⟩, rfl⟩
      exact ⟨⟨a,ha,rfl⟩,h⟩
    · rintro ⟨⟨a,ha,rfl⟩,h⟩
      exact ⟨a,⟨ha,h⟩,rfl⟩
  exact (Finset.card_map σ.toEmbedding).symm.trans (congrArg Finset.card hf)

lemma seat_relabel (γ : ℝ) (σ : Equiv.Perm (Fin D)) (T : Tree D) (l : ℕ)
    (d : Fin D) (A : Finset (Fin D)) :
    seat γ (T.relabel σ) d l A = seat γ T (σ d) l (A.map σ.toEmbedding) := by
  simp only [seat_eq, count_relabel]

lemma seq_relabel (γ : ℝ) (σ : Equiv.Perm (Fin D)) (T : Tree D) (l : ℕ)
    (xs : List (Fin D)) (A : Finset (Fin D)) :
    seq γ (T.relabel σ) l xs A = seq γ T l (xs.map σ) (A.map σ.toEmbedding) := by
  induction xs generalizing A with
  | nil => rfl
  | cons d xs ih => simp only [seq, List.map_cons, ih, seat_relabel, Finset.map_insert,
      Equiv.toEmbedding_apply]

lemma sepLevel_relabel (σ : Equiv.Perm (Fin D)) (T : Tree D) :
    (T.relabel σ).sepLevel = T.sepLevel := by
  have hbot (l : ℕ) : (T.relabel σ).part l = ⊥ ↔ T.part l = ⊥ := by
    constructor
    · intro h
      apply le_bot_iff.mp
      intro a b hab
      have h' : ((T.relabel σ).part l).r (σ.symm a) (σ.symm b) := by
        change (T.part l).r (σ (σ.symm a)) (σ (σ.symm b))
        simpa using hab
      rw [h] at h'
      exact σ.symm.injective h'
    · intro h
      apply le_bot_iff.mp
      intro a b hab
      change (T.part l).r (σ a) (σ b) at hab
      rw [h] at hab
      exact σ.injective hab
  apply Nat.le_antisymm
  · exact Nat.find_min' _ ((hbot _).mpr (Nat.find_spec T.separated))
  · exact Nat.find_min' _ ((hbot _).mp (Nat.find_spec (T.relabel σ).separated))


lemma seq_finRange (γ : ℝ) (T : Tree D) (l : ℕ) :
    seq γ T l (List.finRange D) ∅ =
      ∏ d : Fin D, seat γ T d l (Finset.univ.filter (· < d)) := by
  simpa using seq_sorted γ T l (List.finRange D) (List.sortedLT_finRange D).pairwise ∅

lemma level_relabel (γ : ℝ) (σ : Equiv.Perm (Fin D)) (T : Tree D) (l : ℕ) :
    (∏ d : Fin D, seat γ (T.relabel σ) d l (Finset.univ.filter (· < d))) =
      ∏ d : Fin D, seat γ T d l (Finset.univ.filter (· < d)) := by
  rw [← seq_finRange, seq_relabel, Finset.map_empty, ← seq_finRange]
  exact seq_perm γ T l σ.map_finRange_perm
    ((List.nodup_finRange D).map σ.injective) ∅ (by simp)

end
end NcrpExchange


namespace LastCustomer
open NestedCRP NcrpExchange
noncomputable section
open Classical
variable {D : ℕ}

lemma part_bot (T : Tree D) (l : ℕ) (hl : T.sepLevel ≤ l) : T.part l = ⊥ := by
  apply le_bot_iff.mp
  exact (T.antitone hl).trans (Nat.find_spec T.separated).le

lemma seat_tail (γ : ℝ) (hγ : 0 < γ) (T : Tree D) (l : ℕ) (hl : T.sepLevel ≤ l)
    (d : Fin D) (A : Finset (Fin D)) (hd : d ∉ A) : seat γ T d l A = 1 := by
  have hf (m : ℕ) (hm : T.sepLevel ≤ m) : A.filter (fun e => T.Rel m e d) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro e he hrel
    have hed : e = d := by
      change (T.part m).r e d at hrel
      rw [part_bot T m hm] at hrel
      exact hrel
    exact hd (hed ▸ he)
  simp [seat,hf l hl,hf (l+1) (hl.trans (Nat.le_succ l)),hγ.ne']

lemma mass_extend (γ : ℝ) (hγ : 0 < γ) (T : Tree D) (L : ℕ) (hL : T.sepLevel ≤ L) :
    ncrpMass γ T = ∏ l ∈ Finset.range L, ∏ d : Fin D,
      seat γ T d l (Finset.univ.filter (· < d)) := by
  unfold ncrpMass
  rw [Finset.prod_comm]
  apply Finset.prod_subset (Finset.range_mono hL)
  intro l hl hn
  apply Finset.prod_eq_one
  intro d hd
  apply seat_tail γ hγ T l (by simpa using hn) d _
  simp

lemma last_extend (γ : ℝ) (hγ : 0 < γ) (T : Tree D) (d : Fin D) (L : ℕ)
    (hL : T.sepLevel ≤ L) :
    lastMass γ T d = ∏ l ∈ Finset.range L, seat γ T d l (Finset.univ.erase d) := by
  unfold lastMass
  apply Finset.prod_subset (Finset.range_mono hL)
  intro l hl hn
  exact seat_tail γ hγ T l (by simpa using hn) d _ (by simp)

lemma seq_append_one (γ : ℝ) (T : Tree D) (l : ℕ) (xs : List (Fin D)) (d : Fin D)
    (A : Finset (Fin D)) :
    seq γ T l (xs ++ [d]) A = seq γ T l xs A * seat γ T d l (A ∪ xs.toFinset) := by
  induction xs generalizing A with
  | nil => simp [seq]
  | cons a xs ih =>
    simp only [List.cons_append,seq,ih,List.toFinset_cons]
    rw [mul_assoc]
    have hset : insert a A ∪ xs.toFinset = A ∪ insert a xs.toFinset := by
      ext e
      simp only [Finset.mem_union,Finset.mem_insert]
      tauto
    rw [hset]

lemma seat_agrees (γ : ℝ) (T T' : Tree D) (d a : Fin D) (ha : a ≠ d)
    (h : T.AgreesOff d T') (A : Finset (Fin D)) (hA : d ∉ A) (l : ℕ) :
    seat γ T a l A = seat γ T' a l A := by
  have hf (m : ℕ) : A.filter (fun e => T.Rel m e a) = A.filter (fun e => T'.Rel m e a) := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨he,hr⟩
      exact ⟨he,(h m e a (fun heq => hA (heq ▸ he)) ha).mp hr⟩
    · rintro ⟨he,hr⟩
      exact ⟨he,(h m e a (fun heq => hA (heq ▸ he)) ha).mpr hr⟩
  simp only [seat,hf]

lemma seq_agrees (γ : ℝ) (T T' : Tree D) (d : Fin D) (h : T.AgreesOff d T')
    (xs : List (Fin D)) (hx : d ∉ xs) (A : Finset (Fin D)) (hA : d ∉ A) (l : ℕ) :
    seq γ T l xs A = seq γ T' l xs A := by
  induction xs generalizing A with
  | nil => rfl
  | cons a xs ih =>
    have ha : a ≠ d := fun heq => hx (by simp [heq])
    have hxs : d ∉ xs := fun hh => hx (List.mem_cons_of_mem a hh)
    simp only [seq]
    rw [seat_agrees γ T T' d a ha h A hA l, ih hxs _ (by simp [hA,Ne.symm ha])]

lemma level_split (γ : ℝ) (T : Tree D) (d : Fin D) (l : ℕ) :
    (∏ a : Fin D, seat γ T a l (Finset.univ.filter (· < a))) =
      seq γ T l (Finset.univ.erase d).toList ∅ * seat γ T d l (Finset.univ.erase d) := by
  let xs := (Finset.univ.erase d).toList
  have hn : (xs ++ [d]).Nodup := by simp [List.nodup_append,xs,Finset.nodup_toList]
  have hp : (List.finRange D).Perm (xs ++ [d]) := by
    apply (List.perm_ext_iff_of_nodup (List.nodup_finRange D) hn).mpr
    intro a
    simp only [List.mem_finRange,List.mem_append,List.mem_singleton,Finset.mem_toList,Finset.mem_erase,Finset.mem_univ,true_iff,and_true,xs]
    tauto
  rw [← seq_finRange, seq_perm γ T l hp (List.nodup_finRange D) ∅ (by simp), seq_append_one]
  simp [xs]

end
end LastCustomer

open NestedCRP LastCustomer NcrpExchange in
theorem solution {D : ℕ} {γ : ℝ} (hγ : 0 < γ) (d : Fin D) (T T' : Tree D)
    (h : T.AgreesOff d T') :
    ncrpMass γ T * lastMass γ T' d = ncrpMass γ T' * lastMass γ T d := by
  classical
  let L := max T.sepLevel T'.sepLevel
  have hL : T.sepLevel ≤ L := le_max_left _ _
  have hL' : T'.sepLevel ≤ L := le_max_right _ _
  have hp : (∏ l ∈ Finset.range L, seq γ T l (Finset.univ.erase d).toList ∅) =
      ∏ l ∈ Finset.range L, seq γ T' l (Finset.univ.erase d).toList ∅ := by
    apply Finset.prod_congr rfl
    intro l hl
    exact seq_agrees γ T T' d h _ (by simp) ∅ (by simp) l
  rw [mass_extend γ hγ T L hL, mass_extend γ hγ T' L hL',
    last_extend γ hγ T d L hL, last_extend γ hγ T' d L hL']
  simp_rw [level_split γ _ d]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,hp]
  ring
