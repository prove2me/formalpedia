-- Prove2me | solution 1 for KKBinPacking.LinearGrouping.anyFit_card_le
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:28:18.382927+00:00
-- url     : https://prove2.me/submissions/fb99a179-bab9-479c-bbe6-e6232c861d50

import Definitions.Def_KKBinPacking_LinearGrouping_Algorithm1
import Definitions.Def_KKBinPacking_LinearGrouping_Instance
import Mathlib.Data.Finset.Max
import Mathlib.Order.Lattice.Nat
open KKBinPacking.LinearGrouping

private theorem packing_exists (I : Multiset ℝ) (hI : IsInstance I) :
    ∃ P, IsPacking I P := by
  refine ⟨I.map (fun a => ({a} : Multiset ℝ)),?_,?_⟩
  · induction I using Multiset.induction_on with
    | empty => simp
    | cons a I ih => simpa [Multiset.map_cons,Multiset.join_cons] using congrArg (fun J => a ::ₘ J) (ih (fun b hb => hI b (by simp [hb])))
  · intro b hb
    obtain ⟨a,ha,rfl⟩:=Multiset.mem_map.mp hb
    simpa using (hI a ha).2.le

private theorem opt_attained (I : Multiset ℝ) (hI : IsInstance I) :
    ∃ P, IsPacking I P ∧ P.card=OPT I := by
  obtain ⟨P,hP⟩:=packing_exists I hI
  have hn : Set.Nonempty {B : ℕ | ∃ P : Multiset (Multiset ℝ),IsPacking I P ∧ P.card=B} := ⟨P.card,P,hP,rfl⟩
  exact Nat.sInf_mem hn

private theorem opt_le_card (I : Multiset ℝ) (P : Multiset (Multiset ℝ))
    (hP : IsPacking I P) : OPT I ≤ P.card :=
  Nat.sInf_le ⟨P,hP,rfl⟩

private theorem bin_nonneg (I : Multiset ℝ) (hI : IsInstance I)
    (P : Multiset (Multiset ℝ)) (hP : IsPacking I P) (b : Multiset ℝ) (hb : b ∈ P) :
    0 ≤ b.sum := by
  apply Multiset.sum_nonneg
  intro a ha
  exact (hI a (by rw [← hP.1];exact Multiset.mem_join.mpr ⟨b,hb,ha⟩)).1.le

private theorem optimal_bins_separate (I : Multiset ℝ)
    (P : Multiset (Multiset ℝ)) (hP : IsPacking I P) (hcard : P.card=OPT I)
    (b c : Multiset ℝ) (hb : b ∈ P) (hc : c ∈ P.erase b) : 1 < b.sum+c.sum := by
  classical
  by_contra hn
  have hbc : b.sum+c.sum ≤ 1 := le_of_not_gt hn
  let Q:=(b+c) ::ₘ ((P.erase b).erase c)
  have he : P=b ::ₘ c ::ₘ ((P.erase b).erase c) := by
    rw [Multiset.cons_erase hc,Multiset.cons_erase hb]
  have hQ : IsPacking I Q := by
    constructor
    · have hh:=hP.1
      rw [he] at hh
      simpa [Q,Multiset.join_cons,add_assoc] using hh
    · intro a ha
      rcases Multiset.mem_cons.mp ha with rfl|ha
      · simpa using hbc
      · exact hP.2 a (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase ha))
  have ho:=opt_le_card I Q hQ
  rw [← hcard,he] at ho
  simp only [Q,Multiset.card_cons] at ho
  omega

private theorem size_le_card (I : Multiset ℝ) (P : Multiset (Multiset ℝ))
    (hP : IsPacking I P) : SIZE I ≤ (P.card : ℝ) := by
  have hh (Q : Multiset (Multiset ℝ)) : (∀ b ∈ Q,b.sum ≤ 1) → (Q.map Multiset.sum).sum ≤ (Q.card : ℝ) := by
    induction Q using Multiset.induction_on with
    | empty => simp
    | @cons b Q ih =>
      intro h
      have hb:=h b (by simp)
      have hQ:=ih (fun a ha => h a (by simp [ha]))
      simp only [Multiset.map_cons,Multiset.sum_cons,Multiset.card_cons,Nat.cast_add,Nat.cast_one]
      linarith
  rw [SIZE,← hP.1,Multiset.sum_join]
  exact hh P hP.2


private theorem size_le_opt (I : Multiset ℝ) (hI : IsInstance I) : SIZE I ≤ (OPT I : ℝ) := by
  obtain ⟨P,hP,hcard⟩:=opt_attained I hI
  simpa only [hcard] using size_le_card I P hP

private theorem sum_filter_le (I : Multiset ℝ) (hI : IsInstance I) (p : ℝ → Prop) [DecidablePred p] :
    (I.filter p).sum ≤ I.sum := by
  induction I using Multiset.induction_on with
  | empty => simp
  | @cons a I ih =>
    have ha:=(hI a (by simp)).1
    have hh:=ih (fun b hb => hI b (by simp [hb]))
    by_cases hp : p a
    · simpa [hp] using add_le_add_left hh a
    · simpa [hp] using hh.trans (by linarith : I.sum ≤ a+I.sum)

private theorem card_mul_le_sum (I : Multiset ℝ) (a : ℝ) (ha : ∀ b ∈ I,a ≤ b) :
    (I.card : ℝ)*a ≤ I.sum := by
  induction I using Multiset.induction_on with
  | empty => simp
  | @cons b I ih =>
    have hb:=ha b (by simp)
    have hh:=ih (fun c hc => ha c (by simp [hc]))
    simp only [Multiset.card_cons,Multiset.sum_cons,Nat.cast_add,Nat.cast_one]
    nlinarith


open KKBinPacking.Shared
private noncomputable def light (a : ℝ) (P : Multiset (Multiset ℝ)) : ℕ :=
  (P.filter (fun b => b.sum ≤ a)).card

private theorem light_cons (a : ℝ) (b : Multiset ℝ) (P : Multiset (Multiset ℝ)) :
    light a (b ::ₘ P)=(if b.sum ≤ a then 1 else 0)+light a P := by
  by_cases hh : b.sum ≤ a <;> simp [light,hh,add_comm]

private theorem light_add (a : ℝ) (P Q : Multiset (Multiset ℝ)) :
    light a (P+Q)=light a P+light a Q := by simp [light]

private theorem light_singleton_le (a : ℝ) (b : Multiset ℝ) : light a ({b} : Multiset (Multiset ℝ)) ≤ 1 := by
  simpa [light] using Multiset.card_le_card (Multiset.filter_le (fun c : Multiset ℝ => c.sum ≤ a) ({b} : Multiset (Multiset ℝ)))

private theorem light_into (a p : ℝ) (hp : 0 ≤ p) (P : Multiset (Multiset ℝ))
    (b : Multiset ℝ) (hb : b ∈ P) : light a (P.erase b+{p ::ₘ b}) ≤ light a P := by
  classical
  have he:=congrArg (light a) (Multiset.cons_erase hb)
  rw [light_cons] at he
  rw [light_add]
  have hi : light a ({p ::ₘ b} : Multiset (Multiset ℝ)) ≤ if b.sum ≤ a then 1 else 0 := by
    by_cases hh : b.sum ≤ a
    · simp only [hh,ite_true]
      exact light_singleton_le a (p ::ₘ b)
    · have hh2 : ¬p+b.sum ≤ a := by linarith
      simp [light,hh]
      exact lt_of_not_ge hh2
  omega

private theorem anyFit_light (g : ℝ) (P S Q) (h : AnyFit P S Q)
    (hS : ∀ p ∈ S,0 ≤ p ∧ p ≤ g/2) :
    light (1-g/2) Q ≤ max 1 (light (1-g/2) P) := by
  induction h with
  | done P => exact le_max_right _ _
  | intoBin P S Q p b hp hb hfit hrun ih =>
    have hh:=ih (fun a ha => hS a (Multiset.mem_of_mem_erase ha))
    exact hh.trans (max_le_max le_rfl (light_into _ p (hS p hp).1 P b hb))
  | newBin P S Q p hp hfit hrun ih =>
    have hh:=ih (fun a ha => hS a (Multiset.mem_of_mem_erase ha))
    have hzero : light (1-g/2) P=0 := by
      apply Multiset.card_eq_zero.mpr
      apply Multiset.filter_eq_nil.mpr
      intro b hb
      have hh:=hfit b hb
      have hp':=(hS p hp).2
      linarith
    have hnew : light (1-g/2) (P+{{p}}) ≤ 1 := by
      rw [light_add,hzero]
      simpa only [zero_add] using light_singleton_le (1-g/2) ({p} : Multiset ℝ)
    exact (hh.trans (max_le le_rfl hnew)).trans (le_max_left _ _)

private theorem anyFit_new_heavy (g : ℝ) (P S Q) (h : AnyFit P S Q)
    (hS : ∀ p ∈ S,0 ≤ p ∧ p ≤ g/2) :
    Q.card ≤ P.card ∨ light (1-g/2) Q ≤ 1 := by
  induction h with
  | done P => exact Or.inl le_rfl
  | intoBin P S Q p b hp hb hfit hrun ih =>
    rcases ih (fun a ha => hS a (Multiset.mem_of_mem_erase ha)) with hh|hh
    · left
      have hpos : 0 < P.card := Multiset.card_pos.mpr (by intro he;simpa [he] using hb)
      simp only [Multiset.card_add,Multiset.card_singleton,Multiset.card_erase_of_mem hb,Nat.pred_eq_sub_one] at hh
      omega
    · exact Or.inr hh
  | newBin P S Q p hp hfit hrun ih =>
    right
    have hh:=anyFit_light g (P+{{p}}) (S.erase p) Q hrun
      (fun a ha => hS a (Multiset.mem_of_mem_erase ha))
    have hzero : light (1-g/2) P=0 := by
      apply Multiset.card_eq_zero.mpr
      apply Multiset.filter_eq_nil.mpr
      intro b hb
      have hh:=hfit b hb
      have hp':=(hS p hp).2
      linarith
    have hnew : light (1-g/2) (P+{{p}}) ≤ 1 := by
      rw [light_add,hzero]
      simpa only [zero_add] using light_singleton_le (1-g/2) ({p} : Multiset ℝ)
    exact hh.trans (max_le le_rfl hnew)

private theorem anyFit_join (P S Q) (h : AnyFit P S Q) : Q.join=P.join+S := by
  induction h with
  | done P => simp
  | intoBin P S Q p b hp hb hfit hrun ih =>
    have hbj : b+(P.erase b).join=P.join := by
      simpa only [Multiset.join_cons] using congrArg Multiset.join (Multiset.cons_erase hb)
    have hpj : ({p} : Multiset ℝ)+S.erase p=S := by
      simpa only [Multiset.singleton_add] using Multiset.cons_erase hp
    calc
      Q.join = (P.erase b+{p ::ₘ b}).join+S.erase p := ih
      _ = (b+(P.erase b).join)+({p}+S.erase p) := by
        simp only [Multiset.join_add,Multiset.join_cons,Multiset.join_zero,add_zero]
        simp only [Multiset.singleton_join]
        rw [← Multiset.singleton_add]
        ac_rfl
      _ = _ := by rw [hbj,hpj]
  | newBin P S Q p hp hfit hrun ih =>
    have hpj : ({p} : Multiset ℝ)+S.erase p=S := by
      simpa only [Multiset.singleton_add] using Multiset.cons_erase hp
    calc
      Q.join = (P+{{p}}).join+S.erase p := ih
      _ = P.join+({p}+S.erase p) := by simp [add_assoc]
      _ = _ := by rw [hpj]

private theorem anyFit_capacity (P S Q) (h : AnyFit P S Q)
    (hP : ∀ b ∈ P,b.sum ≤ 1) (hS : ∀ p ∈ S,p ≤ 1) : ∀ b ∈ Q,b.sum ≤ 1 := by
  induction h with
  | done P => exact hP
  | intoBin P S Q p b hp hb hfit hrun ih =>
    apply ih
    · intro c hc
      rcases Multiset.mem_add.mp hc with hc|hc
      · exact hP c (Multiset.mem_of_mem_erase hc)
      · have he : c=p ::ₘ b := by simpa using hc
        rw [he,Multiset.sum_cons]
        linarith
    · intro a ha
      exact hS a (Multiset.mem_of_mem_erase ha)
  | newBin P S Q p hp hfit hrun ih =>
    apply ih
    · intro c hc
      rcases Multiset.mem_add.mp hc with hc|hc
      · exact hP c hc
      · have he : c={p} := by simpa using hc
        simpa only [he,Multiset.sum_singleton] using hS p hp
    · intro a ha
      exact hS a (Multiset.mem_of_mem_erase ha)

private theorem heavy_card_bound (a α : ℝ) (hα : 0 ≤ α) (hprod : 1 ≤ α*a)
    (P : Multiset (Multiset ℝ)) (hP : ∀ b ∈ P,0 ≤ b.sum) :
    (P.card : ℝ) ≤ α*(P.map Multiset.sum).sum+(light a P : ℝ) := by
  induction P using Multiset.induction_on with
  | empty => simp [light]
  | @cons b P ih =>
    have hb:=hP b (by simp)
    have hh:=ih (fun c hc => hP c (by simp [hc]))
    rw [Multiset.card_cons,Multiset.map_cons,Multiset.sum_cons,light_cons]
    by_cases hl : b.sum ≤ a
    · simp only [hl,ite_true,Nat.cast_add,Nat.cast_one]
      nlinarith [mul_nonneg hα hb]
    · have hmul:=mul_le_mul_of_nonneg_left (le_of_not_ge hl) hα
      simp only [hl,ite_false,zero_add,Nat.cast_add,Nat.cast_one]
      nlinarith

theorem solution (I : Multiset ℝ) (hI : IsInstance I) (g : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1)
    (P₀ : Multiset (Multiset ℝ)) (hP₀ : IsPacking (I.filter (fun x => g / 2 < x)) P₀)
    (P : Multiset (Multiset ℝ)) (hP : AnyFit P₀ (I.filter (fun x => x ≤ g / 2)) P) :
    (Multiset.card P : ℝ) ≤ max (Multiset.card P₀ : ℝ) ((1 + g) * (OPT I : ℝ) + 1) := by
  have hS : ∀ p ∈ I.filter (fun x => x ≤ g/2),0 ≤ p ∧ p ≤ g/2 := by
    intro p hp
    exact ⟨(hI p (Multiset.mem_filter.mp hp).1).1.le,(Multiset.mem_filter.mp hp).2⟩
  have hpack : IsPacking I P := by
    constructor
    · rw [anyFit_join _ _ _ hP,hP₀.1]
      simpa only [not_lt] using Multiset.filter_add_not (fun x => g/2<x) I
    · exact anyFit_capacity _ _ _ hP hP₀.2 (fun p hp => (hI p (Multiset.mem_filter.mp hp).1).2.le)
  rcases anyFit_new_heavy g _ _ _ hP hS with hh|hh
  · exact (Nat.cast_le.mpr hh).trans (le_max_left _ _)
  · apply le_trans _ (le_max_right _ _)
    have hc:=heavy_card_bound (1-g/2) (1+g) (by positivity)
      (by nlinarith [mul_nonneg hg0.le (sub_nonneg.mpr hg1)]) P (fun b hb => bin_nonneg I hI P hpack b hb)
    have hl : (light (1-g/2) P : ℝ) ≤ 1 := by exact_mod_cast hh
    have hsum : (P.map Multiset.sum).sum=SIZE I := by rw [← Multiset.sum_join,hpack.1];rfl
    rw [hsum] at hc
    have ho:=mul_le_mul_of_nonneg_left (size_le_opt I hI) (show 0 ≤ 1+g by positivity)
    linarith
