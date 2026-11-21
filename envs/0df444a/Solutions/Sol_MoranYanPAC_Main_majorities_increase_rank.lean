-- Prove2me | solution 1 for MoranYanPAC.Main.majorities_increase_rank
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:59:14.394176+00:00
-- url     : https://prove2.me/submissions/29cdca72-2a78-4dd3-bd7e-0390b9adf2c6

import Mathlib
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_PrivLittlestone_localUniverse
import Definitions.Def_PrivLittlestone_rankLayer
import Definitions.Def_PrivLittlestone_restrictCls
import Definitions.Def_MoranYanPAC_Main_GoodFamily

section
set_option autoImplicit false

namespace MoranYanPAC.Dev.Basic

open UnderstandingML

variable {X : Type*}

def HasTree (H : Set (X → Bool)) (k : ℕ) : Prop := ∃ v : List Bool → X, ShattersTree H k v

theorem HasTree.mono {C H : Set (X → Bool)} {k : ℕ} (hCH : C ⊆ H) (h : HasTree C k) :
    HasTree H k := by
  obtain ⟨v, hv⟩ := h
  refine ⟨v, fun y => ?_⟩
  obtain ⟨f, hf, hf2⟩ := hv y
  exact ⟨f, hCH hf, hf2⟩

theorem HasTree.le {H : Set (X → Bool)} {k j : ℕ} (hjk : j ≤ k) (h : HasTree H k) :
    HasTree H j := by
  obtain ⟨v, hv⟩ := h
  refine ⟨v, fun y => ?_⟩
  let y' : Fin k → Bool := fun i => if hi : (i : ℕ) < j then y ⟨i, hi⟩ else false
  obtain ⟨f, hf, hf2⟩ := hv y'
  refine ⟨f, hf, fun t => ?_⟩
  have h1 := hf2 ⟨t, lt_of_lt_of_le t.2 hjk⟩
  have h2 : (List.ofFn (fun i : Fin ((⟨t, lt_of_lt_of_le t.2 hjk⟩ : Fin k) : ℕ) =>
      y' ⟨i, lt_trans i.2 (lt_of_lt_of_le t.2 hjk)⟩)) =
      List.ofFn (fun i : Fin (t : ℕ) => y ⟨i, lt_trans i.2 t.2⟩) := by
    apply List.ext_get (by simp)
    intro n h1 h2
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    simp only [y']
    have : (n : ℕ) < j := lt_trans h2 (by simpa using t.2)
    simp [this]
  rw [h2] at h1
  rw [h1]
  simp [y', t.2]

theorem le_ldim_iff {H : Set (X → Bool)} {k : ℕ} (hk : 1 ≤ k) :
    (k : ℕ∞) ≤ ldim H ↔ HasTree H k := by
  constructor
  · intro hle
    by_contra hn
    have : ldim H ≤ ((k - 1 : ℕ) : ℕ∞) := by
      refine iSup₂_le fun d hd => ?_
      have hdk : d < k := by
        by_contra hc
        exact hn (HasTree.le (not_lt.1 hc) hd)
      exact_mod_cast Nat.le_sub_one_of_lt hdk
    have h2 := hle.trans this
    have : k ≤ k - 1 := by exact_mod_cast h2
    omega
  · intro h
    exact le_iSup₂ (f := fun (d : ℕ) (_ : ∃ v : List Bool → X, ShattersTree H d v) => (d : ℕ∞)) k h

theorem path_succ {k : ℕ} (y : Fin (k + 1) → Bool) (t : Fin k) :
    List.ofFn (fun j : Fin ((t.succ : Fin (k + 1)) : ℕ) => y ⟨j, lt_trans j.2 t.succ.2⟩) =
      y 0 :: List.ofFn (fun j : Fin (t : ℕ) => Fin.tail y ⟨j, lt_trans j.2 t.2⟩) := by
  have : ((t.succ : Fin (k + 1)) : ℕ) = (t : ℕ) + 1 := rfl
  apply List.ext_get (by simp)
  intro n h1 h2
  simp only [List.get_eq_getElem, List.getElem_ofFn]
  cases n with
  | zero => rfl
  | succ n => simp [Fin.tail]

theorem hasTree_glue {H : Set (X → Bool)} {k : ℕ} (x : X)
    (h0 : HasTree {f ∈ H | f x = false} k) (h1 : HasTree {f ∈ H | f x = true} k) :
    HasTree H (k + 1) := by
  obtain ⟨v0, hv0⟩ := h0
  obtain ⟨v1, hv1⟩ := h1
  refine ⟨fun l => match l with | [] => x | b :: l => if b then v1 l else v0 l, fun y => ?_⟩
  have key : ∃ f ∈ H, f x = y 0 ∧ ∀ t : Fin k,
      f ((if y 0 then v1 else v0) (List.ofFn (fun j : Fin (t : ℕ) => Fin.tail y ⟨j, lt_trans j.2 t.2⟩))) =
        Fin.tail y t := by
    cases hb : y 0
    · obtain ⟨f, hf, hf2⟩ := hv0 (Fin.tail y)
      exact ⟨f, hf.1, hf.2, fun t => by simpa using hf2 t⟩
    · obtain ⟨f, hf, hf2⟩ := hv1 (Fin.tail y)
      exact ⟨f, hf.1, hf.2, fun t => by simpa using hf2 t⟩
  obtain ⟨f, hfH, hfx, hft⟩ := key
  refine ⟨f, hfH, fun t => ?_⟩
  induction t using Fin.cases with
  | zero => simpa using hfx
  | succ t =>
    rw [path_succ]
    have := hft t
    simp only [Fin.tail] at this
    cases hb : y 0 <;> simp_all [Fin.tail]

end MoranYanPAC.Dev.Basic
end

section
set_option autoImplicit false

namespace MoranYanPAC.Dev.Dim

open UnderstandingML MoranYanPAC.Dev.Basic PrivLittlestone

variable {X : Type*}

theorem nonempty_of_ldim {H : Set (X → Bool)} {d : ℕ} (hd : ldim H = d) (hd1 : 1 ≤ d) :
    Nonempty X := by
  have : HasTree H d := (le_ldim_iff hd1).1 (le_of_eq hd.symm)
  obtain ⟨v, _⟩ := this
  exact ⟨v []⟩

theorem hasTree_zero {C : Set (X → Bool)} (hX : Nonempty X) (hC : C.Nonempty) : HasTree C 0 := by
  obtain ⟨f, hf⟩ := hC
  exact ⟨fun _ => Classical.arbitrary X, fun y => ⟨f, hf, fun t => t.elim0⟩⟩

theorem layer_mono (H : Set (X → Bool)) (d : ℕ) {s t : ℕ} (hts : t ≤ s) {g : X → Bool}
    (hg : g ∈ rankLayer H d s) : g ∈ rankLayer H d t := by
  induction s with
  | zero => have : t = 0 := by omega
            subst this; exact hg
  | succ s ih =>
    rcases Nat.lt_or_ge t (s + 1) with h | h
    · exact ih (by omega) hg.1
    · have : t = s + 1 := by omega
      subst this; exact hg

theorem layer_base (hX : Nonempty X) (H : Set (X → Bool)) (d s : ℕ) {g : X → Bool}
    (hg : g ∈ rankLayer H d s) (A : Finset X) (hA : A.card + s ≤ d + 1) :
    HasTree (restrictCls H g A) s := by
  cases s with
  | zero =>
    have hg0 : g ∈ localUniverse H d := hg
    exact hasTree_zero hX (hg0 A (by omega))
  | succ s =>
    have := hg.2 A (by omega)
    exact (le_ldim_iff (by omega)).1 this

end MoranYanPAC.Dev.Dim
end

section
set_option autoImplicit false

namespace MoranYanPAC.Main

open UnderstandingML MoranYanPAC.Dev.Basic MoranYanPAC.Dev.Dim PrivLittlestone

theorem agree_count {X : Type*} (d : ℕ) (G : Finset (X → Bool)) (hgood : Good d G)
    (A : Finset X) (hA : A.card ≤ d + 1) :
    G.card < 2 * (G.filter (fun g => ∀ x ∈ A, g x = majority G x)).card := by
  classical
  have hpos : 0 < G.card := Finset.card_pos.2 hgood.1
  have hsplit := Finset.card_filter_add_card_filter_not (s := G) (fun g => ∀ x ∈ A, g x = majority G x)
  set bad := G.filter (fun g => ¬ ∀ x ∈ A, g x = majority G x) with hbad
  suffices 2 * bad.card < G.card by omega
  rcases A.eq_empty_or_nonempty with he | hne
  · have : bad = ∅ := by
      rw [hbad]; apply Finset.filter_false_of_mem; intro g _; simp [he]
    rw [this]; simpa using hpos
  · have hcov : bad ⊆ A.biUnion (fun x => G.filter (fun g => g x ≠ majority G x)) := by
      intro g hg
      obtain ⟨hgG, hgn⟩ := Finset.mem_filter.1 hg
      push Not at hgn
      obtain ⟨x, hx, hne⟩ := hgn
      exact Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_filter.2 ⟨hgG, hne⟩⟩
    have h1 := (Finset.card_le_card hcov).trans Finset.card_biUnion_le
    have h3 : ∀ x ∈ A, 2 * (d + 1) * (G.filter (fun g => g x ≠ majority G x)).card < G.card :=
      fun x _ => hgood.2 x
    have h5 := Finset.sum_lt_sum_of_nonempty hne h3
    simp only [Finset.sum_const, smul_eq_mul] at h5
    have h6 : 2 * (d + 1) * bad.card ≤
        ∑ x ∈ A, 2 * (d + 1) * (G.filter (fun g => g x ≠ majority G x)).card := by
      rw [← Finset.mul_sum]; exact Nat.mul_le_mul_left _ h1
    have h7 : A.card * G.card ≤ (d + 1) * G.card := Nat.mul_le_mul_right _ hA
    have : (d + 1) * (2 * bad.card) < (d + 1) * G.card := by nlinarith
    exact lt_of_mul_lt_mul_left this (Nat.zero_le _)

theorem chk_majorities_increase_rank {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d)
    (s : ℕ) (hs : s < d) (G : Finset (X → Bool)) (hcard : 2 ≤ G.card)
    (hG : ∀ h ∈ G, h ∈ PrivLittlestone.rankLayer H d s) (hgood : Good d G) :
    majority G ∈ PrivLittlestone.rankLayer H d (s + 1) := by
  classical
  have hX := nonempty_of_ldim hd hd1
  have hAgree : ∀ A : Finset X, A.card ≤ d + 1 → ∃ g ∈ G, ∀ x ∈ A, g x = majority G x := by
    intro A hA
    have := agree_count d G hgood A hA
    have : 0 < (G.filter (fun g => ∀ x ∈ A, g x = majority G x)).card := by omega
    obtain ⟨g, hg⟩ := Finset.card_pos.1 this
    exact ⟨g, (Finset.mem_filter.1 hg).1, (Finset.mem_filter.1 hg).2⟩
  have hres : ∀ (g : X → Bool) (A : Finset X), (∀ x ∈ A, g x = majority G x) →
      restrictCls H g A = restrictCls H (majority G) A := by
    intro g A hg
    ext f
    simp only [restrictCls, Set.mem_setOf_eq]
    exact and_congr_right fun _ => forall_congr' fun x => forall_congr' fun hx => by rw [hg x hx]
  have hFs : ∀ t, t ≤ s → majority G ∈ rankLayer H d t := by
    intro t
    induction t with
    | zero =>
      intro _ A hA
      obtain ⟨g, hgG, hg⟩ := hAgree A hA
      have hgU : g ∈ localUniverse H d := layer_mono H d (Nat.zero_le s) (hG g hgG)
      have := hgU A hA
      rwa [hres g A hg] at this
    | succ t ih =>
      intro hts
      refine ⟨ih (by omega), fun A hA => ?_⟩
      obtain ⟨g, hgG, hg⟩ := hAgree A (by omega)
      have hgt : g ∈ rankLayer H d (t + 1) := layer_mono H d hts (hG g hgG)
      have := hgt.2 A hA
      rwa [hres g A hg] at this
  refine ⟨hFs s le_rfl, fun A hA => ?_⟩
  have hc := agree_count d G hgood A (by omega)
  set GA := G.filter (fun g => ∀ x ∈ A, g x = majority G x) with hGA
  have h2 : 2 ≤ GA.card := by omega
  obtain ⟨g1, hg1, g2, hg2, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < GA.card)
  have hg1' := Finset.mem_filter.1 hg1
  have hg2' := Finset.mem_filter.1 hg2
  obtain ⟨x, hx⟩ : ∃ x, g1 x ≠ g2 x := by
    by_contra hc
    push Not at hc
    exact hne (funext hc)
  have step : ∀ gb ∈ GA, HasTree {f ∈ restrictCls H (majority G) A | f x = gb x} s := by
    intro gb hgb
    have hgb' := Finset.mem_filter.1 hgb
    have hbase := layer_base hX H d s (hG gb hgb'.1) (insert x A)
      (by have := Finset.card_insert_le x A; omega)
    refine HasTree.mono ?_ hbase
    intro f hf
    refine ⟨⟨hf.1, fun y hy => ?_⟩, hf.2 x (Finset.mem_insert_self x A)⟩
    rw [hf.2 y (Finset.mem_insert_of_mem hy), hgb'.2 y hy]
  have hT : HasTree (restrictCls H (majority G) A) (s + 1) := by
    cases h1 : g1 x
    · have h2' : g2 x = true := by cases h : g2 x <;> simp_all
      exact hasTree_glue x (by simpa [h1] using step g1 hg1) (by simpa [h2'] using step g2 hg2)
    · have h2' : g2 x = false := by cases h : g2 x <;> simp_all
      exact hasTree_glue x (by simpa [h2'] using step g2 hg2) (by simpa [h1] using step g1 hg1)
  exact_mod_cast (le_ldim_iff (by omega)).2 hT

end MoranYanPAC.Main
end

theorem solution : type_of% @MoranYanPAC.Main.chk_majorities_increase_rank := @MoranYanPAC.Main.chk_majorities_increase_rank
