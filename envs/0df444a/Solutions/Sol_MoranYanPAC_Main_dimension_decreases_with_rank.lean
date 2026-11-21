-- Prove2me | solution 1 for MoranYanPAC.Main.dimension_decreases_with_rank
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:53:58.322915+00:00
-- url     : https://prove2.me/submissions/6444ad15-82b6-4304-a17d-96e0d40b0574

import Mathlib
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_PrivLittlestone_localUniverse
import Definitions.Def_PrivLittlestone_rankLayer
import Definitions.Def_PrivLittlestone_restrictCls

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

theorem branch_tree {H : Set (X → Bool)} {k : ℕ} {v : List Bool → X} (hv : ShattersTree H (k + 1) v)
    (b : Bool) : HasTree {f ∈ H | f (v []) = b} k := by
  refine ⟨fun l => v (b :: l), fun y => ?_⟩
  obtain ⟨f, hf, hf2⟩ := hv (Fin.cons b y)
  refine ⟨f, ⟨hf, by simpa using hf2 0⟩, fun t => ?_⟩
  have := hf2 t.succ
  rw [path_succ] at this
  simpa using this

theorem hasTree_split {H : Set (X → Bool)} {k : ℕ} (h : HasTree H (k + 1)) :
    ∃ x : X, (∃ g ∈ H, g x = false) ∧ (∃ g ∈ H, g x = true) ∧
      HasTree {f ∈ H | f x = false} k ∧ HasTree {f ∈ H | f x = true} k := by
  obtain ⟨v, hv⟩ := h
  refine ⟨v [], ?_, ?_, branch_tree hv false, branch_tree hv true⟩
  · obtain ⟨f, hf, hf2⟩ := hv (Fin.cons false (fun _ => false))
    exact ⟨f, hf, by simpa using hf2 0⟩
  · obtain ⟨f, hf, hf2⟩ := hv (Fin.cons true (fun _ => false))
    exact ⟨f, hf, by simpa using hf2 0⟩

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

theorem claim (hX : Nonempty X) (H : Set (X → Bool)) (d s : ℕ) (C : Set (X → Bool))
    (hC : C ⊆ rankLayer H d s) :
    ∀ (j : ℕ) (A : Finset X) (g : X → Bool), g ∈ C →
      HasTree {f ∈ C | ∀ x ∈ A, f x = g x} j → A.card + j + s ≤ d + 1 →
      HasTree (restrictCls H g A) (s + j) := by
  classical
  intro j
  induction j with
  | zero =>
    intro A g hg _ hA
    exact layer_base hX H d s (hC hg) A (by omega)
  | succ j ih =>
    intro A g hg hT hA
    obtain ⟨x, ⟨g0, hg0, hx0⟩, ⟨g1, hg1, hx1⟩, T0, T1⟩ := hasTree_split hT
    have step : ∀ (b : Bool) (gb : X → Bool), gb ∈ {f ∈ C | ∀ x ∈ A, f x = g x} → gb x = b →
        HasTree {f ∈ {f ∈ C | ∀ x ∈ A, f x = g x} | f x = b} j →
        HasTree {f ∈ restrictCls H g A | f x = b} (s + j) := by
      intro b gb hgb hxb Tb
      have h1 : HasTree {f ∈ C | ∀ y ∈ insert x A, f y = gb y} j := by
        refine HasTree.mono ?_ Tb
        intro f hf
        refine ⟨hf.1.1, fun y hy => ?_⟩
        rcases Finset.mem_insert.1 hy with rfl | hy
        · rw [hf.2, hxb]
        · rw [hf.1.2 y hy, hgb.2 y hy]
      have h2 := ih (insert x A) gb hgb.1 h1
        (le_trans (by have := Finset.card_insert_le x A; omega) hA)
      refine HasTree.mono ?_ h2
      intro f hf
      refine ⟨⟨hf.1, fun y hy => ?_⟩, ?_⟩
      · rw [hf.2 y (Finset.mem_insert_of_mem hy), hgb.2 y hy]
      · rw [hf.2 x (Finset.mem_insert_self x A), hxb]
    exact hasTree_glue x (step false g0 hg0 hx0 T0) (step true g1 hg1 hx1 T1)

end MoranYanPAC.Dev.Dim
end

section
set_option autoImplicit false

namespace MoranYanPAC.Dev.L4

open UnderstandingML MoranYanPAC.Dev.Basic MoranYanPAC.Dev.Dim PrivLittlestone

variable {X : Type*}

theorem ldim_mono {C H : Set (X → Bool)} (h : C ⊆ H) : ldim C ≤ ldim H := by
  refine iSup₂_le fun d hd => ?_
  exact le_iSup₂ (f := fun (d : ℕ) (_ : ∃ v : List Bool → X, ShattersTree H d v) => (d : ℕ∞)) d
    (HasTree.mono h hd)

theorem ldim_le_sub (H : Set (X → Bool)) (d : ℕ) (hd : ldim H = d) (hd1 : 1 ≤ d)
    (s : ℕ) (hs : s ≤ d) (C : Set (X → Bool)) (hC : C ⊆ rankLayer H d s) (hne : C.Nonempty) :
    ldim C ≤ ((d - s : ℕ) : ℕ∞) := by
  have hX := nonempty_of_ldim hd hd1
  by_contra hlt
  push_neg at hlt
  have h1 : (((d - s + 1 : ℕ)) : ℕ∞) ≤ ldim C := by
    have := Order.add_one_le_of_lt hlt
    simpa using this
  have hT : HasTree C (d - s + 1) := (le_ldim_iff (by omega)).1 h1
  obtain ⟨g, hg⟩ := hne
  have h2 := claim hX H d s C hC (d - s + 1) ∅ g hg
    (HasTree.mono (fun f hf => ⟨hf, by simp⟩) hT) (by simp; omega)
  have h3 : HasTree H (s + (d - s + 1)) := HasTree.mono (fun f hf => hf.1) h2
  have h4 : ((s + (d - s + 1) : ℕ) : ℕ∞) ≤ ldim H := (le_ldim_iff (by omega)).2 h3
  rw [hd] at h4
  have : s + (d - s + 1) ≤ d := by exact_mod_cast h4
  omega

end MoranYanPAC.Dev.L4

namespace MoranYanPAC.Main

open UnderstandingML MoranYanPAC.Dev.Basic MoranYanPAC.Dev.Dim MoranYanPAC.Dev.L4

theorem chk_dimension_decreases_with_rank {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d) :
    (∀ s : ℕ, s ≤ d →
      UnderstandingML.ldimBot (PrivLittlestone.rankLayer H d s) ≤
        ((d - s : ℕ) : WithBot ℕ∞)) ∧
    UnderstandingML.ldimBot (PrivLittlestone.localUniverse H d) = (d : WithBot ℕ∞) := by
  have hUne : (PrivLittlestone.localUniverse H d).Nonempty := by
    obtain ⟨h, hh⟩ := hH
    exact ⟨h, fun A _ => ⟨h, hh, fun _ _ => rfl⟩⟩
  refine ⟨fun s hs => ?_, ?_⟩
  · unfold UnderstandingML.ldimBot
    split_ifs with hne
    · have := ldim_le_sub H d hd hd1 s hs _ (subset_refl _) hne
      exact (WithBot.coe_le_coe.2 this).trans_eq (WithBot.coe_natCast _)
    · exact bot_le
  · unfold UnderstandingML.ldimBot
    rw [if_pos hUne]
    have h1 : ldim (PrivLittlestone.localUniverse H d) ≤ ((d - 0 : ℕ) : ℕ∞) :=
      ldim_le_sub H d hd hd1 0 (Nat.zero_le _) _ (subset_refl _) hUne
    have h2 : ldim H ≤ ldim (PrivLittlestone.localUniverse H d) := by
      apply ldim_mono
      intro h hh
      exact fun A _ => ⟨h, hh, fun _ _ => rfl⟩
    have h3 : ldim (PrivLittlestone.localUniverse H d) = d := by
      apply le_antisymm
      · simpa using h1
      · rwa [hd] at h2
    rw [h3]; simp

end MoranYanPAC.Main
end

theorem solution : type_of% @MoranYanPAC.Main.chk_dimension_decreases_with_rank := @MoranYanPAC.Main.chk_dimension_decreases_with_rank
