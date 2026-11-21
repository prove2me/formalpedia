-- Prove2me | solution 1 for MoranYanPAC.Main.good_subset
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:02:59.866166+00:00
-- url     : https://prove2.me/submissions/e9672ac6-91bc-41d1-ae81-2593189c3780

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

theorem hasTree_zero {C : Set (X → Bool)} (hX : Nonempty X) (hC : C.Nonempty) : HasTree C 0 := by
  obtain ⟨f, hf⟩ := hC
  exact ⟨fun _ => Classical.arbitrary X, fun y => ⟨f, hf, fun t => t.elim0⟩⟩

end MoranYanPAC.Dev.Dim
end

section
set_option autoImplicit false

namespace MoranYanPAC.Dev.L8

open UnderstandingML MoranYanPAC.Dev.Basic MoranYanPAC.Dev.Dim MoranYanPAC.Main

variable {X : Type*}

theorem not_good_branches (d : ℕ) (G : Finset (X → Bool)) (hG : G.Nonempty) (hng : ¬ Good d G) :
    ∃ x : X, ∀ b : Bool, G.card ≤ 2 * (d + 1) * (G.filter (fun g => g x = b)).card := by
  classical
  have hpos : 0 < G.card := Finset.card_pos.2 hG
  have : ∃ x : X, ¬ (2 * (d + 1) * (G.filter (fun h => h x ≠ majority G x)).card < G.card) := by
    by_contra hc
    push Not at hc
    exact hng ⟨hG, fun x => by simpa using hc x⟩
  obtain ⟨x, hx⟩ := this
  refine ⟨x, fun b => ?_⟩
  push Not at hx
  have hsum : G.card = (G.filter (fun h => h x = false)).card + (G.filter (fun h => h x = true)).card := by
    have := Finset.card_filter_add_card_filter_not (s := G) (fun h => h x = false)
    rw [← this]
    congr 2
    apply Finset.filter_congr
    intro h _; simp
  have hq : 2 ≤ 2 * (d + 1) := by omega
  unfold majority at hx
  set nF := (G.filter (fun h => h x = false)).card with hnF
  set nT := (G.filter (fun h => h x = true)).card with hnT
  by_cases hlt : nF < nT
  · have hc : (G.filter (fun h => h x ≠ decide (nF < nT))).card = nF := by
      simp only [hlt, decide_true]
      rw [hnF]; congr 1; apply Finset.filter_congr; intro h _; simp
    rw [hc] at hx
    cases b
    · simpa using hx
    · have : G.card ≤ 2 * nT := by omega
      simpa using this.trans (Nat.mul_le_mul_right _ hq)
  · have hc : (G.filter (fun h => h x ≠ decide (nF < nT))).card = nT := by
      simp only [hlt, decide_false]
      rw [hnT]; congr 1; apply Finset.filter_congr; intro h _; simp
    rw [hc] at hx
    cases b
    · have : G.card ≤ 2 * nF := by omega
      simpa using this.trans (Nat.mul_le_mul_right _ hq)
    · simpa using hx

theorem aux (d : ℕ) : ∀ t : ℕ, ∀ G : Finset (X → Bool), G.Nonempty → ldim (G : Set (X → Bool)) ≤ t →
    ∃ G' : Finset (X → Bool), G' ⊆ G ∧ Good d G' ∧ G.card ≤ (2 * (d + 1)) ^ t * G'.card := by
  classical
  intro t
  induction t with
  | zero =>
    intro G hG hl
    by_cases hg : Good d G
    · exact ⟨G, subset_rfl, hg, by simp⟩
    · exfalso
      obtain ⟨x, hx⟩ := not_good_branches d G hG hg
      have hX : Nonempty X := ⟨x⟩
      have hpos : 0 < G.card := Finset.card_pos.2 hG
      have hne : ∀ b : Bool, {f ∈ (G : Set (X → Bool)) | f x = b}.Nonempty := by
        intro b
        have hn := hx b
        have : 0 < (G.filter (fun g => g x = b)).card :=
          Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at hn; omega)
        obtain ⟨g, hg⟩ := Finset.card_pos.1 this
        exact ⟨g, (Finset.mem_filter.1 hg).1, (Finset.mem_filter.1 hg).2⟩
      have hT : HasTree (G : Set (X → Bool)) (0 + 1) :=
        hasTree_glue x (hasTree_zero hX (hne false)) (hasTree_zero hX (hne true))
      have := (le_ldim_iff (by omega)).2 hT
      have h2 : ((0 + 1 : ℕ) : ℕ∞) ≤ 0 := this.trans hl
      simp at h2
  | succ t ih =>
    intro G hG hl
    by_cases hg : Good d G
    · refine ⟨G, subset_rfl, hg, ?_⟩
      have : 1 ≤ (2 * (d + 1)) ^ (t + 1) := Nat.one_le_pow _ _ (by omega)
      nlinarith
    · obtain ⟨x, hx⟩ := not_good_branches d G hG hg
      have hpos : 0 < G.card := Finset.card_pos.2 hG
      have hset : ∀ b : Bool, (↑(G.filter (fun g => g x = b)) : Set (X → Bool)) =
          {f ∈ (G : Set (X → Bool)) | f x = b} := by
        intro b; ext f; simp
      have hne : ∀ b : Bool, (G.filter (fun g => g x = b)).Nonempty := by
        intro b
        have hn := hx b
        exact Finset.card_pos.1 (Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at hn; omega))
      have hbranch : ∃ b : Bool, ldim (↑(G.filter (fun g => g x = b)) : Set (X → Bool)) ≤ t := by
        by_contra hc
        push Not at hc
        have hb : ∀ b : Bool, HasTree {f ∈ (G : Set (X → Bool)) | f x = b} (t + 1) := by
          intro b
          have := hc b
          rw [hset] at this
          exact (le_ldim_iff (by omega)).1 (by exact_mod_cast Order.add_one_le_of_lt this)
        have hT := hasTree_glue x (hb false) (hb true)
        have := (le_ldim_iff (by omega)).2 hT
        have h2 := this.trans hl
        have : t + 1 + 1 ≤ t + 1 := by exact_mod_cast h2
        omega
      obtain ⟨b, hb⟩ := hbranch
      obtain ⟨G'', hsub, hgood, hcard⟩ := ih _ (hne b) hb
      refine ⟨G'', hsub.trans (Finset.filter_subset _ _), hgood, ?_⟩
      calc G.card ≤ 2 * (d + 1) * (G.filter (fun g => g x = b)).card := hx b
        _ ≤ 2 * (d + 1) * ((2 * (d + 1)) ^ t * G''.card) := Nat.mul_le_mul_left _ hcard
        _ = (2 * (d + 1)) ^ (t + 1) * G''.card := by ring

end MoranYanPAC.Dev.L8

namespace MoranYanPAC.Main

open UnderstandingML MoranYanPAC.Dev.L8

theorem chk_good_subset {X : Type*} (d : ℕ) (hd1 : 1 ≤ d)
    (G : Finset (X → Bool)) (hG : G.Nonempty) (t : ℕ)
    (ht : UnderstandingML.ldimBot (G : Set (X → Bool)) ≤ (t : WithBot ℕ∞)) :
    ∃ G' : Finset (X → Bool), G' ⊆ G ∧ Good d G' ∧
      (G.card : ℝ) / (2 * ((d : ℝ) + 1)) ^ t ≤ G'.card := by
  have hne : (G : Set (X → Bool)).Nonempty := by simpa using hG
  unfold UnderstandingML.ldimBot at ht
  rw [if_pos hne] at ht
  have hl : ldim (G : Set (X → Bool)) ≤ t := by
    have : ((ldim (G : Set (X → Bool)) : ℕ∞) : WithBot ℕ∞) ≤ ((t : ℕ∞) : WithBot ℕ∞) := by
      rw [WithBot.coe_natCast]; exact ht
    exact WithBot.coe_le_coe.1 this
  obtain ⟨G', hsub, hgood, hcard⟩ := aux d t G hG hl
  refine ⟨G', hsub, hgood, ?_⟩
  have hpos : (0 : ℝ) < (2 * ((d : ℝ) + 1)) ^ t := by positivity
  rw [div_le_iff₀ hpos]
  have : (G.card : ℝ) ≤ ((2 * (d + 1)) ^ t * G'.card : ℕ) := by exact_mod_cast hcard
  push_cast at this
  linarith

end MoranYanPAC.Main
end

theorem solution : type_of% @MoranYanPAC.Main.chk_good_subset := @MoranYanPAC.Main.chk_good_subset
