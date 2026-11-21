-- Prove2me | solution 1 for MoranYanPAC.Main.small_witnesses_with_soa
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:07:31.773776+00:00
-- url     : https://prove2.me/submissions/b66cfce8-d73c-46ee-9ab9-d89bcf2899a8

import Mathlib
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_PrivLittlestone_localUniverse
import Definitions.Def_PrivLittlestone_rankLayer
import Definitions.Def_PrivLittlestone_restrictCls
import Definitions.Def_PrivLittlestone_rankOf
import Definitions.Def_MoranYanPAC_Main_SOA

section
set_option autoImplicit false

namespace MoranYanPAC.Dev.Basic

open UnderstandingML

variable {X : Type*}

def HasTree (H : Set (X → Bool)) (k : ℕ) : Prop := ∃ v : List Bool → X, ShattersTree H k v

theorem HasTree.nonempty {H : Set (X → Bool)} {k : ℕ} (h : HasTree H k) : H.Nonempty := by
  obtain ⟨v, hv⟩ := h
  obtain ⟨f, hf, _⟩ := hv (fun _ => false)
  exact ⟨f, hf⟩

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

namespace MoranYanPAC.Dev.L4

open UnderstandingML MoranYanPAC.Dev.Basic MoranYanPAC.Dev.Dim PrivLittlestone

variable {X : Type*}

theorem ldim_mono {C H : Set (X → Bool)} (h : C ⊆ H) : ldim C ≤ ldim H := by
  refine iSup₂_le fun d hd => ?_
  exact le_iSup₂ (f := fun (d : ℕ) (_ : ∃ v : List Bool → X, ShattersTree H d v) => (d : ℕ∞)) d
    (HasTree.mono h hd)

end MoranYanPAC.Dev.L4

namespace MoranYanPAC.Main

open UnderstandingML MoranYanPAC.Dev.Basic MoranYanPAC.Dev.Dim MoranYanPAC.Dev.L4

end MoranYanPAC.Main
end

section
set_option autoImplicit false

namespace MoranYanPAC.Dev.L6

open UnderstandingML MoranYanPAC.Dev.Basic MoranYanPAC.Dev.Dim MoranYanPAC.Dev.L4 PrivLittlestone MoranYanPAC.Main

variable {X : Type*}

theorem ldimBot_eq_of_hasTree {C : Set (X → Bool)} {r : ℕ} (h : HasTree C r) (hle : ldim C ≤ r) :
    ldimBot C = (r : WithBot ℕ∞) := by
  unfold ldimBot
  rw [if_pos h.nonempty]
  have : ldim C = r := by
    apply le_antisymm hle
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · exact (le_ldim_iff hr).2 h
  rw [this]; exact WithBot.coe_natCast _

theorem soa_eq (hX : Nonempty X) (H : Set (X → Bool)) (d r : ℕ) {f : X → Bool}
    (hf : f ∈ rankLayer H d r) (A : Finset X) (hA : A.card + r ≤ d)
    (hdim : ldim (restrictCls H f A) ≤ r) : SOA (restrictCls H f A) = f := by
  classical
  funext x
  set C := restrictCls H f A with hC
  have hbase := layer_base hX H d r hf (insert x A)
    (by have := Finset.card_insert_le x A; omega)
  have hmain : HasTree {c ∈ C | c x = f x} r := by
    refine HasTree.mono ?_ hbase
    intro c hc
    exact ⟨⟨hc.1, fun y hy => hc.2 y (Finset.mem_insert_of_mem hy)⟩, hc.2 x (Finset.mem_insert_self x A)⟩
  have hbr : ldimBot {c ∈ C | c x = f x} = (r : WithBot ℕ∞) :=
    ldimBot_eq_of_hasTree hmain ((ldim_mono (fun c hc => hc.1)).trans hdim)
  have hopp : ∀ b : Bool, b ≠ f x → ldimBot {c ∈ C | c x = b} < (r : WithBot ℕ∞) := by
    intro b hb
    by_cases hne : ({c ∈ C | c x = b} : Set (X → Bool)).Nonempty
    · by_contra hnlt
      have hCo : HasTree {c ∈ C | c x = b} r := by
        rcases Nat.eq_zero_or_pos r with rfl | hr
        · exact hasTree_zero hX hne
        · apply (le_ldim_iff hr).1
          unfold ldimBot at hnlt
          rw [if_pos hne] at hnlt
          have : ¬ (ldim {c ∈ C | c x = b} < (r : ℕ∞)) := fun hlt =>
            hnlt (by rw [← WithBot.coe_natCast]; exact WithBot.coe_lt_coe.2 hlt)
          exact not_lt.1 this
      have hglue : HasTree C (r + 1) := by
        cases b <;> cases hfx : f x <;> simp only [hfx] at hmain hCo hb
        · exact absurd rfl hb
        · exact hasTree_glue x hCo hmain
        · exact hasTree_glue x hmain hCo
        · exact absurd rfl hb
      have h1 := (le_ldim_iff (by omega)).2 hglue
      have h2 := h1.trans hdim
      have : r + 1 ≤ r := by exact_mod_cast h2
      omega
    · unfold ldimBot
      rw [if_neg hne]
      exact (WithBot.bot_lt_coe (r : ℕ∞)).trans_eq (WithBot.coe_natCast r)
  unfold SOA
  cases hb : f x
  · have h1 := hopp true (by simp [hb])
    rw [hb] at hbr
    simp only [decide_eq_false_iff_not]
    exact not_lt.2 (hbr ▸ h1.le)
  · have h1 := hopp false (by simp [hb])
    rw [hb] at hbr
    simp only [decide_eq_true_eq]
    exact hbr ▸ h1

end MoranYanPAC.Dev.L6

namespace MoranYanPAC.Main

open UnderstandingML MoranYanPAC.Dev.Basic MoranYanPAC.Dev.Dim MoranYanPAC.Dev.L4 MoranYanPAC.Dev.L6

theorem chk_small_witnesses_with_soa {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d) :
    ∀ h ∈ PrivLittlestone.localUniverse H d, ∃ A : Finset X,
      A.card ≤ d - PrivLittlestone.rankOf H d h ∧
      UnderstandingML.ldimBot (PrivLittlestone.restrictCls H h A) =
        (PrivLittlestone.rankOf H d h : WithBot ℕ∞) ∧
      {f ∈ PrivLittlestone.localUniverse H d | ∀ x ∈ A, f x = h x} ∩
        PrivLittlestone.rankLayer H d (PrivLittlestone.rankOf H d h) = {h} ∧
      SOA (PrivLittlestone.restrictCls H h A) = h := by
  classical
  intro h hh
  have hX := nonempty_of_ldim hd hd1
  have hrd : PrivLittlestone.rankOf H d h ≤ d := Nat.findGreatest_le _
  have hhr : h ∈ PrivLittlestone.rankLayer H d (PrivLittlestone.rankOf H d h) :=
    Nat.findGreatest_spec (P := fun s => h ∈ PrivLittlestone.rankLayer H d s) (Nat.zero_le d) hh
  set r := PrivLittlestone.rankOf H d h with hr
  have hA : ∃ A : Finset X, A.card ≤ d - r ∧ ldim (PrivLittlestone.restrictCls H h A) ≤ r := by
    by_cases hrd' : r = d
    · refine ⟨∅, by simp, ?_⟩
      have : ldim (PrivLittlestone.restrictCls H h ∅) ≤ ldim H := ldim_mono (fun f hf => hf.1)
      rw [hd] at this
      rw [hrd']; exact this
    · have hlt : r < d := lt_of_le_of_ne hrd hrd'
      have hn : h ∉ PrivLittlestone.rankLayer H d (r + 1) :=
        Nat.findGreatest_is_greatest (P := fun s => h ∈ PrivLittlestone.rankLayer H d s)
          (Nat.lt_succ_self r) (by omega)
      have : ¬ ∀ A : Finset X, A.card ≤ d + 1 - (r + 1) →
          (((r + 1 : ℕ)) : ℕ∞) ≤ ldim (PrivLittlestone.restrictCls H h A) :=
        fun hall => hn ⟨hhr, hall⟩
      push Not at this
      obtain ⟨A, hAc, hAl⟩ := this
      refine ⟨A, by omega, ?_⟩
      have : ldim (PrivLittlestone.restrictCls H h A) < ((r : ℕ∞) + 1) := by simpa using hAl
      exact (ENat.lt_add_one_iff (ENat.natCast_ne_top r)).1 this
  obtain ⟨A, hAc, hAl⟩ := hA
  have hT : HasTree (PrivLittlestone.restrictCls H h A) r := layer_base hX H d r hhr A (by omega)
  have hsoa : SOA (PrivLittlestone.restrictCls H h A) = h := soa_eq hX H d r hhr A (by omega) hAl
  refine ⟨A, hAc, ldimBot_eq_of_hasTree hT hAl, ?_, hsoa⟩
  ext f
  constructor
  · rintro ⟨⟨hfU, hfA⟩, hfr⟩
    have hres : PrivLittlestone.restrictCls H f A = PrivLittlestone.restrictCls H h A := by
      ext g
      simp only [PrivLittlestone.restrictCls, Set.mem_setOf_eq]
      exact and_congr_right fun _ => forall_congr' fun x => forall_congr' fun hx => by rw [hfA x hx]
    have := soa_eq hX H d r hfr A (by omega) (by rw [hres]; exact hAl)
    rw [hres, hsoa] at this
    exact this.symm
  · intro hf
    rw [Set.mem_singleton_iff] at hf
    subst hf
    exact ⟨⟨hh, fun _ _ => rfl⟩, hhr⟩

end MoranYanPAC.Main
end

theorem solution : type_of% @MoranYanPAC.Main.chk_small_witnesses_with_soa := @MoranYanPAC.Main.chk_small_witnesses_with_soa
