-- Prove2me | solution 1 for MoranYanPAC.Main.global_local_candidate_counts
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:23:31.149176+00:00
-- url     : https://prove2.me/submissions/deb72c1e-343d-4a38-9ca3-a62bf4850881

import Mathlib
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_PrivLittlestone_localUniverse
import Definitions.Def_PrivLittlestone_rankLayer
import Definitions.Def_PrivLittlestone_restrictCls
import Definitions.Def_PrivLittlestone_rankOf
import Definitions.Def_PrivLittlestone_witnessSpace
import Definitions.Def_PrivLittlestone_IsWitnessAssignment
import Definitions.Def_PrivLittlestone_versionCell
import Definitions.Def_PrivLittlestone_selDesc
import Definitions.Def_PrivLittlestone_selD
import Definitions.Def_PrivLittlestone_selT
import Definitions.Def_MoranYanPAC_Main_GoodFamily
import Definitions.Def_MoranYanPAC_Main_Candidates
import Theorems.Thm_MoranYanPAC_Main_dimension_decreases_with_rank
import Theorems.Thm_MoranYanPAC_Main_majorities_increase_rank
import Theorems.Thm_MoranYanPAC_Main_dimension_inside_witness
import Theorems.Thm_MoranYanPAC_Main_good_subset
import Theorems.Thm_MoranYanPAC_Main_majorities_preserve_avoidance
import Theorems.Thm_PrivLittlestone_eq_21

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

end MoranYanPAC.Dev.Basic
end

section
set_option autoImplicit false

namespace MoranYanPAC.Dev.Dim

open UnderstandingML MoranYanPAC.Dev.Basic PrivLittlestone

variable {X : Type*}

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

end MoranYanPAC.Dev.Dim
end

section
set_option autoImplicit false

namespace PrivLittlestone.Dev.Sel

variable {X : Type*}

theorem selDesc_mono (H : Set (X → Bool)) (d : ℕ) (Aw : (X → Bool) → Finset X)
    (V : Set (X → Bool)) {k k' : ℕ} (hk : k ≤ k') : selDesc H d Aw V k ⊆ selDesc H d Aw V k' := by
  induction k' with
  | zero => have : k = 0 := by omega
            subst this; exact subset_rfl
  | succ k' ih =>
    rcases Nat.lt_or_ge k (k' + 1) with h | h
    · refine (ih (by omega)).trans ?_
      intro g hg
      simp only [selDesc]
      split_ifs
      · exact Or.inl hg
      · exact hg
    · have : k = k' + 1 := by omega
      subst this; exact subset_rfl

theorem selDesc_prop (H : Set (X → Bool)) (d : ℕ) (Aw : (X → Bool) → Finset X)
    (V : Set (X → Bool)) (k : ℕ) :
    ∀ g ∈ selDesc H d Aw V k, g ∈ V ∧ d - k ≤ rankOf H d g := by
  induction k with
  | zero => intro g hg; exact ⟨hg.1, by simp [hg.2]⟩
  | succ k ih =>
    intro g hg
    simp only [selDesc] at hg
    split_ifs at hg with hk
    · rcases hg with hg | hg
      · have := ih g hg; exact ⟨this.1, by omega⟩
      · exact ⟨hg.1, by rw [hg.2.1]⟩
    · have := ih g hg; exact ⟨this.1, by omega⟩

end PrivLittlestone.Dev.Sel

namespace PrivLittlestone

open PrivLittlestone.Dev.Sel

end PrivLittlestone
end

section
set_option autoImplicit false

namespace MoranYanPAC.Dev.L11a

open UnderstandingML MoranYanPAC.Dev.Basic MoranYanPAC.Dev.Dim PrivLittlestone MoranYanPAC.Main

variable {X : Type*}

theorem ldimBot_mono {C D : Set (X → Bool)} (h : C ⊆ D) : ldimBot C ≤ ldimBot D := by
  unfold ldimBot
  by_cases hC : C.Nonempty
  · have hD : D.Nonempty := hC.mono h
    rw [if_pos hC, if_pos hD]
    refine WithBot.coe_le_coe.2 ?_
    refine iSup₂_le fun d hd => ?_
    exact le_iSup₂ (f := fun (d : ℕ) (_ : ∃ v : List Bool → X, ShattersTree D d v) => (d : ℕ∞)) d
      (HasTree.mono h hd)
  · rw [if_neg hC]; exact bot_le

theorem selDesc_stage (H : Set (X → Bool)) (d : ℕ) (Aw : (X → Bool) → Finset X)
    (V : Set (X → Bool)) (k : ℕ) :
    ∀ g ∈ selDesc H d Aw V k, d - rankOf H d g ≤ k ∧ g ∈ selDesc H d Aw V (d - rankOf H d g) := by
  induction k with
  | zero =>
    intro g hg
    have : rankOf H d g = d := hg.2
    simp only [this, Nat.sub_self]
    exact ⟨le_rfl, hg⟩
  | succ k ih =>
    intro g hg
    have hg' := hg
    simp only [selDesc] at hg'
    split_ifs at hg' with hk
    · rcases hg' with hg' | hg'
      · obtain ⟨h1, h2⟩ := ih g hg'
        exact ⟨by omega, h2⟩
      · have : d - rankOf H d g = k + 1 := by rw [hg'.2.1]; omega
        rw [this]; exact ⟨le_rfl, hg⟩
    · obtain ⟨h1, h2⟩ := ih g hg'
      exact ⟨by omega, h2⟩

theorem selD_sub_union (H : Set (X → Bool)) (d : ℕ) (Aw : (X → Bool) → Finset X)
    (V : Set (X → Bool)) :
    selD H d Aw V ⊆ ⋃ s ∈ Finset.range (d + 1), selT H d Aw V s := by
  have : ∀ k, selDesc H d Aw V k ⊆ ⋃ s ∈ Finset.range (d + 1), selT H d Aw V s := by
    intro k
    induction k with
    | zero =>
      intro g hg
      simp only [Set.mem_iUnion]
      exact ⟨d, by simp, hg.1, hg.2, fun _ hlt => absurd hlt (lt_irrefl _)⟩
    | succ k ih =>
      intro g hg
      have hg' := hg
      simp only [selDesc] at hg'
      split_ifs at hg' with hk
      · rcases hg' with hg' | hg'
        · exact ih hg'
        · simp only [Set.mem_iUnion]
          refine ⟨d - (k + 1), by simp only [Finset.mem_range]; omega, hg'.1, hg'.2.1, fun _ _ hmem => ?_⟩
          have : d - (d - (k + 1)) - 1 = k := by omega
          rw [this] at hmem
          exact hg'.2.2 _ hmem
      · exact ih hg'
  exact this d


theorem mem_layer_of_rank (H : Set (X → Bool)) (d : ℕ) {g : X → Bool}
    (hg : g ∈ localUniverse H d) : g ∈ rankLayer H d (rankOf H d g) := by
  classical
  exact Nat.findGreatest_spec (P := fun s => g ∈ rankLayer H d s) (Nat.zero_le d) hg

theorem rank_ge (H : Set (X → Bool)) (d : ℕ) {g : X → Bool} {t : ℕ} (ht : t ≤ d)
    (hg : g ∈ rankLayer H d t) : t ≤ rankOf H d g := by
  classical
  exact Nat.le_findGreatest (P := fun s => g ∈ rankLayer H d s) ht hg

theorem two_tree {C : Set (X → Bool)} {g1 g2 : X → Bool} (h1 : g1 ∈ C) (h2 : g2 ∈ C) (hne : g1 ≠ g2) :
    HasTree C 1 := by
  obtain ⟨x, hx⟩ : ∃ x, g1 x ≠ g2 x := by
    by_contra hc; push Not at hc; exact hne (funext hc)
  refine ⟨fun _ => x, fun y => ?_⟩
  by_cases hy : g1 x = y 0
  · exact ⟨g1, h1, fun t => by
      have : t = 0 := Subsingleton.elim _ _
      subst this; simpa using hy⟩
  · refine ⟨g2, h2, fun t => ?_⟩
    have : t = 0 := Subsingleton.elim _ _
    subst this
    simp only [List.ofFn_zero]
    cases h : g1 x <;> cases h' : g2 x <;> cases h'' : y 0 <;> simp_all

theorem majority_const {G : Finset (X → Bool)} (hG : G.Nonempty) (x : X) (b : Bool)
    (h : ∀ g ∈ G, g x = b) : majority G x = b := by
  classical
  have hpos : 0 < G.card := Finset.card_pos.2 hG
  unfold majority
  cases b
  · have h1 : (G.filter (fun g => g x = true)).card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.filter_false_of_mem
      intro g hg; simp [h g hg]
    have h2 : (G.filter (fun g => g x = false)).card = G.card := by
      rw [Finset.filter_true_of_mem]; intro g hg; exact h g hg
    simp [h1, h2]
  · have h1 : (G.filter (fun g => g x = false)).card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.filter_false_of_mem
      intro g hg; simp [h g hg]
    have h2 : (G.filter (fun g => g x = true)).card = G.card := by
      rw [Finset.filter_true_of_mem]; intro g hg; exact h g hg
    simp [h1, h2, hpos]


theorem no_good (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d)
    (Aw : (X → Bool) → Finset X) (hAw : SourceWitnesses H d Aw)
    (S : List (X × Bool)) (v : Fin S.length → Bool) (s : ℕ) (hs : s ≤ d)
    (G : Finset (X → Bool)) (hG : (G : Set (X → Bool)) ⊆ selT H d Aw (versionCell H d S v) s)
    (hgood : Good d G) : G.card ≤ 1 := by
  classical
  by_contra hc
  push Not at hc
  have hVU : ∀ g ∈ G, g ∈ versionCell H d S v := fun g hg => (hG hg).1
  have hrank : ∀ g ∈ G, rankOf H d g = s := fun g hg => (hG hg).2.1
  have hFs : ∀ g ∈ G, g ∈ rankLayer H d s := fun g hg => by
    have := mem_layer_of_rank H d (hVU g hg).1
    rwa [hrank g hg] at this
  rcases Nat.lt_or_ge s d with hlt | hge
  · -- s < d
    have hb := Main.majorities_increase_rank H d hH hd hd1 s hlt G (by omega) hFs hgood
    set b := majority G with hbdef
    have hbV : b ∈ versionCell H d S v := by
      refine ⟨(layer_mono H d (Nat.zero_le _) hb), fun i => ?_⟩
      exact majority_const hgood.1 _ _ (fun g hg => (hVU g hg).2 i)
    have hbrank : s + 1 ≤ rankOf H d b := rank_ge H d (by omega) hb
    obtain ⟨g', hg'sel, hbW, hrk, _⟩ := PrivLittlestone.eq_21 H d hH hd hd1 Aw hAw.1 S v ⟨b, hbV⟩ b hbV
    have hst := selDesc_stage H d Aw _ d g' hg'sel
    have hg'mem : g' ∈ selDesc H d Aw (versionCell H d S v) (d - s - 1) :=
      PrivLittlestone.Dev.Sel.selDesc_mono H d Aw _ (by omega) hst.2
    have hg'U : g' ∈ localUniverse H d :=
      (PrivLittlestone.Dev.Sel.selDesc_prop H d Aw _ _ g' hg'mem).1.1
    have hnW := Main.majorities_preserve_avoidance H d hH hd hd1 Aw hAw G hgood
      (fun g hg => (hVU g hg).1) g' hg'U (fun g hg hW => by
        have := (hG hg).2.2 g' hlt hg'mem
        exact this hW)
    exact hnW hbW
  · -- s = d
    have hsd : s = d := le_antisymm hs hge
    obtain ⟨g1, hg1, g2, hg2, hne⟩ := Finset.one_lt_card.1 hc
    have hT : HasTree (rankLayer H d s) 1 := two_tree (hFs g1 hg1) (hFs g2 hg2) hne
    have h1 := (le_ldim_iff (le_refl 1)).2 hT
    have h2 := (Main.dimension_decreases_with_rank H d hH hd hd1).1 s hs
    have hne' : (rankLayer H d s).Nonempty := ⟨g1, hFs g1 hg1⟩
    unfold ldimBot at h2
    rw [if_pos hne'] at h2
    have h3 : ldim (rankLayer H d s) ≤ ((d - s : ℕ) : ℕ∞) := by
      have : ((ldim (rankLayer H d s) : ℕ∞) : WithBot ℕ∞) ≤ (((d - s : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        rw [WithBot.coe_natCast]; exact h2
      exact WithBot.coe_le_coe.1 this
    have h4 := h1.trans h3
    rw [hsd] at h4
    simp at h4


theorem card_bound (d : ℕ) (hd1 : 1 ≤ d) (T : Set (X → Bool)) (t : ℕ)
    (hldim : ldimBot T ≤ (t : WithBot ℕ∞))
    (hnog : ∀ G : Finset (X → Bool), (G : Set (X → Bool)) ⊆ T → Good d G → G.card ≤ 1) :
    T.encard ≤ (((2 * (d + 1)) ^ t : ℕ) : ℕ∞) := by
  classical
  by_contra hlt
  push Not at hlt
  have hle : (((2 * (d + 1)) ^ t + 1 : ℕ) : ℕ∞) ≤ T.encard := by
    have := Order.add_one_le_of_lt hlt
    simpa using this
  obtain ⟨T0, hT0, hcard⟩ := Set.exists_subset_encard_eq hle
  have hfin : T0.Finite := Set.finite_of_encard_eq_coe hcard
  set G0 := hfin.toFinset with hG0
  have hG0card : G0.card = (2 * (d + 1)) ^ t + 1 := by
    have := hfin.encard_eq_coe_toFinset_card
    rw [hcard] at this
    exact_mod_cast this.symm
  have hG0ne : G0.Nonempty := Finset.card_pos.1 (by omega)
  have hsub : (G0 : Set (X → Bool)) ⊆ T := by
    intro g hg; exact hT0 (hfin.mem_toFinset.1 hg)
  have hl : ldimBot (G0 : Set (X → Bool)) ≤ (t : WithBot ℕ∞) := (ldimBot_mono hsub).trans hldim
  obtain ⟨G', hG'sub, hG'good, hG'card⟩ := Main.good_subset d hd1 G0 hG0ne t hl
  have h1 := hnog G' (fun g hg => hsub (hG'sub hg)) hG'good
  have hpos : (0 : ℝ) < (2 * ((d : ℝ) + 1)) ^ t := by positivity
  rw [div_le_iff₀ hpos] at hG'card
  have : (G0.card : ℝ) ≤ (2 * ((d : ℝ) + 1)) ^ t * 1 := by
    refine hG'card.trans ?_
    have : (G'.card : ℝ) ≤ 1 := by exact_mod_cast h1
    nlinarith
  rw [hG0card] at this
  push_cast at this
  linarith

theorem layer_of_selT (H : Set (X → Bool)) (d : ℕ) (Aw : (X → Bool) → Finset X)
    (V : Set (X → Bool)) (s : ℕ) : selT H d Aw V s ∩ {g | g ∈ localUniverse H d} ⊆ rankLayer H d s := by
  intro g hg
  have := mem_layer_of_rank H d hg.2
  rwa [hg.1.2.1] at this

theorem global_bound (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d)
    (Aw : (X → Bool) → Finset X) (hAw : SourceWitnesses H d Aw)
    (S : List (X × Bool)) (v : Fin S.length → Bool) (s : ℕ) (hs : s ≤ d) :
    (selT H d Aw (versionCell H d S v) s).encard ≤ (((2 * (d + 1)) ^ (d - s) : ℕ) : ℕ∞) := by
  refine card_bound d hd1 _ _ ?_ (fun G hG hgood => no_good H d hH hd hd1 Aw hAw S v s hs G hG hgood)
  refine (ldimBot_mono (D := rankLayer H d s) ?_).trans
    ((Main.dimension_decreases_with_rank H d hH hd hd1).1 s hs)
  intro g hg
  exact layer_of_selT H d Aw _ s ⟨hg, hg.1.1⟩

theorem local_bound (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d)
    (Aw : (X → Bool) → Finset X) (hAw : SourceWitnesses H d Aw)
    (S : List (X × Bool)) (v : Fin S.length → Bool) (h : X → Bool) (hh : h ∈ localUniverse H d)
    (s : ℕ) (hs : s ≤ rankOf H d h) :
    (selT H d Aw (versionCell H d S v) s ∩ witnessSpace H d Aw h).encard ≤
      (((2 * (d + 1)) ^ (rankOf H d h - s) : ℕ) : ℕ∞) := by
  have hrd : rankOf H d h ≤ d := by classical exact Nat.findGreatest_le _
  refine card_bound d hd1 _ _ ?_ (fun G hG hgood =>
    no_good H d hH hd hd1 Aw hAw S v s (by omega) G (fun g hg => (hG hg).1) hgood)
  refine (ldimBot_mono (D := witnessSpace H d Aw h ∩ rankLayer H d s) ?_).trans
    ((Main.dimension_inside_witness H d hH hd hd1 Aw hAw h hh).1 s hs)
  intro g hg
  exact ⟨hg.2, layer_of_selT H d Aw _ s ⟨hg.1, hg.1.1.1⟩⟩

end MoranYanPAC.Dev.L11a
end

section
set_option autoImplicit false

namespace MoranYanPAC.Dev.Sauer

theorem sum_choose_le (n d : ℕ) (hd : 1 ≤ d) (hdn : d ≤ n) :
    (∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ)) ≤ (Real.exp 1 * n / d) ^ d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hd hdn)
  have hr : (1 : ℝ) ≤ n / d := by rw [le_div_iff₀ hdpos]; simp only [one_mul]; exact_mod_cast hdn
  have step1 : (∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ)) ≤
      ∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ) * (n / d) ^ (d - k) := by
    refine Finset.sum_le_sum fun k _ => ?_
    have : (1 : ℝ) ≤ (n / d) ^ (d - k) := one_le_pow₀ hr
    nlinarith [(Nat.cast_nonneg (n.choose k) : (0 : ℝ) ≤ n.choose k)]
  have step2 : ∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ) * (n / d) ^ (d - k) =
      (n / d : ℝ) ^ d * ∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ) * (d / n : ℝ) ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have : (n / d : ℝ) ^ d = (n / d) ^ (d - k) * (n / d) ^ k := by rw [← pow_add]; congr 1; omega
    rw [this]
    have h2 : (n / d : ℝ) ^ k * (d / n : ℝ) ^ k = 1 := by
      rw [← mul_pow]; rw [div_mul_div_comm, mul_comm (n : ℝ) d, div_self (by positivity)]; simp
    calc (n.choose k : ℝ) * (n / d) ^ (d - k) = (n.choose k : ℝ) * (n / d) ^ (d - k) * ((n / d : ℝ) ^ k * (d / n : ℝ) ^ k) := by rw [h2]; ring
      _ = _ := by ring
  have step3 : ∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ) * (d / n : ℝ) ^ k ≤
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (d / n : ℝ) ^ k := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega)) ?_
    intro k _ _; positivity
  have step4 : ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (d / n : ℝ) ^ k = (1 + d / n : ℝ) ^ n := by
    rw [show (1 + (d : ℝ) / n) = d / n + 1 by ring, add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [one_pow]
    ring
  have step5 : (1 + d / n : ℝ) ^ n ≤ Real.exp 1 ^ d := by
    have h1 : (1 + d / n : ℝ) ≤ Real.exp (d / n) := by linarith [Real.add_one_le_exp (d / n : ℝ)]
    calc (1 + d / n : ℝ) ^ n ≤ Real.exp (d / n) ^ n := pow_le_pow_left₀ (by positivity) h1 n
      _ = Real.exp ((d / n) * n) := by rw [← Real.exp_nat_mul]; ring_nf
      _ = Real.exp d := by rw [div_mul_cancel₀ _ hnpos.ne']
      _ = Real.exp 1 ^ d := by rw [← Real.exp_nat_mul]; ring_nf
  calc (∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ)) ≤ _ := step1
    _ = _ := step2
    _ ≤ (n / d : ℝ) ^ d * (1 + d / n : ℝ) ^ n := by
        rw [← step4]; exact mul_le_mul_of_nonneg_left step3 (by positivity)
    _ ≤ (n / d : ℝ) ^ d * Real.exp 1 ^ d := mul_le_mul_of_nonneg_left step5 (by positivity)
    _ = (Real.exp 1 * n / d) ^ d := by rw [← mul_pow]; congr 1; ring

end MoranYanPAC.Dev.Sauer
end

section
set_option autoImplicit false

namespace MoranYanPAC.Dev.L11b

open UnderstandingML MoranYanPAC.Dev.Basic MoranYanPAC.Dev.Dim PrivLittlestone MoranYanPAC.Main

variable {X : Type*}

open Classical in
noncomputable def cells (H : Set (X → Bool)) (d : ℕ) (S : List (X × Bool)) :
    Finset (Fin S.length → Bool) :=
  Finset.univ.filter (fun v => (versionCell H d S v).Nonempty)

open Classical in
noncomputable def cellFamily (H : Set (X → Bool)) (d : ℕ) (S : List (X × Bool)) :
    Finset (Finset (Fin S.length)) :=
  (cells H d S).image (fun v => Finset.univ.filter (fun i => v i = true))

theorem mem_cells (H : Set (X → Bool)) (d : ℕ) (S : List (X × Bool)) (v : Fin S.length → Bool) :
    v ∈ cells H d S ↔ (versionCell H d S v).Nonempty := by
  classical
  simp [cells]

theorem shatters_card_le (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d) (S : List (X × Bool))
    (T : Finset (Fin S.length)) (hT : (cellFamily H d S).Shatters T) :
    T.card ≤ d := by
  classical
  rcases Nat.eq_zero_or_pos T.card with h0 | hpos
  · omega
  obtain ⟨i0, hi0⟩ := Finset.card_pos.1 hpos
  set m := T.card with hm
  let xs : Fin S.length → X := fun i => (S.get i).1
  let pos : Fin m → Fin S.length := fun j => (T.equivFin.symm j).1
  have hpos_mem : ∀ j, pos j ∈ T := fun j => (T.equivFin.symm j).2
  have hpos_inj : Function.Injective pos := by
    intro a b hab
    exact T.equivFin.symm.injective (Subtype.ext hab)
  let x0 : X := xs i0
  let v : List Bool → X := fun l => if h : l.length < m then xs (pos ⟨l.length, h⟩) else x0
  have hU : ∀ y : Fin m → Bool, ∃ f ∈ localUniverse H d, ∀ j : Fin m, f (xs (pos j)) = y j := by
    intro y
    set t : Finset (Fin S.length) := (Finset.univ.filter (fun j => y j = true)).image pos with ht
    have htT : t ⊆ T := by
      intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hi
      exact hpos_mem j
    obtain ⟨u, hu, hTu⟩ := hT htT
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨f, hf⟩ := (mem_cells H d S v').1 hv'
    refine ⟨f, hf.1, fun j => ?_⟩
    have h1 : f (xs (pos j)) = v' (pos j) := hf.2 (pos j)
    rw [h1]
    have h2 : pos j ∈ T ∩ Finset.univ.filter (fun i => v' i = true) ↔ pos j ∈ t := by rw [hTu]
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, ht, Finset.mem_image] at h2
    have h3 : v' (pos j) = true ↔ y j = true := by
      constructor
      · intro hv
        obtain ⟨j', hj', hjj⟩ := h2.1 ⟨hpos_mem j, hv⟩
        rw [← hpos_inj hjj]; exact hj'
      · intro hy
        exact (h2.2 ⟨j, hy, rfl⟩).2
    cases hy : y j <;> cases hv : v' (pos j) <;> simp_all
  have hTree : HasTree (localUniverse H d) m := by
    refine ⟨v, fun y => ?_⟩
    obtain ⟨f, hf, hfy⟩ := hU y
    refine ⟨f, hf, fun t => ?_⟩
    have : v (List.ofFn (fun j : Fin (t : ℕ) => y ⟨j, lt_trans j.2 t.2⟩)) = xs (pos t) := by
      simp only [v, List.length_ofFn, dif_pos t.2]
    rw [this, hfy]
  have hldim := (Main.dimension_decreases_with_rank H d hH hd hd1).2
  have hUne : (localUniverse H d).Nonempty := by
    obtain ⟨h, hh⟩ := hH
    exact ⟨h, fun A _ => ⟨h, hh, fun _ _ => rfl⟩⟩
  unfold ldimBot at hldim
  rw [if_pos hUne] at hldim
  have hl : ldim (localUniverse H d) = d := by
    have : ((ldim (localUniverse H d) : ℕ∞) : WithBot ℕ∞) = ((d : ℕ∞) : WithBot ℕ∞) := by
      rw [WithBot.coe_natCast]; exact hldim
    exact WithBot.coe_injective this
  have := (le_ldim_iff hpos).2 hTree
  rw [hl] at this
  exact_mod_cast this


theorem cells_card_le (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d) (S : List (X × Bool)) :
    (cells H d S).card ≤ ∑ k ∈ Finset.range (d + 1), S.length.choose k := by
  classical
  have hinj : Function.Injective
      (fun v : Fin S.length → Bool => Finset.univ.filter (fun i => v i = true)) := by
    intro v w hvw
    funext i
    have := congrArg (fun F => i ∈ F) hvw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
    cases hv : v i <;> cases hw : w i <;> simp_all
  have h1 : (cellFamily H d S).card = (cells H d S).card := Finset.card_image_of_injective _ hinj
  have h2 := Finset.card_le_card_shatterer (cellFamily H d S)
  have h3 := Finset.card_shatterer_le_sum_vcDim (𝒜 := cellFamily H d S)
  have h4 : (cellFamily H d S).vcDim ≤ d := by
    unfold Finset.vcDim
    refine Finset.sup_le fun T hT => ?_
    exact shatters_card_le H d hH hd hd1 S T (Finset.mem_shatterer.1 hT)
  rw [Fintype.card_fin] at h3
  have h5 : ∑ k ∈ Finset.Iic (cellFamily H d S).vcDim, S.length.choose k ≤
      ∑ k ∈ Finset.range (d + 1), S.length.choose k := by
    refine Finset.sum_le_sum_of_subset ?_
    intro k hk
    simp only [Finset.mem_Iic, Finset.mem_range] at hk ⊢
    omega
  omega

theorem geom_le (q : ℕ) (hq : 2 ≤ q) (d : ℕ) :
    ∑ s ∈ Finset.range (d + 1), q ^ (d - s) ≤ 2 * q ^ d := by
  have : ∑ s ∈ Finset.range (d + 1), q ^ (d - s) = ∑ j ∈ Finset.range (d + 1), q ^ j := by
    have := Finset.sum_range_reflect (fun j => q ^ j) (d + 1)
    simpa using this
  rw [this]
  clear this
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ]
    have h1 : 2 * q ^ d ≤ q * q ^ d := Nat.mul_le_mul_right _ hq
    calc ∑ j ∈ Finset.range (d + 1), q ^ j + q ^ (d + 1) ≤ 2 * q ^ d + q ^ (d + 1) := by omega
      _ ≤ 2 * q ^ (d + 1) := by rw [pow_succ]; nlinarith

end MoranYanPAC.Dev.L11b
end

section
set_option autoImplicit false

namespace MoranYanPAC.Dev.L11c

open UnderstandingML MoranYanPAC.Dev.Basic MoranYanPAC.Dev.Dim PrivLittlestone MoranYanPAC.Main
  MoranYanPAC.Dev.L11a MoranYanPAC.Dev.L11b

variable {X : Type*}

theorem selD_finset (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d)
    (Aw : (X → Bool) → Finset X) (hAw : SourceWitnesses H d Aw)
    (S : List (X × Bool)) (v : Fin S.length → Bool) :
    ∃ F : Finset (X → Bool), selD H d Aw (versionCell H d S v) ⊆ ↑F ∧
      F.card ≤ 2 * (2 * (d + 1)) ^ d := by
  classical
  have hfin : ∀ s, s ≤ d → (selT H d Aw (versionCell H d S v) s).Finite := fun s hs =>
    Set.finite_of_encard_le_coe (global_bound H d hH hd hd1 Aw hAw S v s hs)
  let G : ℕ → Finset (X → Bool) := fun s =>
    if h : s ≤ d then (hfin s h).toFinset else ∅
  refine ⟨(Finset.range (d + 1)).biUnion G, ?_, ?_⟩
  · intro g hg
    have := selD_sub_union H d Aw _ hg
    simp only [Set.mem_iUnion] at this
    obtain ⟨s, hs, hgs⟩ := this
    simp only [Finset.coe_biUnion, Finset.coe_range, Set.mem_iUnion]
    have hsd : s ≤ d := by simp only [Finset.mem_range] at hs; omega
    refine ⟨s, by simpa using hs, ?_⟩
    simp only [G, dif_pos hsd]
    exact (hfin s hsd).mem_toFinset.2 hgs
  · refine (Finset.card_biUnion_le).trans ?_
    refine le_trans (Finset.sum_le_sum (g := fun s => (2 * (d + 1)) ^ (d - s)) fun s hs => ?_)
      (geom_le _ (by omega) d)
    have hsd : s ≤ d := by simp only [Finset.mem_range] at hs; omega
    simp only [G, dif_pos hsd]
    have h1 := (hfin s hsd).encard_eq_coe_toFinset_card
    have h2 := global_bound H d hH hd hd1 Aw hAw S v s hsd
    rw [h1] at h2
    exact_mod_cast h2

end MoranYanPAC.Dev.L11c

namespace MoranYanPAC.Main

open UnderstandingML MoranYanPAC.Dev.L11a MoranYanPAC.Dev.L11b MoranYanPAC.Dev.L11c MoranYanPAC.Dev

theorem chk_global_local_candidate_counts {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d)
    (Aw : (X → Bool) → Finset X) (hAw : SourceWitnesses H d Aw) (S : List (X × Bool)) :
    (∀ v : Fin S.length → Bool, (PrivLittlestone.versionCell H d S v).Nonempty →
      (∀ s : ℕ, s ≤ d →
        (PrivLittlestone.selT H d Aw (PrivLittlestone.versionCell H d S v) s).encard ≤
          (((2 * (d + 1)) ^ (d - s) : ℕ) : ℕ∞)) ∧
      (∀ h ∈ PrivLittlestone.localUniverse H d, ∀ s : ℕ,
        s ≤ PrivLittlestone.rankOf H d h →
        (PrivLittlestone.selT H d Aw (PrivLittlestone.versionCell H d S v) s ∩
          PrivLittlestone.witnessSpace H d Aw h).encard ≤
            (((2 * (d + 1)) ^ (PrivLittlestone.rankOf H d h - s) : ℕ) : ℕ∞))) ∧
    (candidates H d Aw S).Finite ∧
    (d ≤ S.length → ((candidates H d Aw S).ncard : ℝ) ≤
      2 * (2 * ((d : ℝ) + 1)) ^ d * (Real.exp 1 * S.length / d) ^ d) := by
  classical
  have hF := fun v => selD_finset H d hH hd hd1 Aw hAw S v
  choose F hF1 hF2 using hF
  have hcand : candidates H d Aw S ⊆ ↑((cells H d S).biUnion F) := by
    intro g hg
    simp only [candidates, Set.mem_iUnion] at hg
    obtain ⟨v, hv⟩ := hg
    simp only [Finset.coe_biUnion, Set.mem_iUnion]
    refine ⟨v, ?_, hF1 v hv⟩
    rw [Finset.mem_coe, mem_cells]
    obtain ⟨hgV, _⟩ := PrivLittlestone.Dev.Sel.selDesc_prop H d Aw _ d g hv
    exact ⟨g, hgV⟩
  refine ⟨fun v _ => ⟨fun s hs => global_bound H d hH hd hd1 Aw hAw S v s hs,
    fun h hh s hs => local_bound H d hH hd hd1 Aw hAw S v h hh s hs⟩,
    (Finset.finite_toSet _).subset hcand, fun hdn => ?_⟩
  have h1 : (candidates H d Aw S).ncard ≤ ((cells H d S).biUnion F).card := by
    calc (candidates H d Aw S).ncard ≤ (↑((cells H d S).biUnion F) : Set (X → Bool)).ncard :=
          Set.ncard_le_ncard hcand (Finset.finite_toSet _)
      _ = _ := Set.ncard_coe_finset _
  have h2 : ((cells H d S).biUnion F).card ≤ (cells H d S).card * (2 * (2 * (d + 1)) ^ d) :=
    (Finset.card_biUnion_le).trans (Finset.sum_le_card_nsmul _ _ _ (fun v _ => hF2 v))
  have h3 := cells_card_le H d hH hd hd1 S
  have h4 : ((∑ k ∈ Finset.range (d + 1), (S.length.choose k : ℝ))) ≤
      (Real.exp 1 * S.length / d) ^ d := Sauer.sum_choose_le S.length d hd1 hdn
  have h5 : ((cells H d S).card : ℝ) ≤ (Real.exp 1 * S.length / d) ^ d := by
    refine le_trans ?_ h4
    exact_mod_cast h3
  have h6 : ((candidates H d Aw S).ncard : ℝ) ≤
      ((cells H d S).card : ℝ) * (2 * (2 * ((d : ℝ) + 1)) ^ d) := by
    have := h1.trans h2
    exact_mod_cast this
  calc ((candidates H d Aw S).ncard : ℝ) ≤ _ := h6
    _ ≤ (Real.exp 1 * S.length / d) ^ d * (2 * (2 * ((d : ℝ) + 1)) ^ d) :=
        mul_le_mul_of_nonneg_right h5 (by positivity)
    _ = _ := by ring

end MoranYanPAC.Main
end

theorem solution : type_of% @MoranYanPAC.Main.chk_global_local_candidate_counts := @MoranYanPAC.Main.chk_global_local_candidate_counts
