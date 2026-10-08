-- Prove2me | solution 1 for KKBinPacking.GeometricGrouping.algorithm2_log_squared_bound
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-05T22:55:28.748919+00:00
-- url     : https://prove2.me/submissions/5945a079-aa9c-4c4d-a88a-ed34a673a9f3

import Mathlib
import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
import Definitions.Def_KKBinPacking_Shared_AnyFit
import Definitions.Def_KKBinPacking_GeometricGrouping_GeomGroup
import Definitions.Def_KKBinPacking_GeometricGrouping_Algorithm2

set_option autoImplicit false

/- Complete checked body: GreedyBasics -/
section

set_option autoImplicit false
open KKBinPacking.GeometricGrouping

namespace KKBinPacking.GeometricProof

/-- The exact greedy prefix and its unused suffix partition the list. -/
theorem takeUntil_partition (k : ℝ) (L : List ℝ) :
    takeUntil k L ++ L.drop (takeUntil k L).length = L := by
  classical
  induction L generalizing k with
  | nil => simp [takeUntil]
  | cons x L ih =>
    by_cases h : k ≤ x
    · simp [takeUntil, h]
    · simp only [takeUntil, if_neg h, List.length_cons, List.drop_succ_cons, List.cons_append]
      rw [ih]

theorem takeUntil_isPrefix (k : ℝ) (L : List ℝ) : takeUntil k L <+: L :=
  ⟨_, takeUntil_partition k L⟩

theorem takeUntil_sublist (k : ℝ) (L : List ℝ) : List.Sublist (takeUntil k L) L :=
  (takeUntil_isPrefix k L).sublist

theorem takeUntil_length_le (k : ℝ) (L : List ℝ) : (takeUntil k L).length ≤ L.length :=
  (takeUntil_sublist k L).length_le

theorem takeUntil_ne_nil (k : ℝ) (L : List ℝ) (hL : L ≠ []) : takeUntil k L ≠ [] := by
  cases L with
  | nil => exact (hL rfl).elim
  | cons x L =>
    have h := takeUntil_cons_length_pos k x L
    intro he
    simp [he] at h

/-- A greedy group is full whenever some items remain after it. -/
theorem takeUntil_full_of_remainder (k : ℝ) (L : List ℝ)
    (hrest : L.drop (takeUntil k L).length ≠ []) : k ≤ (takeUntil k L).sum := by
  classical
  induction L generalizing k with
  | nil => simp at hrest
  | cons x L ih =>
    by_cases h : k ≤ x
    · simp [takeUntil, h]
    · have hr : L.drop (takeUntil (k-x) L).length ≠ [] := by
        simpa only [takeUntil, if_neg h, List.length_cons, List.drop_succ_cons] using hrest
      have hh := ih (k-x) hr
      simp only [takeUntil, if_neg h, List.sum_cons]
      linarith

theorem takeUntil_drop_length_lt (k x : ℝ) (L : List ℝ) :
    ((x::L).drop (takeUntil k (x::L)).length).length < (x::L).length := by
  have h := takeUntil_cons_length_pos k x L
  simp only [List.length_drop, List.length_cons]
  omega

theorem geomGroupsList_flatten (k : ℝ) (L : List ℝ) :
    (geomGroupsList k L).flatten = L := by
  generalize hm : L.length = m
  induction m using Nat.strong_induction_on generalizing L with
  | h m ih =>
    cases L with
    | nil => simp [geomGroupsList]
    | cons x L =>
      have hr : ((x::L).drop (takeUntil k (x::L)).length).length < m := by
        rw [← hm]
        exact takeUntil_drop_length_lt k x L
      rw [geomGroupsList, List.flatten_cons, ih _ hr _ rfl]
      exact takeUntil_partition k (x::L)

theorem geomGroupsList_ne_nil (k : ℝ) (L : List ℝ) (hL : L ≠ []) :
    geomGroupsList k L ≠ [] := by
  cases L with
  | nil => exact (hL rfl).elim
  | cons x L => simp [geomGroupsList]

theorem geomGroupsList_groups_nonempty (k : ℝ) (L : List ℝ) :
    ∀ G ∈ geomGroupsList k L, G ≠ [] := by
  generalize hm : L.length = m
  induction m using Nat.strong_induction_on generalizing L with
  | h m ih =>
    cases L with
    | nil => simp [geomGroupsList]
    | cons x L =>
      have hr : ((x::L).drop (takeUntil k (x::L)).length).length < m := by
        rw [← hm]
        exact takeUntil_drop_length_lt k x L
      rw [geomGroupsList]
      intro G hG
      rcases List.mem_cons.mp hG with rfl | hG
      · exact takeUntil_ne_nil k _ (by simp)
      · exact ih _ hr _ rfl G hG

end KKBinPacking.GeometricProof

end

/- Complete checked body: GreedyMass -/
section

set_option autoImplicit false
open KKBinPacking.GeometricGrouping

namespace KKBinPacking.GeometricProof

/-- All but the last greedy group account for at least their number times the threshold. -/
theorem geomGroupsList_count_size (k : ℝ) (L : List ℝ)
    (hL : ∀ x ∈ L, 0 ≤ x) :
    (((geomGroupsList k L).length-1 : ℕ) : ℝ)*k ≤ L.sum := by
  generalize hm : L.length = m
  induction m using Nat.strong_induction_on generalizing L with
  | h m ih =>
    cases L with
    | nil => simp [geomGroupsList]
    | cons x L =>
      let G := takeUntil k (x::L)
      let R := (x::L).drop G.length
      have hr : R.length < m := by
        rw [← hm]
        exact takeUntil_drop_length_lt k x L
      have hR : ∀ y ∈ R, 0 ≤ y := fun y hy => hL y (List.mem_of_mem_drop hy)
      rw [geomGroupsList]
      change (((geomGroupsList k R).length+1-1 : ℕ) : ℝ)*k ≤ (x::L).sum
      rw [Nat.add_sub_cancel]
      by_cases hR0 : R = []
      · rw [hR0, geomGroupsList]
        simpa using List.sum_nonneg hL
      · have hi := ih R.length hr R hR rfl
        have hfull : k ≤ G.sum := takeUntil_full_of_remainder k (x::L) hR0
        have hpos : 0 < (geomGroupsList k R).length :=
          List.length_pos_iff.mpr (geomGroupsList_ne_nil k R hR0)
        have hc : (((geomGroupsList k R).length-1 : ℕ) : ℝ)+1 =
            ((geomGroupsList k R).length : ℝ) := by
          exact_mod_cast (Nat.sub_add_cancel hpos : (geomGroupsList k R).length-1+1 = _)
        have hck : (((geomGroupsList k R).length-1 : ℕ) : ℝ)*k+k =
            ((geomGroupsList k R).length : ℝ)*k := by rw [← hc]; ring
        have hs : (x::L).sum = G.sum+R.sum := by
          have hp := congrArg List.sum (takeUntil_partition k (x::L))
          simpa only [List.sum_append, G, R] using hp.symm
        rw [hs]
        linarith

/-- The greedy groups preserve every relation inherited from the sorted concatenation. -/
theorem geomGroupsList_pairwise (k : ℝ) (L : List ℝ) (hL : L.Pairwise (· ≥ ·)) :
    (∀ G ∈ geomGroupsList k L, G.Pairwise (· ≥ ·)) ∧
      (geomGroupsList k L).Pairwise (fun A B => ∀ a ∈ A, ∀ b ∈ B, b ≤ a) := by
  apply List.pairwise_flatten.mp
  rwa [geomGroupsList_flatten]

end KKBinPacking.GeometricProof

end

/- Complete checked body: GroupBlocks -/
section

set_option autoImplicit false

namespace KKBinPacking.GeometricProof

def blockPairs (A B : List ℝ) : Multiset (ℝ × ℝ) :=
  ((B.take A.length).map (fun p => (p, B.headD 0)) : List (ℝ × ℝ))

def pairsOfGroups (G : List (List ℝ)) : Multiset (ℝ × ℝ) :=
  (List.zipWith blockPairs G G.tail).sum

def discardOfGroups (G : List (List ℝ)) : Multiset ℝ :=
  (G.headD [] : Multiset ℝ) +
    (List.zipWith (fun A B : List ℝ => (B.drop A.length : Multiset ℝ)) G G.tail).sum

theorem blockPairs_fst_partition (A B : List ℝ) :
    (blockPairs A B).map Prod.fst + (B.drop A.length : Multiset ℝ) = (B : Multiset ℝ) := by
  simp only [blockPairs, Multiset.map_coe, List.map_map, Function.comp_def,
    List.map_id', Multiset.coe_add]
  rw [List.take_append_drop]

theorem forall₂_multiset_rel {α β : Type*} {R : α → β → Prop} {A : List α} {B : List β}
    (h : List.Forall₂ R A B) : Multiset.Rel R (A : Multiset α) (B : Multiset β) := by
  induction h with
  | nil => exact Multiset.Rel.zero
  | cons hab _ ih => exact Multiset.Rel.cons hab ih

theorem headD_ge_of_pairwise {B : List ℝ} (hB : B.Pairwise (· ≥ ·)) :
    ∀ b ∈ B, b ≤ B.headD 0 := by
  cases B with
  | nil => simp
  | cons b B =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · exact (List.pairwise_cons.mp hB).1 x hx

theorem blockPairs_order {A B : List ℝ} (hB : B.Pairwise (· ≥ ·)) :
    ∀ p ∈ blockPairs A B, p.1 ≤ p.2 := by
  intro p hp
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp hp)
  exact headD_ge_of_pairwise hB b (List.mem_of_mem_take hb)

theorem blockPairs_source {A B : List ℝ} :
    ∀ p ∈ blockPairs A B, p.1 ∈ B := by
  intro p hp
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp hp)
  exact List.mem_of_mem_take hb

theorem blockPairs_rounded_mem {A B : List ℝ} (hB : B ≠ []) :
    ∀ p ∈ blockPairs A B, p.2 ∈ B := by
  cases B with
  | nil => exact (hB rfl).elim
  | cons b B =>
    intro p hp
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp hp)
    simp

/-- One rounded group is dominated by an equally long prefix of the preceding group. -/
theorem blockPairs_domination (A B : List ℝ)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, b ≤ a) :
    Multiset.Rel (· ≤ ·) ((blockPairs A B).map Prod.snd) (A.take B.length : Multiset ℝ) := by
  cases B with
  | nil => simp [blockPairs]
  | cons b B =>
    rw [blockPairs, Multiset.map_coe]
    apply forall₂_multiset_rel
    apply List.forall₂_of_length_eq_of_get
    · simp [Nat.min_comm]
    · intro i hi hj
      have hleft : (((((b::B).take A.length).map (fun p => (p, (b::B).headD 0))).map Prod.snd).get ⟨i,hi⟩) = b := by
        simp only [List.get_eq_getElem, List.getElem_map, List.headD_cons]
      rw [hleft]
      exact hcross _ (List.mem_of_mem_take (List.get_mem _ _)) b (by simp)

theorem blockPairs_rounded_card (A B : List ℝ) :
    (((blockPairs A B).map Prod.snd).toFinset).card ≤ 1 := by
  classical
  have hs : ((blockPairs A B).map Prod.snd).toFinset ⊆ {B.headD 0} := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_toFinset.mp hx)
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp hp)
    simp
  simpa using Finset.card_le_card hs

end KKBinPacking.GeometricProof

end

/- Complete checked body: GroupAggregates -/
section

set_option autoImplicit false

namespace KKBinPacking.GeometricProof

def tailDiscardOfGroups (G : List (List ℝ)) : Multiset ℝ :=
  (List.zipWith (fun A B : List ℝ => (B.drop A.length : Multiset ℝ)) G G.tail).sum

theorem pairs_cons_cons (A B : List ℝ) (G : List (List ℝ)) :
    pairsOfGroups (A :: B :: G) = blockPairs A B + pairsOfGroups (B :: G) := rfl

theorem tailDiscard_cons_cons (A B : List ℝ) (G : List (List ℝ)) :
    tailDiscardOfGroups (A :: B :: G) =
      (B.drop A.length : Multiset ℝ) + tailDiscardOfGroups (B :: G) := rfl

theorem pairs_tail_partition (G : List (List ℝ)) :
    (pairsOfGroups G).map Prod.fst + tailDiscardOfGroups G =
      (G.tail.flatten : Multiset ℝ) := by
  induction G with
  | nil => simp [pairsOfGroups, tailDiscardOfGroups]
  | cons A G ih =>
    cases G with
    | nil => simp [pairsOfGroups, tailDiscardOfGroups]
    | cons B G =>
      rw [pairs_cons_cons, Multiset.map_add, tailDiscard_cons_cons]
      calc
        _ = ((blockPairs A B).map Prod.fst + (B.drop A.length : Multiset ℝ)) +
            ((pairsOfGroups (B :: G)).map Prod.fst + tailDiscardOfGroups (B :: G)) := by
              ac_rfl
        _ = (B : Multiset ℝ) + (G.flatten : Multiset ℝ) := by
              rw [blockPairs_fst_partition, ih]; rfl
        _ = _ := by simp

theorem pairs_partition (G : List (List ℝ)) :
    (pairsOfGroups G).map Prod.fst + discardOfGroups G = (G.flatten : Multiset ℝ) := by
  cases G with
  | nil => simp [pairsOfGroups, discardOfGroups]
  | cons A G =>
    change (pairsOfGroups (A :: G)).map Prod.fst +
      ((A : Multiset ℝ) + tailDiscardOfGroups (A :: G)) = _
    calc
      _ = (A : Multiset ℝ) +
        ((pairsOfGroups (A :: G)).map Prod.fst + tailDiscardOfGroups (A :: G)) := by ac_rfl
      _ = _ := by rw [pairs_tail_partition]; simp

theorem pairs_rounded_card (G : List (List ℝ)) :
    (((pairsOfGroups G).map Prod.snd).toFinset).card ≤ G.tail.length := by
  classical
  induction G with
  | nil => simp [pairsOfGroups]
  | cons A G ih =>
    cases G with
    | nil => simp [pairsOfGroups]
    | cons B G =>
      rw [pairs_cons_cons, Multiset.map_add, Multiset.toFinset_add]
      have hc := Finset.card_union_le
        (((blockPairs A B).map Prod.snd).toFinset)
        (((pairsOfGroups (B :: G)).map Prod.snd).toFinset)
      have hb := blockPairs_rounded_card A B
      simp only [List.tail_cons, List.length_cons] at ih ⊢
      omega

theorem pairs_domination (G : List (List ℝ))
    (hG : G.Pairwise (fun A B => ∀ a ∈ A, ∀ b ∈ B, b ≤ a)) :
    ∃ J₀ ≤ (G.flatten : Multiset ℝ),
      Multiset.Rel (· ≤ ·) ((pairsOfGroups G).map Prod.snd) J₀ := by
  induction G with
  | nil => exact ⟨0, le_refl _, by simp [pairsOfGroups]⟩
  | cons A G ih =>
    cases G with
    | nil => exact ⟨0, by simp, by simp [pairsOfGroups]⟩
    | cons B G =>
      obtain ⟨J₀, hJ₀, hrel⟩ := ih (List.pairwise_cons.mp hG).2
      refine ⟨(A.take B.length : Multiset ℝ) + J₀, ?_, ?_⟩
      · have ht : (A.take B.length : Multiset ℝ) ≤ (A : Multiset ℝ) :=
          Multiset.coe_le.mpr (List.take_sublist _ _).subperm
        simpa only [List.flatten_cons, ← Multiset.coe_add] using add_le_add ht hJ₀
      · rw [pairs_cons_cons, Multiset.map_add]
        exact (blockPairs_domination A B ((List.pairwise_cons.mp hG).1 B (by simp))).add hrel

theorem pairs_properties (G : List (List ℝ))
    (hne : ∀ A ∈ G, A ≠ []) (hsorted : ∀ A ∈ G, A.Pairwise (· ≥ ·)) :
    ∀ p ∈ pairsOfGroups G, p.1 ∈ G.flatten ∧ p.2 ∈ G.flatten ∧ p.1 ≤ p.2 := by
  induction G with
  | nil => simp [pairsOfGroups]
  | cons A G ih =>
    cases G with
    | nil => simp [pairsOfGroups]
    | cons B G =>
      intro p hp
      rw [pairs_cons_cons, Multiset.mem_add] at hp
      rcases hp with hp | hp
      · have hb : B ∈ A :: B :: G := by simp
        refine ⟨?_, ?_, blockPairs_order (hsorted B hb) p hp⟩
        · exact List.mem_flatten.mpr ⟨B, hb, blockPairs_source p hp⟩
        · exact List.mem_flatten.mpr ⟨B, hb, blockPairs_rounded_mem (hne B hb) p hp⟩
      · obtain ⟨h₁, h₂, h₃⟩ := ih (fun B hB => hne B (by simp [hB]))
          (fun B hB => hsorted B (by simp [hB])) p hp
        exact ⟨List.mem_append.mpr (Or.inr h₁), List.mem_append.mpr (Or.inr h₂), h₃⟩

end KKBinPacking.GeometricProof

end

/- Complete checked body: CanonicalGrouping -/
section

set_option autoImplicit false
open KKBinPacking.GeometricGrouping

namespace KKBinPacking.GeometricProof

theorem geomGroups_flatten (k : ℕ) (I : Multiset ℝ) :
    ((geomGroups k I).flatten : Multiset ℝ) = I := by
  rw [geomGroups, geomGroupsList_flatten, Multiset.sort_eq]

theorem geom_partition (k : ℕ) (I : Multiset ℝ) :
    (geomPairs k I).map Prod.fst + geomJ' k I = I := by
  exact (pairs_partition (geomGroups k I)).trans (geomGroups_flatten k I)

theorem geom_pair_properties (k : ℕ) (I : Multiset ℝ) (hI : IsInstance I) :
    ∀ p ∈ geomPairs k I, 0 < p.1 ∧ p.1 ≤ p.2 ∧ p.2 < 1 := by
  have hne := geomGroupsList_groups_nonempty (k : ℝ) (I.sort (· ≥ ·))
  have hs := geomGroupsList_pairwise (k : ℝ) (I.sort (· ≥ ·))
    (Multiset.pairwise_sort I (· ≥ ·))
  intro p hp
  obtain ⟨h₁, h₂, h₃⟩ := pairs_properties (geomGroups k I) hne hs.1 p hp
  have hmem₁ : p.1 ∈ I := by
    rw [← geomGroups_flatten k I]; exact Multiset.mem_coe.mpr h₁
  have hmem₂ : p.2 ∈ I := by
    rw [← geomGroups_flatten k I]; exact Multiset.mem_coe.mpr h₂
  exact ⟨(hI _ hmem₁).1, h₃, (hI _ hmem₂).2⟩

theorem geomJ_instance (k : ℕ) (I : Multiset ℝ) (hI : IsInstance I) :
    IsInstance (geomJ k I) := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
  obtain ⟨hpos, hle, hlt⟩ := geom_pair_properties k I hI p hp
  exact ⟨hpos.trans_le hle, hlt⟩

theorem geomJ'_instance (k : ℕ) (I : Multiset ℝ) (hI : IsInstance I) :
    IsInstance (geomJ' k I) := by
  intro x hx
  apply hI
  rw [← geom_partition k I]
  exact Multiset.mem_add.mpr (Or.inr hx)

theorem geomJ_matching (k : ℕ) (I : Multiset ℝ) :
    ∃ I₀ ≤ I, Multiset.Rel (· ≤ ·) (geomJ k I) I₀ := by
  have hs := geomGroupsList_pairwise (k : ℝ) (I.sort (· ≥ ·))
    (Multiset.pairwise_sort I (· ≥ ·))
  obtain ⟨I₀, hI₀, hrel⟩ := pairs_domination (geomGroups k I) hs.2
  exact ⟨I₀, by rwa [geomGroups_flatten] at hI₀, hrel⟩

theorem geomJ_numSizes_size (k : ℕ) (I : Multiset ℝ) (hI : IsInstance I) :
    (numSizes (geomJ k I) : ℝ) * k ≤ SIZE I := by
  have hcard := pairs_rounded_card (geomGroups k I)
  rw [List.length_tail] at hcard
  have hcount : (numSizes (geomJ k I) : ℝ) ≤
      (((geomGroups k I).length - 1 : ℕ) : ℝ) := by
    exact_mod_cast (hcard : numSizes (geomJ k I) ≤ _)
  have hm := geomGroupsList_count_size (k : ℝ) (I.sort (· ≥ ·))
    (fun x hx => (hI x ((Multiset.mem_sort _).mp hx)).1.le)
  have hs : (I.sort (· ≥ ·)).sum = SIZE I := by
    change (↑(I.sort (· ≥ ·)) : Multiset ℝ).sum = I.sum
    rw [Multiset.sort_eq]
  rw [hs] at hm
  exact (mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg k)).trans hm

end KKBinPacking.GeometricProof

end

/- Complete checked body: AttributedAnyFit -/
section

namespace KKBinPacking.GeometricProof.AttributedAnyFit

-- Prove2me | solution 1 for KKBinPacking.GeometricGrouping.anyFit_card_le
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:05:41.966748+00:00
-- url     : https://prove2.me/submissions/8142180b-473b-4f7c-b9cc-1551cc9a49bd

open KKBinPacking.GeometricGrouping
open KKBinPacking.Shared

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
      have hpos : 0 < P.card := Multiset.card_pos.mpr (by intro he;simp [he] at hb)
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
        simp only [Multiset.join_add]
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

theorem anyFit_card_le_checked (I : Multiset ℝ) (hI : IsInstance I) (g : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1)
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

theorem opt_attained_checked (I : Multiset ℝ) (hI : IsInstance I) :
    ∃ P, IsPacking I P ∧ P.card = OPT I := opt_attained I hI

theorem size_le_opt_checked (I : Multiset ℝ) (hI : IsInstance I) :
    SIZE I ≤ (OPT I : ℝ) := size_le_opt I hI

theorem anyFit_join_checked (P S Q) (h : AnyFit P S Q) :
    Q.join = P.join + S := anyFit_join P S Q h

theorem anyFit_capacity_checked (P S Q) (h : AnyFit P S Q)
    (hP : ∀ b ∈ P, b.sum ≤ 1) (hS : ∀ p ∈ S, p ≤ 1) :
    ∀ b ∈ Q, b.sum ≤ 1 := anyFit_capacity P S Q h hP hS

end KKBinPacking.GeometricProof.AttributedAnyFit
end

/- Complete checked body: TracePacking -/
section

set_option autoImplicit false
open KKBinPacking.GeometricGrouping KKBinPacking.Shared

namespace KKBinPacking.GeometricProof

noncomputable section

theorem sum_le_of_submultiset {A B : Multiset ℝ} (hAB : A ≤ B)
    (hB : ∀ x ∈ B, 0 ≤ x) : A.sum ≤ B.sum := by
  have hs : 0 ≤ (B-A).sum := Multiset.sum_nonneg (fun x hx => hB x (Multiset.mem_of_le (Multiset.sub_le_self B A) hx))
  have he := congrArg Multiset.sum (add_tsub_cancel_of_le hAB)
  rw [Multiset.sum_add] at he
  linarith

theorem principalConfigs_card (x : Multiset ℝ →₀ ℝ) :
    (principalConfigs x).card = principalCount x := by
  classical
  simp [principalConfigs, principalCount]

theorem principalConfigs_mem {I c : Multiset ℝ} {x : Multiset ℝ →₀ ℝ}
    (hx : IsLPFeasible I x) (hc : c ∈ principalConfigs x) : IsConfiguration I c := by
  classical
  simp only [principalConfigs, Multiset.mem_sum] at hc
  obtain ⟨a, ha, hc⟩ := hc
  have he : c = a := (Multiset.mem_replicate.mp hc).2
  subst c
  exact hx.1 a ha

theorem trace_instance {k : ℕ} {g : ℝ} {I : Multiset ℝ}
    (hI : IsInstance I) (tr : Alg2Trace k g I) : ∀ i ≤ tr.t, IsInstance (tr.inst i) := by
  intro i
  induction i with
  | zero =>
    intro _ x hx
    rw [tr.inst_zero] at hx
    exact hI x (Multiset.mem_filter.mp hx).1
  | succ i ih =>
    intro hi x hx
    have hit : i < tr.t := by omega
    have hinst := ih (by omega)
    rw [tr.inst_succ i hit] at hx
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
    have hpm := Multiset.mem_of_le (Multiset.sub_le_self _ _) hp
    obtain ⟨hpos, hle, hlt⟩ := geom_pair_properties k (tr.inst i) hinst p hpm
    exact ⟨hpos, hle.trans_lt hlt⟩

theorem trace_iteration_balance {k : ℕ} {g : ℝ} {I : Multiset ℝ}
    (tr : Alg2Trace k g I) (i : ℕ) (hi : i < tr.t) :
    ((tr.Bp i).map (Multiset.map Prod.fst) + tr.PJ' i).join + tr.inst (i+1) = tr.inst i := by
  rw [Multiset.join_add, ← Multiset.map_join, (tr.PJ'_packing i hi).1, tr.inst_succ i hi]
  calc
    _ = ((tr.Bp i).join.map Prod.fst +
      (geomPairs k (tr.inst i) - (tr.Bp i).join).map Prod.fst) + geomJ' k (tr.inst i) := by ac_rfl
    _ = _ := by rw [← Multiset.map_add, add_tsub_cancel_of_le (tr.Bp_sub i hi), geom_partition]

theorem trace_principal_capacity {k : ℕ} {g : ℝ} {I : Multiset ℝ}
    (hI : IsInstance I) (tr : Alg2Trace k g I) (i : ℕ) (hi : i < tr.t) :
    ∀ b ∈ (tr.Bp i).map (Multiset.map Prod.fst), b.sum ≤ 1 := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
  obtain ⟨c, hc, hac⟩ := Multiset.exists_mem_of_rel_of_mem (tr.Bp_config i hi) ha
  have hcfg := principalConfigs_mem (tr.x_basic i hi).1 hc
  have hinst := trace_instance hI tr i hi.le
  have hrounded := geomJ_instance k (tr.inst i) hinst
  have horder : ∀ p ∈ a, p.1 ≤ p.2 := by
    intro p hp
    have hm := Multiset.mem_of_le (tr.Bp_sub i hi) (Multiset.mem_join.mpr ⟨a, ha, hp⟩)
    exact (geom_pair_properties k (tr.inst i) hinst p hm).2.1
  exact (Multiset.sum_map_le_sum_map Prod.fst Prod.snd horder).trans
    ((sum_le_of_submultiset hac (fun x hx => (hrounded x (hcfg.2.1 x hx)).1.le)).trans hcfg.2.2)

theorem trace_iteration_capacity {k : ℕ} {g : ℝ} {I : Multiset ℝ}
    (hI : IsInstance I) (tr : Alg2Trace k g I) (i : ℕ) (hi : i < tr.t) :
    ∀ b ∈ (tr.Bp i).map (Multiset.map Prod.fst) + tr.PJ' i, b.sum ≤ 1 := by
  intro b hb
  rcases Multiset.mem_add.mp hb with hb | hb
  · exact trace_principal_capacity hI tr i hi b hb
  · exact (tr.PJ'_packing i hi).2 b hb

theorem trace_prefix_balance {k : ℕ} {g : ℝ} {I : Multiset ℝ}
    (tr : Alg2Trace k g I) : ∀ r ≤ tr.t,
    (∑ i ∈ Finset.range r, ((tr.Bp i).map (Multiset.map Prod.fst) + tr.PJ' i)).join +
      tr.inst r = tr.inst 0 := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
    intro hr
    rw [Finset.sum_range_succ, Multiset.join_add, add_assoc,
      trace_iteration_balance tr r (by omega)]
    exact ih (by omega)

theorem trace_step3_packing {k : ℕ} {g : ℝ} {I : Multiset ℝ}
    (hI : IsInstance I) (tr : Alg2Trace k g I) :
    IsPacking (I.filter (fun p => g < p)) (alg2Step3Bins tr.t tr.Bp tr.PJ' tr.P3) := by
  constructor
  · rw [alg2Step3Bins, Multiset.join_add, tr.P3_packing.1]
    exact (trace_prefix_balance tr tr.t le_rfl).trans tr.inst_zero
  · intro b hb
    rw [alg2Step3Bins, Multiset.mem_add] at hb
    rcases hb with hb | hb
    · obtain ⟨i, hi, hb⟩ := Multiset.mem_sum.mp hb
      exact trace_iteration_capacity hI tr i (Finset.mem_range.mp hi) b hb
    · exact tr.P3_packing.2 b hb

theorem trace_final_packing {k : ℕ} {g : ℝ} {I : Multiset ℝ}
    (hI : IsInstance I) (tr : Alg2Trace k g I) : IsPacking I tr.P := by
  have hpack := trace_step3_packing hI tr
  constructor
  · rw [AttributedAnyFit.anyFit_join_checked _ _ _ tr.P_insert, hpack.1]
    simpa only [not_lt] using Multiset.filter_add_not (fun p => g < p) I
  · exact AttributedAnyFit.anyFit_capacity_checked _ _ _ tr.P_insert hpack.2
      (fun p hp => (hI p (Multiset.mem_filter.mp hp).1).2.le)

theorem trace_step3_card {k : ℕ} {g : ℝ} {I : Multiset ℝ}
    (tr : Alg2Trace k g I) :
    (alg2Step3Bins tr.t tr.Bp tr.PJ' tr.P3).card =
      (∑ i ∈ Finset.range tr.t, (principalCount (tr.x i) + (tr.PJ' i).card)) + tr.P3.card := by
  classical
  simp only [alg2Step3Bins, Multiset.card_add, Multiset.card_sum, Multiset.card_map]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Multiset.card_eq_card_of_rel (tr.Bp_config i (Finset.mem_range.mp hi)), principalConfigs_card]

end
end KKBinPacking.GeometricProof

end

/- Complete checked body: WeightedLists -/
section

namespace KKBinPacking.GeometricProof

noncomputable section

def weightedSum {α : Type*} (P : List (α × ℝ)) (f : α → ℝ) : ℝ :=
  (P.map (fun p => p.2 * f p.1)).sum

@[simp] theorem weightedSum_nil {α : Type*} (f : α → ℝ) :
    weightedSum [] f = 0 := rfl

@[simp] theorem weightedSum_cons {α : Type*} (p : α × ℝ) (P : List (α × ℝ))
    (f : α → ℝ) : weightedSum (p :: P) f = p.2 * f p.1 + weightedSum P f := rfl

theorem weightedSum_add {α : Type*} (P : List (α × ℝ)) (f g : α → ℝ) :
    weightedSum P (fun a => f a + g a) = weightedSum P f + weightedSum P g := by
  induction P with
  | nil => simp
  | cons p P ih => simp only [weightedSum_cons, mul_add, ih]; ring

theorem weightedSum_mul {α : Type*} (P : List (α × ℝ)) (f : α → ℝ) (r : ℝ) :
    weightedSum P (fun a => r * f a) = r * weightedSum P f := by
  induction P with
  | nil => simp
  | cons p P ih => simp only [weightedSum_cons, ih]; ring

theorem weightedSum_const {α : Type*} (P : List (α × ℝ)) (r : ℝ) :
    weightedSum P (fun _ => r) = r * weightedSum P (fun _ => 1) := by
  simpa only [mul_one] using weightedSum_mul P (fun _ => 1) r

theorem weightedSum_nonneg {α : Type*} (P : List (α × ℝ)) (f : α → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ p.2) (hf : ∀ p ∈ P, 0 ≤ f p.1) :
    0 ≤ weightedSum P f := by
  apply List.sum_nonneg
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  exact mul_nonneg (hw p hp) (hf p hp)

theorem weightedSum_congr {α : Type*} (P : List (α × ℝ)) (f g : α → ℝ)
    (h : ∀ p ∈ P, f p.1 = g p.1) : weightedSum P f = weightedSum P g := by
  unfold weightedSum
  congr 1
  exact List.map_congr_left (fun p hp => by rw [h p hp])

theorem weightedSum_mono {α : Type*} (P : List (α × ℝ)) (f g : α → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ p.2) (h : ∀ p ∈ P, f p.1 ≤ g p.1) :
    weightedSum P f ≤ weightedSum P g := by
  induction P with
  | nil => simp
  | cons p P ih =>
    rw [weightedSum_cons, weightedSum_cons]
    apply add_le_add (mul_le_mul_of_nonneg_left (h p List.mem_cons_self)
      (hw p List.mem_cons_self))
    exact ih (fun q hq => hw q (List.mem_cons_of_mem p hq))
      (fun q hq => h q (List.mem_cons_of_mem p hq))

def weightedBind {α β : Type*} (P : List (α × ℝ)) (K : α → List (β × ℝ)) :
    List (β × ℝ) :=
  P.flatMap (fun p => (K p.1).map (fun q => (q.1, p.2 * q.2)))

theorem weightedSum_bind {α β : Type*} (P : List (α × ℝ))
    (K : α → List (β × ℝ)) (f : β → ℝ) :
    weightedSum (weightedBind P K) f = weightedSum P (fun a => weightedSum (K a) f) := by
  induction P with
  | nil => simp [weightedBind, weightedSum]
  | cons p P ih =>
    simp only [weightedBind, List.flatMap_cons, weightedSum, List.map_append,
      List.sum_append, List.map_map, Function.comp_def]
    have h : ((K p.1).map (fun q => p.2 * q.2 * f q.1)).sum =
        p.2 * weightedSum (K p.1) f := by
      simp only [mul_assoc, List.sum_map_mul_left, weightedSum]
    rw [h]
    change _ + weightedSum (weightedBind P K) f = _
    rw [ih]
    rfl

theorem weightedBind_mem {α β : Type*} {P : List (α × ℝ)}
    {K : α → List (β × ℝ)} {q : β × ℝ} (hq : q ∈ weightedBind P K) :
    ∃ p ∈ P, ∃ r ∈ K p.1, q = (r.1, p.2 * r.2) := by
  obtain ⟨p, hp, hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨r, hr, he⟩ := List.mem_map.mp hq
  exact ⟨p, hp, r, hr, he.symm⟩

def weightedConvolve (P Q : List (Multiset ℝ × ℝ)) : List (Multiset ℝ × ℝ) :=
  weightedBind P (fun a => Q.map (fun q => (a + q.1, q.2)))

theorem weightedSum_convolve (P Q : List (Multiset ℝ × ℝ)) (f : Multiset ℝ → ℝ)
    (hf : ∀ a b, f (a + b) = f a + f b) :
    weightedSum (weightedConvolve P Q) f =
      weightedSum P f * weightedSum Q (fun _ => 1) +
      weightedSum P (fun _ => 1) * weightedSum Q f := by
  rw [weightedConvolve, weightedSum_bind]
  have hinner (a : Multiset ℝ) :
      weightedSum (Q.map (fun q => (a + q.1, q.2))) f =
        f a * weightedSum Q (fun _ => 1) + weightedSum Q f := by
    simp only [weightedSum, List.map_map, Function.comp_def]
    change weightedSum Q (fun b => f (a + b)) = _
    simp_rw [hf]
    rw [weightedSum_add, weightedSum_const]
    rfl
  simp_rw [hinner]
  rw [weightedSum_add]
  congr 1
  · simpa only [mul_comm] using weightedSum_mul P f (weightedSum Q (fun _ => 1))
  · simpa only [mul_comm] using weightedSum_const P (weightedSum Q f)

theorem weightedConvolve_mass (P Q : List (Multiset ℝ × ℝ)) :
    weightedSum (weightedConvolve P Q) (fun _ => 1) =
      weightedSum P (fun _ => 1) * weightedSum Q (fun _ => 1) := by
  rw [weightedConvolve, weightedSum_bind]
  have h (a : Multiset ℝ) : weightedSum (Q.map (fun q => (a + q.1, q.2)))
      (fun _ => 1) = weightedSum Q (fun _ => 1) := by simp [weightedSum, Function.comp_def]
  simp_rw [h]
  rw [weightedSum_const, mul_comm]

theorem weightedConvolve_mem {P Q : List (Multiset ℝ × ℝ)} {r : Multiset ℝ × ℝ}
    (hr : r ∈ weightedConvolve P Q) :
    ∃ p ∈ P, ∃ q ∈ Q, r = (p.1 + q.1, p.2 * q.2) := by
  obtain ⟨p, hp, a, ha, he⟩ := weightedBind_mem (P := P)
    (K := fun a => Q.map (fun q => (a + q.1, q.2))) hr
  obtain ⟨q, hq, hqa⟩ := List.mem_map.mp ha
  refine ⟨p, hp, q, hq, ?_⟩
  rw [he, ← hqa]

end
end KKBinPacking.GeometricProof

end

/- Complete checked body: ConfigurationKernels -/
section

namespace KKBinPacking.GeometricProof

noncomputable section

def SupportedBelow (A : Multiset ℝ) (b : ℝ) (P : List (Multiset ℝ × ℝ)) : Prop :=
  ∀ p ∈ P, 0 ≤ p.2 ∧ (∀ t ∈ p.1, t ∈ A) ∧ p.1.sum ≤ b

theorem supportedBelow_convolve {A : Multiset ℝ} {b c : ℝ}
    {P Q : List (Multiset ℝ × ℝ)} (hP : SupportedBelow A b P)
    (hQ : SupportedBelow A c Q) : SupportedBelow A (b + c) (weightedConvolve P Q) := by
  intro r hr
  obtain ⟨p, hp, q, hq, rfl⟩ := weightedConvolve_mem hr
  obtain ⟨hp0, hpt, hps⟩ := hP p hp
  obtain ⟨hq0, hqt, hqs⟩ := hQ q hq
  refine ⟨mul_nonneg hp0 hq0, ?_, ?_⟩
  · intro t ht
    rcases Multiset.mem_add.mp ht with ht | ht
    · exact hpt t ht
    · exact hqt t ht
  · simpa only [Multiset.sum_add] using add_le_add hps hqs

theorem configuration_kernel_exists (A c : Multiset ℝ)
    (K : ℝ → List (Multiset ℝ × ℝ))
    (hK : ∀ s ∈ c, SupportedBelow A s (K s) ∧ weightedSum (K s) (fun _ => 1) = 1) :
    ∃ P : List (Multiset ℝ × ℝ), SupportedBelow A c.sum P ∧
      weightedSum P (fun _ => 1) = 1 ∧
      ∀ t : ℝ, weightedSum P (fun b => (b.count t : ℝ)) =
        (c.map (fun s => weightedSum (K s) (fun b => (b.count t : ℝ)))).sum := by
  classical
  induction c using Multiset.induction_on with
  | empty =>
    refine ⟨[(0, 1)], ?_, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst p
      simp [Multiset.sum_zero]
    · simp
    · intro t
      simp
  | @cons s c ih =>
    obtain ⟨P, hP, hPm, hPc⟩ := ih (fun t ht => hK t (Multiset.mem_cons_of_mem ht))
    obtain ⟨hs, hsm⟩ := hK s (Multiset.mem_cons_self s c)
    refine ⟨weightedConvolve (K s) P, ?_, ?_, ?_⟩
    · simpa only [Multiset.sum_cons] using supportedBelow_convolve hs hP
    · rw [weightedConvolve_mass, hsm, hPm, mul_one]
    · intro t
      rw [weightedSum_convolve _ _ _ (by intro a b; simp [Multiset.count_add]),
        hPm, hsm, mul_one, one_mul, hPc, Multiset.map_cons, Multiset.sum_cons]

end
end KKBinPacking.GeometricProof

end

/- Complete checked body: ReplacementRows -/
section

namespace KKBinPacking.GeometricProof

noncomputable section

def replacementRow (U : Multiset ℝ) (b : ℝ) : List (Multiset ℝ × ℝ) :=
  (0, 1 - (U.card : ℝ) / b) :: U.toList.map (fun t => ({t}, 1 / b))

theorem singleton_list_mean (U : Multiset ℝ) (a : ℝ) (f : Multiset ℝ → ℝ) :
    weightedSum (U.toList.map (fun t => ({t}, a))) f =
      a * (U.map (fun t => f {t})).sum := by
  simp only [weightedSum, List.map_map, Function.comp_def, Multiset.sum_map_toList]
  induction U using Multiset.induction_on with
  | empty => simp
  | cons t U ih => simp only [Multiset.map_cons, Multiset.sum_cons, ih]; ring

theorem replacementRow_mass (U : Multiset ℝ) (b : ℝ) :
    weightedSum (replacementRow U b) (fun _ => 1) = 1 := by
  rw [replacementRow, weightedSum_cons, singleton_list_mean]
  dsimp only
  have hsum : (U.map (fun _ : ℝ => (1 : ℝ))).sum = (U.card : ℝ) := by simp
  rw [hsum]
  ring

theorem replacementRow_supported {A U : Multiset ℝ} {s b : ℝ}
    (hs : 0 ≤ s) (hb : 0 < b) (hc : (U.card : ℝ) ≤ b)
    (hU : ∀ t ∈ U, t ∈ A ∧ t ≤ s) :
    SupportedBelow A s (replacementRow U b) := by
  intro p hp
  rcases List.mem_cons.mp hp with hp | hp
  · subst p
    refine ⟨sub_nonneg.mpr ((div_le_one₀ hb).mpr hc), ?_, ?_⟩
    · simp
    · simpa using hs
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
    have htU := Multiset.mem_toList.mp ht
    refine ⟨by positivity, ?_, ?_⟩
    · intro u hu
      have : u = t := Multiset.mem_singleton.mp hu
      rw [this]
      exact (hU t htU).1
    · simpa using (hU t htU).2

theorem replacementRow_count (U : Multiset ℝ) (b t : ℝ) :
    weightedSum (replacementRow U b) (fun c => (c.count t : ℝ)) =
      (U.count t : ℝ) / b := by
  classical
  rw [replacementRow, weightedSum_cons, singleton_list_mean]
  simp only [Multiset.count_zero, Nat.cast_zero, mul_zero, zero_add]
  have hcount : (U.map (fun s => (({s} : Multiset ℝ).count t : ℝ))).sum =
      (U.count t : ℝ) := by
    induction U using Multiset.induction_on with
    | empty => simp
    | @cons s U ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih]
      by_cases h : s = t
      · subst s
        simp [add_comm]
      · simp [Ne.symm h]
  rw [hcount]
  ring

end
end KKBinPacking.GeometricProof

end

/- Complete checked body: WeightedLP -/
section

namespace KKBinPacking.GeometricProof
open KKBinPacking.Shared

noncomputable section

def lpEval (f : Multiset ℝ → ℝ) (x : Multiset ℝ →₀ ℝ) : ℝ :=
  x.sum (fun c w => w * f c)

@[simp] theorem lpEval_zero (f : Multiset ℝ → ℝ) : lpEval f 0 = 0 := by
  simp [lpEval]

theorem lpEval_add (f : Multiset ℝ → ℝ) (x y : Multiset ℝ →₀ ℝ) :
    lpEval f (x + y) = lpEval f x + lpEval f y := by
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem lpEval_sub (f : Multiset ℝ → ℝ) (x y : Multiset ℝ →₀ ℝ) :
    lpEval f (x - y) = lpEval f x - lpEval f y := by
  exact Finsupp.sum_sub_index (fun _ _ _ => sub_mul _ _ _)

@[simp] theorem lpEval_single (f : Multiset ℝ → ℝ) (c : Multiset ℝ) (w : ℝ) :
    lpEval f (Finsupp.single c w) = w * f c := by
  exact Finsupp.sum_single_index (zero_mul _)

theorem lpCost_eq_eval (x : Multiset ℝ →₀ ℝ) : lpCost x = lpEval (fun _ => 1) x := by
  simp [lpCost, lpEval, Finsupp.sum]

def listLP : List (Multiset ℝ × ℝ) → (Multiset ℝ →₀ ℝ)
  | [] => 0
  | p :: P => (if p.1 = 0 then 0 else Finsupp.single p.1 p.2) + listLP P

theorem lpEval_listLP (P : List (Multiset ℝ × ℝ)) (f : Multiset ℝ → ℝ) (hf : f 0 = 0) :
    lpEval f (listLP P) = weightedSum P f := by
  induction P with
  | nil => simp [listLP]
  | cons p P ih =>
    rw [listLP, lpEval_add, ih, weightedSum_cons]
    split_ifs with h
    · simp [h, hf]
    · rw [lpEval_single]

theorem listLP_nonneg (P : List (Multiset ℝ × ℝ)) (hw : ∀ p ∈ P, 0 ≤ p.2) :
    ∀ c, 0 ≤ listLP P c := by
  classical
  induction P with
  | nil => simp [listLP]
  | cons p P ih =>
    intro c
    have hp := hw p List.mem_cons_self
    have hr := ih (fun q hq => hw q (List.mem_cons_of_mem p hq)) c
    rw [listLP, Finsupp.add_apply]
    apply add_nonneg _ hr
    split_ifs
    · simp
    · by_cases hc : p.1 = c
      · simp [hc, hp]
      · rw [Finsupp.single_eq_of_ne (Ne.symm hc)]

theorem listLP_support (P : List (Multiset ℝ × ℝ)) (Q : Multiset ℝ → Prop)
    (hQ : ∀ p ∈ P, p.1 ≠ 0 → Q p.1) :
    ∀ c ∈ (listLP P).support, Q c := by
  classical
  induction P with
  | nil => simp [listLP]
  | cons p P ih =>
    intro c hc
    rw [listLP] at hc
    have hmem := Finsupp.support_add hc
    rcases Finset.mem_union.mp hmem with hc | hc
    · split_ifs at hc with h
      · simp at hc
      · have he : c = p.1 := Finset.mem_singleton.mp (Finsupp.support_single_subset hc)
        rw [he]
        exact hQ p List.mem_cons_self h
    · exact ih (fun q hq => hQ q (List.mem_cons_of_mem p hq)) c hc

theorem listLP_cost_le (P : List (Multiset ℝ × ℝ)) (hw : ∀ p ∈ P, 0 ≤ p.2) :
    lpCost (listLP P) ≤ weightedSum P (fun _ => 1) := by
  rw [lpCost_eq_eval]
  induction P with
  | nil => simp [listLP]
  | cons p P ih =>
    have hp := hw p List.mem_cons_self
    have hr := ih (fun q hq => hw q (List.mem_cons_of_mem p hq))
    rw [listLP, lpEval_add, weightedSum_cons]
    split_ifs
    · simp only [lpEval_zero, zero_add, mul_one]
      linarith
    · simpa only [lpEval_single, mul_one] using add_le_add_right hr p.2

theorem lpFeasible_of_list (A : Multiset ℝ) (P : List (Multiset ℝ × ℝ))
    (hP : SupportedBelow A 1 P)
    (hcover : ∀ t ∈ A, (A.count t : ℝ) ≤ weightedSum P (fun c => (c.count t : ℝ))) :
    IsLPFeasible A (listLP P) := by
  classical
  refine ⟨listLP_support P (IsConfiguration A) ?_,
    listLP_nonneg P (fun p hp => (hP p hp).1), ?_⟩
  · intro p hp hne
    exact ⟨hne, (hP p hp).2⟩
  · intro t ht
    have hh := hcover t (Multiset.mem_toFinset.mp ht)
    rw [← lpEval_listLP P (fun c => (c.count t : ℝ)) (by simp)] at hh
    exact hh

end
end KKBinPacking.GeometricProof

end

/- Complete checked body: LPLinearSums -/
section

namespace KKBinPacking.GeometricProof

noncomputable section

def sourceWeights (x : Multiset ℝ →₀ ℝ) : List (Multiset ℝ × ℝ) :=
  x.support.toList.map (fun c => (c, x c))

theorem sourceWeights_mean (x : Multiset ℝ →₀ ℝ) (f : Multiset ℝ → ℝ) :
    weightedSum (sourceWeights x) f = lpEval f x := by
  classical
  simp [weightedSum, sourceWeights, Function.comp_def, lpEval, Finsupp.sum]

theorem sourceWeights_mem {x : Multiset ℝ →₀ ℝ} {p : Multiset ℝ × ℝ}
    (hp : p ∈ sourceWeights x) : p.1 ∈ x.support ∧ p.2 = x p.1 := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
  exact ⟨Finset.mem_toList.mp hc, rfl⟩

theorem multiset_sum_count_expansion (c : Multiset ℝ) (S : Finset ℝ) (f : ℝ → ℝ)
    (hc : c.toFinset ⊆ S) :
    (c.map f).sum = ∑ s ∈ S, (c.count s : ℝ) * f s := by
  classical
  rw [Finset.sum_multiset_map_count]
  simp only [nsmul_eq_mul]
  apply Finset.sum_subset hc
  intro s _ hs
  have : c.count s = 0 := Multiset.count_eq_zero.mpr (by simpa using hs)
  simp [this]

theorem lpEval_count_swap (x : Multiset ℝ →₀ ℝ) (S : Finset ℝ) (f : ℝ → ℝ)
    (hx : ∀ c ∈ x.support, c.toFinset ⊆ S) :
    lpEval (fun c => (c.map f).sum) x =
      ∑ s ∈ S, lpEval (fun c => (c.count s : ℝ)) x * f s := by
  classical
  unfold lpEval Finsupp.sum
  calc
    _ = ∑ c ∈ x.support, x c * ∑ s ∈ S, (c.count s : ℝ) * f s := by
      apply Finset.sum_congr rfl
      intro c hc
      dsimp only
      rw [multiset_sum_count_expansion c S f (hx c hc)]
    _ = _ := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_mul]

end
end KKBinPacking.GeometricProof

end

/- Complete checked body: LPTransportRows -/
section

namespace KKBinPacking.GeometricProof
open KKBinPacking.Shared KKBinPacking.GeometricGrouping

noncomputable section

theorem lp_transport_rows (A B : Multiset ℝ) (hB : IsInstance B)
    (U : ℝ → Multiset ℝ)
    (hU : ∀ s ∈ B, ∀ t ∈ U s, t ∈ A ∧ t ≤ s)
    (hcard : ∀ s ∈ B, (U s).card ≤ B.count s)
    (hcover : ∀ t ∈ A, (A.count t : ℝ) ≤
      ∑ s ∈ B.toFinset, ((U s).count t : ℝ))
    (x : Multiset ℝ →₀ ℝ) (hx : IsLPFeasible B x) :
    ∃ y : Multiset ℝ →₀ ℝ, IsLPFeasible A y ∧ lpCost y ≤ lpCost x := by
  classical
  let K (s : ℝ) := replacementRow (U s) (B.count s)
  have hrow (s : ℝ) (hs : s ∈ B) : SupportedBelow A s (K s) ∧
      weightedSum (K s) (fun _ => 1) = 1 := by
    refine ⟨replacementRow_supported (hB s hs).1.le ?_ ?_ (hU s hs),
      replacementRow_mass _ _⟩
    · exact_mod_cast Multiset.count_pos.mpr hs
    · exact_mod_cast hcard s hs
  have hall (c : x.support) : ∃ P : List (Multiset ℝ × ℝ),
      SupportedBelow A c.val.sum P ∧ weightedSum P (fun _ => 1) = 1 ∧
      ∀ t : ℝ, weightedSum P (fun b => (b.count t : ℝ)) =
        (c.val.map (fun s => weightedSum (K s) (fun b => (b.count t : ℝ)))).sum := by
    apply configuration_kernel_exists
    intro s hs
    exact hrow s ((hx.1 c.val c.property).2.1 s hs)
  choose P hP hmass hmoment using hall
  let C (c : Multiset ℝ) : List (Multiset ℝ × ℝ) :=
    if hc : c ∈ x.support then P ⟨c, hc⟩ else []
  have hC (c : Multiset ℝ) (hc : c ∈ x.support) :
      SupportedBelow A 1 (C c) ∧ weightedSum (C c) (fun _ => 1) = 1 ∧
      ∀ t : ℝ, weightedSum (C c) (fun b => (b.count t : ℝ)) =
        (c.map (fun s => weightedSum (K s) (fun b => (b.count t : ℝ)))).sum := by
    simp only [C, dif_pos hc]
    refine ⟨?_, hmass ⟨c, hc⟩, hmoment ⟨c, hc⟩⟩
    intro p hp
    obtain ⟨hw, ht, hb⟩ := hP ⟨c, hc⟩ p hp
    exact ⟨hw, ht, hb.trans (hx.1 c hc).2.2⟩
  let L := weightedBind (sourceWeights x) C
  have hL : SupportedBelow A 1 L := by
    intro q hq
    obtain ⟨p, hp, r, hr, he⟩ := weightedBind_mem hq
    obtain ⟨hps, hpw⟩ := sourceWeights_mem hp
    obtain ⟨hr0, hrt, hrs⟩ := (hC p.1 hps).1 r hr
    rw [he]
    exact ⟨mul_nonneg (by rw [hpw]; exact hx.2.1 p.1) hr0, hrt, hrs⟩
  have hLmass : weightedSum L (fun _ => 1) = lpCost x := by
    rw [weightedSum_bind]
    calc
      _ = weightedSum (sourceWeights x) (fun _ => 1) := by
        apply weightedSum_congr
        intro p hp
        exact (hC p.1 (sourceWeights_mem hp).1).2.1
      _ = lpCost x := by rw [sourceWeights_mean, lpCost_eq_eval]
  have hLcount (t : ℝ) (ht : t ∈ A) :
      (A.count t : ℝ) ≤ weightedSum L (fun c => (c.count t : ℝ)) := by
    let f (s : ℝ) := weightedSum (K s) (fun c => (c.count t : ℝ))
    have hf (s : ℝ) : f s = ((U s).count t : ℝ) / (B.count s : ℝ) :=
      replacementRow_count _ _ _
    have he : weightedSum L (fun c => (c.count t : ℝ)) =
        ∑ s ∈ B.toFinset, lpEval (fun c => (c.count s : ℝ)) x * f s := by
      rw [weightedSum_bind]
      calc
        _ = weightedSum (sourceWeights x) (fun c => (c.map f).sum) := by
          apply weightedSum_congr
          intro p hp
          exact (hC p.1 (sourceWeights_mem hp).1).2.2 t
        _ = _ := by
          rw [sourceWeights_mean]
          apply lpEval_count_swap
          intro c hc s hs
          exact Multiset.mem_toFinset.mpr ((hx.1 c hc).2.1 s (Multiset.mem_toFinset.mp hs))
    rw [he]
    apply (hcover t ht).trans
    apply Finset.sum_le_sum
    intro s hs
    have hb : (0 : ℝ) < B.count s := by
      exact_mod_cast Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hs)
    have hc := hx.2.2 s hs
    have hf0 : 0 ≤ f s := by rw [hf]; positivity
    have hm := mul_le_mul_of_nonneg_right hc hf0
    rw [hf] at hm ⊢
    have hh : (B.count s : ℝ) * ((U s).count t / (B.count s : ℝ)) = (U s).count t := by
      field_simp [ne_of_gt hb]
    rw [hh] at hm
    exact hm
  refine ⟨listLP L, lpFeasible_of_list A L hL hLcount, ?_⟩
  exact (listLP_cost_le L (fun p hp => (hL p hp).1)).trans_eq hLmass

end
end KKBinPacking.GeometricProof

end

/- Complete checked body: LPBasic -/
section

namespace KKBinPacking.GeometricProof
open KKBinPacking.Shared KKBinPacking.GeometricGrouping

noncomputable section

theorem lpCost_nonneg {I : Multiset ℝ} {x : Multiset ℝ →₀ ℝ}
    (hx : IsLPFeasible I x) : 0 ≤ lpCost x :=
  Finset.sum_nonneg (fun c _ => hx.2.1 c)

def binsWeighted (P : Multiset (Multiset ℝ)) : List (Multiset ℝ × ℝ) :=
  P.toList.map (fun c => (c, 1))

theorem binsWeighted_mean (P : Multiset (Multiset ℝ)) (f : Multiset ℝ → ℝ) :
    weightedSum (binsWeighted P) f = (P.map f).sum := by
  simp [weightedSum, binsWeighted, Function.comp_def, Multiset.sum_map_toList]

theorem binsWeighted_count (P : Multiset (Multiset ℝ)) (t : ℝ) :
    weightedSum (binsWeighted P) (fun c => (c.count t : ℝ)) = (P.join.count t : ℝ) := by
  classical
  rw [binsWeighted_mean]
  induction P using Multiset.induction_on with
  | empty => simp
  | cons c P ih => simp [ih, Multiset.count_add]

theorem packing_lp_feasible {I : Multiset ℝ} {P : Multiset (Multiset ℝ)}
    (hP : IsPacking I P) : IsLPFeasible I (listLP (binsWeighted P)) := by
  apply lpFeasible_of_list
  · intro p hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    have hcP := Multiset.mem_toList.mp hc
    refine ⟨zero_le_one, ?_, hP.2 c hcP⟩
    intro t ht
    rw [← hP.1]
    exact Multiset.mem_join.mpr ⟨c, hcP, ht⟩
  · intro t _
    rw [binsWeighted_count, hP.1]

theorem packing_lp_cost_le (P : Multiset (Multiset ℝ)) :
    lpCost (listLP (binsWeighted P)) ≤ (P.card : ℝ) := by
  have hw : ∀ p ∈ binsWeighted P, 0 ≤ p.2 := by
    intro p hp
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hp
    exact zero_le_one
  have h := listLP_cost_le (binsWeighted P) hw
  simpa [binsWeighted_mean, Multiset.map_const, Multiset.sum_replicate] using h

theorem lp_feasible_exists (I : Multiset ℝ) (hI : IsInstance I) :
    ∃ x, IsLPFeasible I x := by
  obtain ⟨P, hP, _⟩ := AttributedAnyFit.opt_attained_checked I hI
  exact ⟨_, packing_lp_feasible hP⟩

theorem lin_le_cost {I : Multiset ℝ} {x : Multiset ℝ →₀ ℝ}
    (hx : IsLPFeasible I x) : LIN I ≤ lpCost x := by
  apply csInf_le
  · exact ⟨0, by rintro z ⟨y, hy, rfl⟩; exact lpCost_nonneg hy⟩
  · exact ⟨x, hx, rfl⟩

theorem lin_nonneg (I : Multiset ℝ) (hI : IsInstance I) : 0 ≤ LIN I := by
  apply le_csInf
  · obtain ⟨x, hx⟩ := lp_feasible_exists I hI
    exact ⟨lpCost x, x, hx, rfl⟩
  · rintro z ⟨x, hx, rfl⟩
    exact lpCost_nonneg hx

theorem lin_le_opt (I : Multiset ℝ) (hI : IsInstance I) : LIN I ≤ (OPT I : ℝ) := by
  obtain ⟨P, hP, hcard⟩ := AttributedAnyFit.opt_attained_checked I hI
  exact (lin_le_cost (packing_lp_feasible hP)).trans (by simpa [hcard] using packing_lp_cost_le P)

end
end KKBinPacking.GeometricProof

end

/- Complete checked body: MatchingFibers -/
section

namespace KKBinPacking.GeometricProof

noncomputable section

theorem matching_pairs {A B : Multiset ℝ} (h : Multiset.Rel (· ≤ ·) A B) :
    ∃ M : Multiset (ℝ × ℝ), M.map Prod.fst = A ∧ M.map Prod.snd = B ∧
      ∀ p ∈ M, p.1 ≤ p.2 := by
  induction h with
  | zero => exact ⟨0, rfl, rfl, by simp⟩
  | @cons a b A B hab _ ih =>
    obtain ⟨M, hA, hB, hM⟩ := ih
    refine ⟨(a,b) ::ₘ M, by simp [hA], by simp [hB], ?_⟩
    intro p hp
    rcases Multiset.mem_cons.mp hp with rfl | hp
    · exact hab
    · exact hM p hp

def matchingFiber (M : Multiset (ℝ × ℝ)) (s : ℝ) : Multiset ℝ :=
  (M.filter (fun p => p.2 = s)).map Prod.fst

theorem matchingFiber_card (M : Multiset (ℝ × ℝ)) (s : ℝ) :
    (matchingFiber M s).card = (M.map Prod.snd).count s := by
  classical
  simp only [matchingFiber, Multiset.card_map, Multiset.count_map]
  congr 2
  funext p
  exact propext eq_comm

theorem matchingFiber_mem {M : Multiset (ℝ × ℝ)} {s t : ℝ}
    (ht : t ∈ matchingFiber M s) : (t,s) ∈ M := by
  obtain ⟨p, hp, ht⟩ := Multiset.mem_map.mp ht
  obtain ⟨hpM, hps⟩ := Multiset.mem_filter.mp hp
  have he : p = (t,s) := Prod.ext ht hps
  exact he ▸ hpM

theorem matchingFiber_count_sum (M : Multiset (ℝ × ℝ)) (S : Finset ℝ)
    (hS : ∀ p ∈ M, p.2 ∈ S) (t : ℝ) :
    ∑ s ∈ S, ((matchingFiber M s).count t : ℝ) = ((M.map Prod.fst).count t : ℝ) := by
  classical
  induction M using Multiset.induction_on with
  | empty => simp [matchingFiber]
  | @cons p M ih =>
    have hp : p.2 ∈ S := hS p (Multiset.mem_cons_self p M)
    have hM := ih (fun q hq => hS q (Multiset.mem_cons_of_mem hq))
    have he (s : ℝ) : ((matchingFiber (p ::ₘ M) s).count t : ℝ) =
        (if p.2 = s then (if p.1 = t then 1 else 0) else 0) +
        ((matchingFiber M s).count t : ℝ) := by
      by_cases hs : p.2 = s <;> by_cases ht : p.1 = t <;>
        simp [matchingFiber, hs, ht, Ne.symm, add_comm]
    simp_rw [he]
    rw [Finset.sum_add_distrib, hM]
    have hi : (∑ s ∈ S, if p.2 = s then (if p.1 = t then (1 : ℝ) else 0) else 0) =
        if p.1 = t then 1 else 0 := by simp [hp]
    rw [hi]
    by_cases ht : p.1 = t <;> simp [ht, Ne.symm, add_comm]

end
end KKBinPacking.GeometricProof

end

/- Complete checked body: LPTransport -/
section

namespace KKBinPacking.GeometricProof
open KKBinPacking.Shared KKBinPacking.GeometricGrouping

noncomputable section

theorem lp_transport {A B : Multiset ℝ} (hB : IsInstance B)
    (hmatch : ∃ B₀ ≤ B, Multiset.Rel (· ≤ ·) A B₀)
    {x : Multiset ℝ →₀ ℝ} (hx : IsLPFeasible B x) :
    ∃ y : Multiset ℝ →₀ ℝ, IsLPFeasible A y ∧ lpCost y ≤ lpCost x := by
  classical
  obtain ⟨B₀, hB₀, hm⟩ := hmatch
  obtain ⟨M, hMA, hMB, hM⟩ := matching_pairs hm
  apply lp_transport_rows A B hB (matchingFiber M) _ _ _ x hx
  · intro s _ t ht
    have hp := matchingFiber_mem ht
    refine ⟨?_, hM (t,s) hp⟩
    rw [← hMA]
    exact Multiset.mem_map.mpr ⟨(t,s), hp, rfl⟩
  · intro s _
    rw [matchingFiber_card, hMB]
    exact (Multiset.le_iff_count.mp hB₀) s
  · intro t _
    have hS : ∀ p ∈ M, p.2 ∈ B.toFinset := by
      intro p hp
      apply Multiset.mem_toFinset.mpr
      apply Multiset.mem_of_le hB₀
      rw [← hMB]
      exact Multiset.mem_map.mpr ⟨p, hp, rfl⟩
    rw [matchingFiber_count_sum M B.toFinset hS t, hMA]

theorem lin_mono_matching {A B : Multiset ℝ} (hB : IsInstance B)
    (hmatch : ∃ B₀ ≤ B, Multiset.Rel (· ≤ ·) A B₀) : LIN A ≤ LIN B := by
  apply le_csInf
  · obtain ⟨x, hx⟩ := lp_feasible_exists B hB
    exact ⟨lpCost x, x, hx, rfl⟩
  · rintro z ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hcost⟩ := lp_transport hB hmatch hx
    exact (lin_le_cost hy).trans hcost

theorem lin_mono_submultiset {A B : Multiset ℝ} (hB : IsInstance B) (hAB : A ≤ B) :
    LIN A ≤ LIN B :=
  lin_mono_matching hB ⟨A, hAB, Multiset.rel_refl_of_refl_on (fun _ _ => le_rfl)⟩

end
end KKBinPacking.GeometricProof

end

/- Complete checked body: LPRestriction -/
section

namespace KKBinPacking.GeometricProof
open KKBinPacking.Shared KKBinPacking.GeometricGrouping

noncomputable section

theorem multiset_filter_sum_le (c : Multiset ℝ) (p : ℝ → Prop) [DecidablePred p]
    (hc : ∀ t ∈ c, 0 ≤ t) : (c.filter p).sum ≤ c.sum := by
  induction c using Multiset.induction_on with
  | empty => simp
  | @cons t c ih =>
    have ht := hc t (Multiset.mem_cons_self t c)
    have hr := ih (fun s hs => hc s (Multiset.mem_cons_of_mem hs))
    by_cases hp : p t
    · simpa [hp] using add_le_add_left hr t
    · simp only [Multiset.filter_cons_of_neg c hp, Multiset.sum_cons]
      linarith

theorem lp_restrict_types (A B : Multiset ℝ) (hB : IsInstance B)
    (x : Multiset ℝ →₀ ℝ)
    (hxconf : ∀ c ∈ x.support, IsConfiguration B c) (hxpos : ∀ c, 0 ≤ x c)
    (hcover : ∀ t ∈ A, (A.count t : ℝ) ≤ lpEval (fun c => (c.count t : ℝ)) x) :
    ∃ y : Multiset ℝ →₀ ℝ, IsLPFeasible A y ∧ lpCost y ≤ lpCost x := by
  classical
  let L := (sourceWeights x).map (fun p => (p.1.filter (fun s => s ∈ A), p.2))
  have hmean (f : Multiset ℝ → ℝ) :
      weightedSum L f = lpEval (fun c => f (c.filter (fun s => s ∈ A))) x := by
    change weightedSum ((sourceWeights x).map _) f = _
    simp only [weightedSum, List.map_map, Function.comp_def]
    exact sourceWeights_mean x (fun c => f (c.filter (fun s => s ∈ A)))
  have hL : SupportedBelow A 1 L := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨hqs, hqw⟩ := sourceWeights_mem hq
    refine ⟨by rw [hqw]; exact hxpos q.1, ?_, ?_⟩
    · intro t ht
      exact (Multiset.mem_filter.mp ht).2
    · exact (multiset_filter_sum_le q.1 _ (fun t ht =>
        (hB t ((hxconf q.1 hqs).2.1 t ht)).1.le)).trans (hxconf q.1 hqs).2.2
  have hLc (t : ℝ) (ht : t ∈ A) :
      (A.count t : ℝ) ≤ weightedSum L (fun c => (c.count t : ℝ)) := by
    rw [hmean]
    simpa only [Multiset.count_filter_of_pos ht] using hcover t ht
  refine ⟨listLP L, lpFeasible_of_list A L hL hLc, ?_⟩
  have hh := listLP_cost_le L (fun p hp => (hL p hp).1)
  rw [hmean, ← lpCost_eq_eval] at hh
  exact hh

end
end KKBinPacking.GeometricProof

end

/- Complete checked body: LPSize -/
section

namespace KKBinPacking.GeometricProof
open KKBinPacking.Shared KKBinPacking.GeometricGrouping

theorem lp_size_le_cost {I : Multiset ℝ} (hI : IsInstance I)
    {x : Multiset ℝ →₀ ℝ} (hx : IsLPFeasible I x) : SIZE I ≤ lpCost x := by
  classical
  have hsum : SIZE I = ∑ s ∈ I.toFinset, (I.count s : ℝ) * s := by
    simpa [SIZE] using multiset_sum_count_expansion I I.toFinset id Finset.Subset.rfl
  have hswap : lpEval Multiset.sum x =
      ∑ s ∈ I.toFinset, lpEval (fun c => (c.count s : ℝ)) x * s := by
    simpa using lpEval_count_swap x I.toFinset id (by
      intro c hc s hs
      exact Multiset.mem_toFinset.mpr ((hx.1 c hc).2.1 s (Multiset.mem_toFinset.mp hs)))
  calc
    SIZE I ≤ lpEval Multiset.sum x := by
      rw [hsum, hswap]
      exact Finset.sum_le_sum (fun s hs => mul_le_mul_of_nonneg_right (hx.2.2 s hs)
        (hI s (Multiset.mem_toFinset.mp hs)).1.le)
    _ ≤ lpCost x := by
      rw [lpCost_eq_eval, ← sourceWeights_mean, ← sourceWeights_mean]
      apply weightedSum_mono
      · intro p hp
        rw [(sourceWeights_mem hp).2]
        exact hx.2.1 p.1
      · intro p hp
        exact (hx.1 p.1 (sourceWeights_mem hp).1).2.2

end KKBinPacking.GeometricProof

end

/- Complete checked body: FractionalRemainder -/
section

namespace KKBinPacking.GeometricProof
open KKBinPacking.Shared KKBinPacking.GeometricGrouping

noncomputable section

def floorVector (x : Multiset ℝ →₀ ℝ) : Multiset ℝ →₀ ℝ :=
  x.mapRange (fun w => (⌊w⌋₊ : ℝ)) (by simp)

def fractionVector (x : Multiset ℝ →₀ ℝ) : Multiset ℝ →₀ ℝ := x - floorVector x

@[simp] theorem floorVector_apply (x : Multiset ℝ →₀ ℝ) (c : Multiset ℝ) :
    floorVector x c = (⌊x c⌋₊ : ℝ) := rfl

@[simp] theorem fractionVector_apply (x : Multiset ℝ →₀ ℝ) (c : Multiset ℝ) :
    fractionVector x c = x c - (⌊x c⌋₊ : ℝ) := rfl

theorem fractionVector_support (x : Multiset ℝ →₀ ℝ) :
    (fractionVector x).support ⊆ x.support := by
  intro c hc
  have hm := Finsupp.support_sub hc
  exact (Finset.mem_union.mp hm).elim id (fun h => Finsupp.support_mapRange h)

theorem fractionVector_nonneg (x : Multiset ℝ →₀ ℝ) (hx : ∀ c, 0 ≤ x c) :
    ∀ c, 0 ≤ fractionVector x c := fun c => sub_nonneg.mpr (Nat.floor_le (hx c))

theorem fractionVector_lt_one (x : Multiset ℝ →₀ ℝ) (c : Multiset ℝ) :
    fractionVector x c < 1 := by
  have h := Nat.lt_floor_add_one (x c)
  change x c - (⌊x c⌋₊ : ℝ) < 1
  linarith

theorem floorVector_eval (x : Multiset ℝ →₀ ℝ) (f : Multiset ℝ → ℝ) :
    lpEval f (floorVector x) = ∑ c ∈ x.support, (⌊x c⌋₊ : ℝ) * f c := by
  exact Finsupp.sum_mapRange_index (fun _ => zero_mul _)

theorem fractionVector_cost (x : Multiset ℝ →₀ ℝ) :
    lpCost (fractionVector x) = lpCost x - (principalCount x : ℝ) := by
  rw [lpCost_eq_eval, fractionVector, lpEval_sub, floorVector_eval, ← lpCost_eq_eval]
  simp [principalCount, Nat.cast_sum]

theorem fractionVector_cost_le_support (x : Multiset ℝ →₀ ℝ) :
    lpCost (fractionVector x) ≤ (x.support.card : ℝ) := by
  unfold lpCost
  calc
    _ ≤ ∑ _c ∈ (fractionVector x).support, (1 : ℝ) :=
      Finset.sum_le_sum (fun c _ => (fractionVector_lt_one x c).le)
    _ = ((fractionVector x).support.card : ℝ) := by simp
    _ ≤ (x.support.card : ℝ) := by exact_mod_cast Finset.card_le_card (fractionVector_support x)

theorem principal_slots_count (x : Multiset ℝ →₀ ℝ) (t : ℝ) :
    ((principalConfigs x).join.count t : ℝ) = lpEval (fun c => (c.count t : ℝ)) (floorVector x) := by
  classical
  rw [floorVector_eval]
  unfold principalConfigs
  generalize x.support = S
  induction S using Finset.induction_on with
  | empty => simp
  | @insert c S hc ih =>
    rw [Finset.sum_insert hc, Finset.sum_insert hc, Multiset.join_add, Multiset.count_add,
      Nat.cast_add, ih]
    congr 1
    have hrep : (Multiset.replicate ⌊x c⌋₊ c).join = ⌊x c⌋₊ • c := by
      exact Multiset.sum_replicate _ _
    rw [hrep, Multiset.count_nsmul, Nat.cast_mul]

end
end KKBinPacking.GeometricProof

end

/- Complete checked body: ResidualLP -/
section

namespace KKBinPacking.GeometricProof
open KKBinPacking.Shared KKBinPacking.GeometricGrouping

noncomputable section

theorem residual_count_coverage (M T : Multiset (ℝ × ℝ)) (hT : T ≤ M)
    (x : Multiset ℝ →₀ ℝ) (hx : IsLPFeasible (M.map Prod.snd) x)
    (hmax : ∀ s, (T.map Prod.snd).count s =
      min ((M.map Prod.snd).count s) ((principalConfigs x).join.count s))
    (t : ℝ) (ht : t ∈ (M - T).map Prod.snd) :
    (((M - T).map Prod.snd).count t : ℝ) ≤
      lpEval (fun c => (c.count t : ℝ)) (fractionVector x) := by
  classical
  have hadd : (M - T).map Prod.snd + T.map Prod.snd = M.map Prod.snd := by
    rw [← Multiset.map_add, tsub_add_cancel_of_le hT]
  have hcount := congrArg (Multiset.count t) hadd
  rw [Multiset.count_add, hmax] at hcount
  have htM : t ∈ M.map Prod.snd := by
    rw [← hadd]
    exact Multiset.mem_add.mpr (Or.inl ht)
  have hcov : ((M.map Prod.snd).count t : ℝ) ≤
      lpEval (fun c => (c.count t : ℝ)) x :=
    hx.2.2 t (Multiset.mem_toFinset.mpr htM)
  by_cases h : (M.map Prod.snd).count t ≤ (principalConfigs x).join.count t
  · rw [min_eq_left h] at hcount
    have hz : ((M - T).map Prod.snd).count t = 0 := by omega
    rw [hz, Nat.cast_zero]
    unfold lpEval Finsupp.sum
    exact Finset.sum_nonneg (fun c _ =>
      mul_nonneg (fractionVector_nonneg x hx.2.1 c) (Nat.cast_nonneg _))
  · rw [min_eq_right (le_of_not_ge h)] at hcount
    have hr : (((M - T).map Prod.snd).count t : ℝ) +
        ((principalConfigs x).join.count t : ℝ) = ((M.map Prod.snd).count t : ℝ) := by
      exact_mod_cast hcount
    rw [principal_slots_count] at hr
    rw [fractionVector, lpEval_sub]
    linarith

theorem residual_lp_bounds (M T : Multiset (ℝ × ℝ)) (hT : T ≤ M)
    (hM : ∀ p ∈ M, 0 < p.1 ∧ p.1 ≤ p.2)
    (hB : IsInstance (M.map Prod.snd))
    (x : Multiset ℝ →₀ ℝ) (hx : IsLPFeasible (M.map Prod.snd) x)
    (hmax : ∀ s, (T.map Prod.snd).count s =
      min ((M.map Prod.snd).count s) ((principalConfigs x).join.count s)) :
    LIN ((M - T).map Prod.fst) + (principalCount x : ℝ) ≤ lpCost x ∧
      SIZE ((M - T).map Prod.fst) ≤ (x.support.card : ℝ) := by
  classical
  let R := (M - T).map Prod.snd
  let A := (M - T).map Prod.fst
  have hR : IsInstance R := by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp ht
    exact hB p.2 (Multiset.mem_map.mpr ⟨p, Multiset.mem_of_le (tsub_le_self) hp, rfl⟩)
  have hA : IsInstance A := by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp ht
    have hpM := Multiset.mem_of_le (tsub_le_self : M - T ≤ M) hp
    exact ⟨(hM p hpM).1, (hM p hpM).2.trans_lt
      (hB p.2 (Multiset.mem_map.mpr ⟨p, hpM, rfl⟩)).2⟩
  have hconf : ∀ c ∈ (fractionVector x).support, IsConfiguration (M.map Prod.snd) c :=
    fun c hc => hx.1 c (fractionVector_support x hc)
  obtain ⟨y, hy, hcosty⟩ := lp_restrict_types R (M.map Prod.snd) hB
    (fractionVector x) hconf (fractionVector_nonneg x hx.2.1)
    (residual_count_coverage M T hT x hx hmax)
  have hmatch : Multiset.Rel (· ≤ ·) A R := by
    apply Multiset.rel_map.mpr
    apply Multiset.rel_refl_of_refl_on
    intro p hp
    exact (hM p (Multiset.mem_of_le (tsub_le_self : M - T ≤ M) hp)).2
  obtain ⟨z, hz, hcostz⟩ := lp_transport hR ⟨R, le_rfl, hmatch⟩ hy
  have hzcost := hcostz.trans hcosty
  constructor
  · have hh := (lin_le_cost hz).trans hzcost
    rw [fractionVector_cost] at hh
    linarith
  · exact (lp_size_le_cost hA hz).trans (hzcost.trans (fractionVector_cost_le_support x))

end
end KKBinPacking.GeometricProof

end

/- Complete checked body: BasicSupport -/
section

namespace KKBinPacking.GeometricProof
open KKBinPacking.Shared

noncomputable section

theorem exists_small_coefficients {ι : Type*} [Fintype ι] (w u : ι → ℝ)
    (hw : ∀ i, 0 < w i) : ∃ δ : ℝ, 0 < δ ∧ ∀ i, |δ * u i| ≤ w i := by
  classical
  let S : ℝ := ∑ i, |u i| / w i
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => div_nonneg (abs_nonneg _) (hw i).le)
  have hden : 0 < 1 + S := by linarith
  refine ⟨1 / (1 + S), by positivity, ?_⟩
  intro i
  have hi : |u i| / w i ≤ S :=
    Finset.single_le_sum (fun j _ => div_nonneg (abs_nonneg _) (hw j).le) (Finset.mem_univ i)
  have hi' := (div_le_iff₀ (hw i)).mp hi
  rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (1 + S))]
  have he : 1 / (1 + S) * |u i| = |u i| / (1 + S) := by ring
  rw [he]
  apply (div_le_iff₀ hden).mpr
  nlinarith [hw i]

theorem basic_columns_independent {I : Multiset ℝ} {x : Multiset ℝ →₀ ℝ}
    (hx : IsBasicFeasible I x) :
    LinearIndependent ℝ (fun c : x.support => fun t : I.toFinset => (c.val.count t.val : ℝ)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha c
  have hw (b : x.support) : 0 < x b.val :=
    lt_of_le_of_ne (hx.1.2.1 b.val) (Ne.symm (Finsupp.mem_support_iff.mp b.property))
  obtain ⟨δ, hδ, hsmall⟩ := exists_small_coefficients (fun b : x.support => x b.val) a hw
  let e : x.support ↪ Multiset ℝ := ⟨Subtype.val, Subtype.val_injective⟩
  let z : x.support →₀ ℝ := Finsupp.equivFunOnFinite.symm (fun b => δ * a b)
  let y : Multiset ℝ →₀ ℝ := z.embDomain e
  have hys : y.support ⊆ x.support := by
    intro b hb
    rw [Finsupp.support_embDomain] at hb
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hb
    exact u.property
  have hyb (b : Multiset ℝ) : |y b| ≤ x b := by
    by_cases hb : b ∈ x.support
    · have he : y b = δ * a ⟨b, hb⟩ := Finsupp.embDomain_apply_self e z ⟨b, hb⟩
      rw [he]
      exact hsmall ⟨b, hb⟩
    · have he : y b = 0 := Finsupp.notMem_support_iff.mp (fun hy => hb (hys hy))
      rw [he, abs_zero]
      exact hx.1.2.1 b
  have hycount (t : ℝ) (ht : t ∈ I.toFinset) : lpEval (fun b => (b.count t : ℝ)) y = 0 := by
    have hpoint := congrFun ha ⟨t, ht⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hpoint
    change (z.embDomain e).sum (fun b w => w * (b.count t : ℝ)) = 0
    rw [Finsupp.sum_embDomain]
    change z.sum (fun b w => w * (b.val.count t : ℝ)) = 0
    rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
    change (∑ b : x.support, (δ * a b) * (b.val.count t : ℝ)) = 0
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, hpoint, mul_zero]
  have hplus : IsLPFeasible I (x + y) := by
    refine ⟨?_, ?_, ?_⟩
    · intro b hb
      have hm := Finsupp.support_add hb
      exact hx.1.1 b (Finset.mem_union.mp hm |>.elim id (fun hy => hys hy))
    · intro b
      change 0 ≤ x b + y b
      have hh := (abs_le.mp (hyb b)).1
      linarith
    · intro t ht
      change (I.count t : ℝ) ≤ lpEval (fun b => (b.count t : ℝ)) (x + y)
      rw [lpEval_add, hycount t ht, add_zero]
      exact hx.1.2.2 t ht
  have hminus : IsLPFeasible I (x - y) := by
    refine ⟨?_, ?_, ?_⟩
    · intro b hb
      have hm := Finsupp.support_sub hb
      exact hx.1.1 b (Finset.mem_union.mp hm |>.elim id (fun hy => hys hy))
    · intro b
      change 0 ≤ x b - y b
      exact sub_nonneg.mpr (abs_le.mp (hyb b)).2
    · intro t ht
      change (I.count t : ℝ) ≤ lpEval (fun b => (b.count t : ℝ)) (x - y)
      rw [lpEval_sub, hycount t ht, sub_zero]
      exact hx.1.2.2 t ht
  have he := congrArg (fun f : Multiset ℝ →₀ ℝ => f c.val) (hx.2 y hplus hminus)
  have hyc : y c.val = δ * a c := Finsupp.embDomain_apply_self e z c
  rw [hyc] at he
  exact (mul_eq_zero.mp he).resolve_left hδ.ne'

theorem basic_support_card_le {I : Multiset ℝ} {x : Multiset ℝ →₀ ℝ}
    (hx : IsBasicFeasible I x) : x.support.card ≤ I.toFinset.card := by
  classical
  have h := (basic_columns_independent hx).fintype_card_le_finrank
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using h

end
end KKBinPacking.GeometricProof

end

/- Complete checked body: TraceEstimates -/
section

set_option autoImplicit false
open KKBinPacking.GeometricGrouping KKBinPacking.Shared

namespace KKBinPacking.GeometricProof

noncomputable section

theorem trace_iteration_estimates {g : ℝ} {I : Multiset ℝ}
    (hI : IsInstance I) (tr : Alg2Trace 2 g I) (i : ℕ) (hi : i < tr.t) :
    LIN (tr.inst (i+1)) + (principalCount (tr.x i) : ℝ) ≤ LIN (tr.inst i) + 1 ∧
      2 * SIZE (tr.inst (i+1)) ≤ SIZE (tr.inst i) := by
  have hinst := trace_instance hI tr i hi.le
  have hb := residual_lp_bounds (geomPairs 2 (tr.inst i)) (tr.Bp i).join (tr.Bp_sub i hi)
    (fun p hp => ⟨(geom_pair_properties 2 (tr.inst i) hinst p hp).1,
      (geom_pair_properties 2 (tr.inst i) hinst p hp).2.1⟩)
    (geomJ_instance 2 (tr.inst i) hinst) (tr.x i) (tr.x_basic i hi).1 (tr.Bp_max i hi)
  rw [← tr.inst_succ i hi] at hb
  constructor
  · have hm := lin_mono_matching hinst (geomJ_matching 2 (tr.inst i))
    have hc := tr.x_cost i hi
    linarith
  · have hs := basic_support_card_le (tr.x_basic i hi)
    have hs' : ((tr.x i).support.card : ℝ) ≤ (numSizes (geomJ 2 (tr.inst i)) : ℝ) := by
      exact_mod_cast hs
    have hm := geomJ_numSizes_size 2 (tr.inst i) hinst
    norm_num only [Nat.cast_ofNat] at hm
    linarith [hb.2]

theorem trace_principal_sum {g : ℝ} {I : Multiset ℝ}
    (hI : IsInstance I) (tr : Alg2Trace 2 g I) :
    (∑ i ∈ Finset.range tr.t, (principalCount (tr.x i) : ℝ)) ≤ (OPT I : ℝ) + tr.t := by
  have htel : ∀ r ≤ tr.t,
      (∑ i ∈ Finset.range r, (principalCount (tr.x i) : ℝ)) + LIN (tr.inst r) ≤
        LIN (tr.inst 0) + r := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      intro hr
      have hh := ih (by omega)
      have hs := (trace_iteration_estimates hI tr r (by omega)).1
      rw [Finset.sum_range_succ]
      push_cast
      linarith
  have hstart : LIN (tr.inst 0) ≤ (OPT I : ℝ) := by
    rw [tr.inst_zero]
    exact (lin_mono_submultiset hI (Multiset.filter_le _ _)).trans (lin_le_opt I hI)
  have hend := lin_nonneg (tr.inst tr.t) (trace_instance hI tr tr.t le_rfl)
  linarith [htel tr.t le_rfl]

theorem trace_size_geometric {g : ℝ} {I : Multiset ℝ}
    (hI : IsInstance I) (tr : Alg2Trace 2 g I) :
    ∀ i ≤ tr.t, (2 : ℝ)^i * SIZE (tr.inst i) ≤ SIZE I := by
  intro i
  induction i with
  | zero =>
    intro _
    simp only [pow_zero, one_mul, tr.inst_zero]
    exact sum_le_of_submultiset (Multiset.filter_le _ _) (fun x hx => (hI x hx).1.le)
  | succ i ih =>
    intro hi
    have hh := ih (by omega)
    have hs := (trace_iteration_estimates hI tr i (by omega)).2
    have hsm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (2 : ℝ)^i)
    rw [pow_succ]
    nlinarith

theorem trace_iteration_count {I : Multiset ℝ} (hI : IsInstance I) (hS : 2 ≤ SIZE I)
    (tr : Alg2Trace 2 (1 / SIZE I) I) :
    (tr.t : ℝ) ≤ 1 + Real.logb 2 (SIZE I) := by
  have hS0 : 0 < SIZE I := by linarith
  have hlog : 0 ≤ Real.log (SIZE I) := Real.log_nonneg (by linarith)
  have hlogb : 0 ≤ Real.logb 2 (SIZE I) :=
    (Real.logb_nonneg_iff (by norm_num : (1 : ℝ) < 2) hS0).mpr (by linarith)
  by_cases ht : tr.t = 0
  · rw [ht, Nat.cast_zero]; linarith
  · have hi : tr.t-1 < tr.t := by omega
    have hloop := tr.loop_run (tr.t-1) hi
    have hn : (1 : ℝ) < SIZE (tr.inst (tr.t-1)) := by
      norm_num [alg2Threshold] at hloop
      linarith
    have hp := trace_size_geometric hI tr (tr.t-1) hi.le
    have hp0 : 0 < (2 : ℝ)^(tr.t-1) := by positivity
    have hpS : (2 : ℝ)^(tr.t-1) < SIZE I := by nlinarith
    have hlogs := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) hp0 hpS
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlogs
    have htcast : ((tr.t-1 : ℕ) : ℝ)+1 = tr.t := by
      exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ tr.t))
    linarith

theorem trace_step3_bound {I : Multiset ℝ} (hI : IsInstance I) (hS : 2 ≤ SIZE I)
    (tr : Alg2Trace 2 (1 / SIZE I) I) :
    ((alg2Step3Bins tr.t tr.Bp tr.PJ' tr.P3).card : ℝ) ≤
      (OPT I : ℝ) + (1 + Real.logb 2 (SIZE I)) * (9 + 4 * Real.log (SIZE I)) +
        2 + 4 * Real.log (SIZE I) := by
  have hsum := trace_principal_sum hI tr
  have hJ : (∑ i ∈ Finset.range tr.t, ((tr.PJ' i).card : ℝ)) ≤
      (tr.t : ℝ) * (8+4*Real.log (SIZE I)) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range tr.t, (8+4*Real.log (SIZE I)) := by
        apply Finset.sum_le_sum
        intro i hi
        have h := tr.PJ'_card i (Finset.mem_range.mp hi)
        norm_num at h
        linarith
      _ = _ := by simp [mul_add]
  have hP3 := tr.P3_card
  norm_num at hP3
  have ht := trace_iteration_count hI hS tr
  have hlog : 0 ≤ Real.log (SIZE I) := Real.log_nonneg (by linarith)
  have hmul := mul_le_mul_of_nonneg_right ht (by linarith : 0 ≤ 9+4*Real.log (SIZE I))
  rw [trace_step3_card]
  push_cast
  rw [Finset.sum_add_distrib]
  linarith

end
end KKBinPacking.GeometricProof

end

/- Complete checked body: AttributedOptUpper -/
section

namespace KKBinPacking.GeometricProof.AttributedOptUpper

-- Prove2me | solution 1 for KKBinPacking.GeometricGrouping.opt_le_two_size_add_one
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:05:45.497759+00:00
-- url     : https://prove2.me/submissions/b2060619-28e6-4011-af6a-d8026d7d5540

open KKBinPacking.GeometricGrouping

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

theorem opt_le_two_size_add_one_checked (I : Multiset ℝ) (hI : IsInstance I) :
    (OPT I : ℝ) ≤ 2 * SIZE I + 1 := by
  classical
  obtain ⟨P,hP,hcard⟩:=opt_attained I hI
  by_cases hzero : P=0
  · rw [← hcard,hzero]
    have hi : I=0 := by simpa [hzero] using hP.1.symm
    simp [hi,SIZE]
  obtain ⟨b,hb,hmin⟩:=Multiset.exists_min_image Multiset.sum hzero
  have hrest (c : Multiset ℝ) (hc : c ∈ P.erase b) : (1/2:ℝ) ≤ c.sum := by
    have hh:=optimal_bins_separate I P hP hcard b c hb hc
    have hm:=hmin c (Multiset.mem_of_mem_erase hc)
    linarith
  have hsum (Q : Multiset (Multiset ℝ)) : (∀ c ∈ Q,(1/2:ℝ) ≤ c.sum) →
      (Q.card : ℝ)/2 ≤ (Q.map Multiset.sum).sum := by
    induction Q using Multiset.induction_on with
    | empty => simp
    | @cons c Q ih =>
      intro h
      have hc:=h c (by simp)
      have hQ:=ih (fun a ha => h a (by simp [ha]))
      simp only [Multiset.map_cons,Multiset.sum_cons,Multiset.card_cons,Nat.cast_add,Nat.cast_one]
      linarith
  have hh:=hsum (P.erase b) hrest
  have hb0:=bin_nonneg I hI P hP b hb
  have he : P=b ::ₘ P.erase b := (Multiset.cons_erase hb).symm
  have hi : SIZE I=b.sum+((P.erase b).map Multiset.sum).sum := by
    calc
      SIZE I = P.join.sum := by rw [hP.1];rfl
      _ = (b ::ₘ P.erase b).join.sum := congrArg (fun Q : Multiset (Multiset ℝ) => Q.join.sum) he
      _ = _ := by rw [Multiset.join_cons,Multiset.sum_add,Multiset.sum_join]
  rw [← hcard,he,Multiset.card_cons,Nat.cast_add,Nat.cast_one,hi]
  linarith


end KKBinPacking.GeometricProof.AttributedOptUpper
end

/- Complete checked body: FinalAnyFit -/
section

namespace KKBinPacking.GeometricProof
open KKBinPacking.Shared KKBinPacking.GeometricGrouping

theorem final_anyFit_bound (I : Multiset ℝ) (hI : IsInstance I) (hS : 2 ≤ SIZE I)
    (P₀ P : Multiset (Multiset ℝ))
    (hP₀ : IsPacking (I.filter (fun x => 1 / SIZE I < x)) P₀)
    (hcard : (P₀.card : ℝ) ≤ (OPT I : ℝ) +
      (1 + Real.logb 2 (SIZE I)) * (9 + 4 * Real.log (SIZE I)) +
      2 + 4 * Real.log (SIZE I))
    (hinsert : AnyFit P₀ (I.filter (fun x => x ≤ 1 / SIZE I)) P) :
    IsPacking I P ∧ (P.card : ℝ) ≤ (OPT I : ℝ) +
      (1 + Real.logb 2 (OPT I)) * (9 + 4 * Real.log (OPT I)) +
      2 + 4 * Real.log (OPT I) := by
  have hS0 : 0 < SIZE I := by linarith
  have hSO := AttributedAnyFit.size_le_opt_checked I hI
  have hO1 : 1 ≤ (OPT I : ℝ) := by linarith
  have hLS : 0 ≤ Real.log (SIZE I) := Real.log_nonneg (by linarith)
  have hLO : 0 ≤ Real.log (OPT I) := Real.log_nonneg hO1
  have hBS : 0 ≤ Real.logb 2 (SIZE I) := Real.logb_nonneg (by norm_num) (by linarith)
  have hBO : 0 ≤ Real.logb 2 (OPT I) := Real.logb_nonneg (by norm_num) hO1
  have hlog : Real.log (SIZE I) ≤ Real.log (OPT I) := Real.log_le_log hS0 hSO
  have hbase : Real.logb 2 (SIZE I) ≤ Real.logb 2 (OPT I) :=
    Real.logb_le_logb_of_le (by norm_num) hS0 hSO
  have hprod : (1 + Real.logb 2 (SIZE I)) * (9 + 4 * Real.log (SIZE I)) ≤
      (1 + Real.logb 2 (OPT I)) * (9 + 4 * Real.log (OPT I)) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hcard' : (P₀.card : ℝ) ≤ (OPT I : ℝ) +
      (1 + Real.logb 2 (OPT I)) * (9 + 4 * Real.log (OPT I)) +
      2 + 4 * Real.log (OPT I) := by linarith
  have hg0 : 0 < 2 / SIZE I := div_pos (by norm_num) hS0
  have hg1 : 2 / SIZE I ≤ 1 := (div_le_one₀ hS0).mpr hS
  have hhalf : (2 / SIZE I) / 2 = 1 / SIZE I := by ring
  have hbound := AttributedAnyFit.anyFit_card_le_checked I hI (2 / SIZE I) hg0 hg1 P₀
    (by simpa only [hhalf] using hP₀) P (by simpa only [hhalf] using hinsert)
  have hupper := AttributedOptUpper.opt_le_two_size_add_one_checked I hI
  have hmul := mul_le_mul_of_nonneg_left hupper hg0.le
  have hcancel : (2 / SIZE I) * SIZE I = 2 := div_mul_cancel₀ _ hS0.ne'
  have halt : (1 + 2 / SIZE I) * (OPT I : ℝ) + 1 ≤ (OPT I : ℝ) + 6 := by
    nlinarith
  have herr : (OPT I : ℝ) + 6 ≤ (OPT I : ℝ) +
      (1 + Real.logb 2 (OPT I)) * (9 + 4 * Real.log (OPT I)) +
      2 + 4 * Real.log (OPT I) := by
    nlinarith [mul_nonneg hBO hLO]
  refine ⟨?_, hbound.trans (max_le hcard' (halt.trans herr))⟩
  refine ⟨?_, AttributedAnyFit.anyFit_capacity_checked _ _ _ hinsert hP₀.2 ?_⟩
  · rw [AttributedAnyFit.anyFit_join_checked _ _ _ hinsert, hP₀.1]
    simpa only [not_lt] using Multiset.filter_add_not (fun x => 1 / SIZE I < x) I
  · intro p hp
    exact (hI p (Multiset.mem_filter.mp hp).1).2.le

end KKBinPacking.GeometricProof

end

/- Complete checked body: BinPackingRoot -/
section

namespace KKBinPacking.GeometricGrouping
theorem algorithm2_log_squared_bound (I : Multiset ℝ) (hI : IsInstance I) (hS : 2 ≤ SIZE I)
    (P : Multiset (Multiset ℝ)) (hP : Alg2Run 2 (1 / SIZE I) I P) :
    IsPacking I P ∧
      (Multiset.card P : ℝ) ≤
        (OPT I : ℝ) + (1 + Real.logb 2 (OPT I)) * (9 + 4 * Real.log (OPT I)) +
          2 + 4 * Real.log (OPT I) := by
  obtain ⟨tr, rfl⟩ := hP
  exact KKBinPacking.GeometricProof.final_anyFit_bound I hI hS
    (alg2Step3Bins tr.t tr.Bp tr.PJ' tr.P3) tr.P
    (KKBinPacking.GeometricProof.trace_step3_packing hI tr)
    (KKBinPacking.GeometricProof.trace_step3_bound hI hS tr) tr.P_insert
end KKBinPacking.GeometricGrouping

end

open KKBinPacking.Shared KKBinPacking.GeometricGrouping

theorem solution (I : Multiset ℝ) (hI : IsInstance I) (hS : 2 ≤ SIZE I)
    (P : Multiset (Multiset ℝ)) (hP : Alg2Run 2 (1 / SIZE I) I P) :
    IsPacking I P ∧
      (Multiset.card P : ℝ) ≤
        (OPT I : ℝ) + (1 + Real.logb 2 (OPT I)) * (9 + 4 * Real.log (OPT I)) +
          2 + 4 * Real.log (OPT I) := by
  exact KKBinPacking.GeometricGrouping.algorithm2_log_squared_bound I hI hS P hP

#print axioms KKBinPacking.GeometricGrouping.algorithm2_log_squared_bound
#print axioms solution
