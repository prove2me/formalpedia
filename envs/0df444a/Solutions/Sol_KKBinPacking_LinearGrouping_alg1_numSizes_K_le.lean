-- Prove2me | solution 1 for KKBinPacking.LinearGrouping.alg1_numSizes_K_le
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:35:45.089145+00:00
-- url     : https://prove2.me/submissions/e3ab2fc3-6126-4a06-88e4-c6ec6887f445

import Definitions.Def_KKBinPacking_LinearGrouping_Algorithm1
open KKBinPacking.LinearGrouping KKBinPacking.Shared

private theorem chunks_go_bound {α : Type*} (k : ℕ) (xs : List α)
    (a : Array α) (b : Array (List α)) :
    k*((List.toChunks.go k xs a b).length-1) ≤ k*b.size+a.size+xs.length := by
  induction xs generalizing a b with
  | nil => simp [List.toChunks.go]
  | cons x xs ih =>
    rw [List.toChunks.go]
    split
    · rename_i ha
      have hae : a.size=k := by simpa using ha
      have hh:=ih ((Array.mkEmpty k).push x) (b.push a.toList)
      simp only [Array.size_push,List.length_cons] at hh ⊢
      have he0 : (Array.mkEmpty k : Array α).size=0 := rfl
      rw [he0] at hh
      rw [hae]
      simpa [Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    · have hh:=ih (a.push x) b
      simpa only [Array.size_push,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

private theorem chunks_bound {α : Type*} (k : ℕ) (xs : List α) :
    k*((xs.toChunks k).length-1) ≤ xs.length := by
  cases xs with
  | nil => simp [List.toChunks]
  | cons x xs =>
    cases k with
    | zero => simp
    | succ k =>
      have hh:=chunks_go_bound (k+1) xs #[x] #[]
      simpa [List.toChunks,Nat.add_comm] using hh

private theorem round_groups_sizes (gs : List (List ℝ)) :
    numSizes (gs.map roundUpGroup).sum ≤ gs.length := by
  classical
  induction gs with
  | nil => simp [numSizes]
  | cons g gs ih =>
    have hg : numSizes (roundUpGroup g) ≤ 1 := by
      by_cases hh : g.length=0 <;> simp [numSizes,roundUpGroup,Multiset.toFinset_replicate,hh]
    simp only [List.map_cons,List.sum_cons,List.length_cons,numSizes,Multiset.toFinset_add] at ⊢
    have hh:=Finset.card_union_le (roundUpGroup g).toFinset ((gs.map roundUpGroup).sum).toFinset
    change (roundUpGroup g).toFinset.card ≤ 1 at hg
    change ((gs.map roundUpGroup).sum).toFinset.card ≤ gs.length at ih
    omega

theorem solution (ε : ℝ) (hε : 0 < ε) (I : Multiset ℝ) (hI : IsInstance I) :
    (numSizes (alg1K ε I) : ℝ) ≤ 1 / ε ^ 2 := by
  let n:=(alg1J ε I).card
  let k:=alg1k ε I
  let L:=(alg1J ε I).sort (· ≥ ·)
  let r:=(L.toChunks k).length-1
  by_cases hn : n=0
  · have hz : alg1J ε I=0 := Multiset.card_eq_zero.mp hn
    simp only [alg1K,linGroup,linGroups,hz,Multiset.sort_zero,List.toChunks,List.drop_nil,
      List.map_nil,List.sum_nil,numSizes,Multiset.toFinset_zero,Finset.card_empty,Nat.cast_zero]
    positivity
  have hnpos : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnr : numSizes (alg1K ε I) ≤ r := by
    exact (round_groups_sizes ((L.toChunks k).drop 1)).trans_eq (List.length_drop)
  have hrn : (r:ℝ)*(k:ℝ) ≤ (n:ℝ) := by
    have hh:=chunks_bound k L
    have hlen : L.length=n := Multiset.length_sort _
    rw [hlen] at hh
    change k*r ≤ n at hh
    exact_mod_cast (by simpa only [Nat.mul_comm] using hh : r*k ≤ n)
  have hceil : (n:ℝ)*ε^2 ≤ (k:ℝ) := Nat.le_ceil _
  have hrε : (r:ℝ)*ε^2 ≤ 1 := by
    apply (mul_le_mul_iff_left₀ hnpos).mp
    calc
      ((r:ℝ)*ε^2)*(n:ℝ) = (r:ℝ)*((n:ℝ)*ε^2) := by ring
      _ ≤ (r:ℝ)*(k:ℝ) := mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg _)
      _ ≤ (n:ℝ) := hrn
      _ = 1*(n:ℝ) := by ring
  exact (Nat.cast_le.mpr hnr).trans ((le_div_iff₀ (sq_pos_of_pos hε)).mpr hrε)
