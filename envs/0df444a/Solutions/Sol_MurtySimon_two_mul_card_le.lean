-- Prove2me | solution 1 for MurtySimon.two_mul_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:20:39.511919+00:00
-- url     : https://prove2.me/submissions/a317b1b4-5d48-4af7-b9a2-0a2810f4d7db

module
public import Definitions.Def_MurtySimon_Equality
public import Definitions.Def_MurtySimon_Main
public import Theorems.Thm_MurtySimon_IsMid_symm
public import Theorems.Thm_MurtySimon_OnPath_mem_edgeSet
public import Theorems.Thm_MurtySimon_OnPath_ne


set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
namespace MurtySimon
theorem _root_.solution {M : Finset (Sym2 V)} (hM : IsEdgeMatching G M) :
    2 * #M ≤ Fintype.card V := by
  classical
  have hcard : ∀ e ∈ M, #(univ.filter (· ∈ e)) = 2 := by
    intro e he
    have hne := hM.1 e he
    induction e using Sym2.ind with
    | h a b =>
      rw [mem_edgeSet] at hne
      have : univ.filter (· ∈ s(a, b)) = {a, b} := by
        ext v; simp [Sym2.mem_iff]
      rw [this, card_pair hne.ne]
  have hdisj : (M : Set (Sym2 V)).PairwiseDisjoint fun e => univ.filter (· ∈ e) := by
    intro e he f hf hef
    rw [Function.onFun, Finset.disjoint_left]
    intro v hv hv'
    exact hM.2 e he f hf hef v (mem_filter.1 hv).2 (mem_filter.1 hv').2
  calc 2 * #M = ∑ e ∈ M, #(univ.filter (· ∈ e)) := by
        rw [sum_congr rfl hcard, sum_const, smul_eq_mul, mul_comm]
    _ = #(M.biUnion fun e => univ.filter (· ∈ e)) := (card_biUnion hdisj).symm
    _ ≤ #(univ : Finset V) := card_le_univ _
    _ = Fintype.card V := card_univ
end MurtySimon
