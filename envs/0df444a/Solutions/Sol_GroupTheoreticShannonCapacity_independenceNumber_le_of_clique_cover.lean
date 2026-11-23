-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.independenceNumber_le_of_clique_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:37:15.156795+00:00
-- url     : https://prove2.me/submissions/a96ae2b6-ea93-40ac-a467-f7271f6fb4b4

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic

set_option autoImplicit true
open GroupTheoreticShannonCapacity
namespace GroupTheoreticShannonCapacity
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (cliques : Finset (Finset V)) (weights : Finset V → ℝ)
    (hclique : ∀ C ∈ cliques, G.IsClique C)
    (hpos : ∀ C ∈ cliques, weights C ≥ 0)
    (hcover : ∀ v : V, (cliques.filter (v ∈ ·)).sum weights ≥ 1)
    (W : ℝ) (hW : cliques.sum weights ≤ W) :
    (G.indepNum : ℝ) ≤ W := by
  classical
  by_cases hW_pos : W < 0
  · -- If W < 0, then cliques.sum weights < 0, but sum of non-negative is ≥ 0
    have hsum_nonneg : 0 ≤ cliques.sum weights := Finset.sum_nonneg (fun C hC => hpos C hC)
    linarith
  push_neg at hW_pos
  obtain ⟨S, hSmax⟩ := SimpleGraph.maximumIndepSet_exists (G := G)
  have hS_indep : G.IsIndepSet (S : Set V) :=
    (SimpleGraph.isMaximumIndepSet_iff G S).1 hSmax |>.1
  -- Each clique contains at most 1 element of S
  have hone : ∀ C ∈ cliques, (S.filter (· ∈ C)).card ≤ 1 := by
    intro C hC
    by_contra h
    push_neg at h
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h
    rw [Finset.mem_filter] at hu hv
    -- u, v ∈ S with u ≠ v, so ¬G.Adj u v
    have hpair := (SimpleGraph.isIndepSet_iff G).1 hS_indep
    have hnadj := hpair (by simpa using hu.1) (by simpa using hv.1) huv
    -- But u, v ∈ C which is a clique, so G.Adj u v (contradiction)
    have hadj := hclique C hC hu.2 hv.2 huv
    exact hnadj hadj
  -- Counting argument:
  -- ∑_{v ∈ S} ∑_{C : v ∈ C} weight(C) ≥ |S| (each vertex covered with weight ≥ 1)
  have hleft : (S.card : ℝ) ≤ S.sum (fun v => (cliques.filter (v ∈ ·)).sum weights) := by
    calc (S.card : ℝ) = S.sum (fun _ => (1 : ℝ)) := by simp
      _ ≤ S.sum (fun v => (cliques.filter (v ∈ ·)).sum weights) := by
          apply Finset.sum_le_sum
          intro v _
          exact hcover v
  -- ∑_{v ∈ S} ∑_{C : v ∈ C} weight(C) = ∑_{C} weight(C) × |S ∩ C| ≤ W
  have hright : S.sum (fun v => (cliques.filter (v ∈ ·)).sum weights) ≤ W := by
    -- Swap the order of summation
    calc S.sum (fun v => (cliques.filter (v ∈ ·)).sum weights)
        = S.sum (fun v => cliques.sum (fun C => if v ∈ C then weights C else 0)) := by
            congr 1; ext v; exact Finset.sum_filter _ _
      _ = cliques.sum (fun C => S.sum (fun v => if v ∈ C then weights C else 0)) := by
            rw [Finset.sum_comm]
      _ = cliques.sum (fun C => weights C * (S.filter (· ∈ C)).card) := by
            congr 1; ext C
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ cliques.sum (fun C => weights C * 1) := by
            apply Finset.sum_le_sum
            intro C hC
            apply mul_le_mul_of_nonneg_left _ (hpos C hC)
            exact_mod_cast hone C hC
      _ = cliques.sum weights := by simp
      _ ≤ W := hW
  have hS_card : S.card = G.indepNum := by
    simpa using
      (SimpleGraph.maximumIndepSet_card_eq_indepNum (G := G) S hSmax)
  have hS_le : (S.card : ℝ) ≤ W := le_trans hleft hright
  simpa [hS_card] using hS_le
end GroupTheoreticShannonCapacity
