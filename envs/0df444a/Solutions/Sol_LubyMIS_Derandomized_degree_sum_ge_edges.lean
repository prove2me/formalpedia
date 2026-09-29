-- Prove2me | solution 1 for LubyMIS.Derandomized.degree_sum_ge_edges
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:40:34.896418+00:00
-- url     : https://prove2.me/submissions/7bdef22c-49d8-457f-b981-6934f618dbb9

import Mathlib
import Definitions.Def_LubyMIS_Derandomized_Basic

namespace LubyMIS.Derandomized

/-- Dart weight: a low vertex `i` gives `d(i)/(2 d(j))` to the dart `(i,j)`, a high vertex gives `1`. -/
noncomputable def aux_dse_w {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (i j : V) : ℝ :=
  if sumInv H i ≤ 2 then (H.degree i : ℝ) / (2 * (H.degree j : ℝ)) else 1

lemma aux_dse_pair {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (i j : V)
    (h : H.Adj i j) : 1 ≤ aux_dse_w H i j + aux_dse_w H j i := by
  have hi : (0:ℝ) < H.degree i := by
    exact_mod_cast (H.degree_pos_iff_exists_adj i).mpr ⟨j, h⟩
  have hj : (0:ℝ) < H.degree j := by
    exact_mod_cast (H.degree_pos_iff_exists_adj j).mpr ⟨i, h.symm⟩
  unfold aux_dse_w
  split_ifs with h1 h2 h2
  · rw [div_add_div _ _ (by positivity) (by positivity), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg ((H.degree i : ℝ) - H.degree j)]
  · have : 0 ≤ (H.degree i : ℝ) / (2 * H.degree j) := by positivity
    linarith
  · have : 0 ≤ (H.degree j : ℝ) / (2 * H.degree i) := by positivity
    linarith
  · linarith

lemma aux_dse_row {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (i : V) :
    (if sumInv H i ≤ 2 then (H.degree i : ℝ) * sumInv H i / 2 else (H.degree i : ℝ)) =
      ∑ j, if H.Adj i j then aux_dse_w H i j else 0 := by
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun j => H.Adj i j) = H.neighborFinset i := by
    ext j; simp
  rw [hf]
  unfold aux_dse_w
  split_ifs with h
  · unfold sumInv
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simp [SimpleGraph.card_neighborFinset_eq_degree]

end LubyMIS.Derandomized

open LubyMIS.Derandomized

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    (∑ i ∈ Finset.univ.filter (fun i => sumInv H i ≤ 2), (H.degree i : ℝ) * sumInv H i / 2) +
        (∑ i ∈ Finset.univ.filter (fun i => 2 < sumInv H i), (H.degree i : ℝ)) ≥
      (H.edgeFinset.card : ℝ) := by
  set f : V → V → ℝ := fun i j => if H.Adj i j then aux_dse_w H i j else 0 with hfdef
  have hL : (∑ i ∈ Finset.univ.filter (fun i => sumInv H i ≤ 2),
        (H.degree i : ℝ) * sumInv H i / 2) +
        (∑ i ∈ Finset.univ.filter (fun i => 2 < sumInv H i), (H.degree i : ℝ)) =
      ∑ i, ∑ j, f i j := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hfdef, ← aux_dse_row]
    by_cases h1 : sumInv H i ≤ 2
    · have h2 : ¬ (2 < sumInv H i) := not_lt.mpr h1
      simp [h1, h2]
    · have h2 : 2 < sumInv H i := lt_of_not_ge h1
      simp [h1, h2]
  have hcomm : ∑ i, ∑ j, f j i = ∑ i, ∑ j, f i j := Finset.sum_comm
  have hdeg : ∀ i, ∑ j, (if H.Adj i j then (1:ℝ) else 0) = (H.degree i : ℝ) := by
    intro i
    rw [Finset.sum_boole]
    have hf : Finset.univ.filter (fun j => H.Adj i j) = H.neighborFinset i := by
      ext j; simp
    rw [hf, SimpleGraph.card_neighborFinset_eq_degree]
  have hpt : ∀ i j, (if H.Adj i j then (1:ℝ) else 0) ≤ f i j + f j i := by
    intro i j
    by_cases h : H.Adj i j
    · simp only [hfdef, h, h.symm, if_true]
      exact aux_dse_pair H i j h
    · have h' : ¬ H.Adj j i := fun h' => h h'.symm
      simp [hfdef, h, h']
  have hsum : ∑ i, (H.degree i : ℝ) ≤ ∑ i, ∑ j, (f i j + f j i) := by
    apply Finset.sum_le_sum
    intro i _
    rw [← hdeg i]
    apply Finset.sum_le_sum
    intro j _
    exact hpt i j
  have htwice : (∑ i, (H.degree i : ℝ)) = 2 * (H.edgeFinset.card : ℝ) := by
    exact_mod_cast H.sum_degrees_eq_twice_card_edges
  have hsplit : ∑ i, ∑ j, (f i j + f j i) = ∑ i, ∑ j, f i j + ∑ i, ∑ j, f j i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_add_distrib]
  rw [hL]
  linarith
