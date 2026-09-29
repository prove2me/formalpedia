-- Prove2me | solution 1 for LubyMIS.MonteCarlo.degree_sum_ge_edges
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:31:14.98722+00:00
-- url     : https://prove2.me/submissions/a77e3d2d-63ce-44e8-b8ad-baeb63191abe

import Mathlib
import Definitions.Def_LubyMIS_MonteCarlo_Basic

namespace LubyMIS.MonteCarlo

/-- Per-dart charge: vertex `i` charges `d(i)/(2 d(j))` to the dart `(i, j)` if `sum(i) ≤ 2`,
and `1` otherwise. -/
noncomputable def aux_lmcdeg_h {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (i j : V) : ℝ :=
  if sumInv H i ≤ 2 then (H.degree i : ℝ) / (2 * (H.degree j : ℝ)) else 1

theorem aux_lmcdeg_f_eq {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (i : V) :
    (if sumInv H i ≤ 2 then (H.degree i : ℝ) * sumInv H i / 2 else (H.degree i : ℝ)) =
      ∑ j ∈ H.neighborFinset i, aux_lmcdeg_h H i j := by
  unfold aux_lmcdeg_h
  split_ifs with hs
  · unfold sumInv
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  · simp [SimpleGraph.card_neighborFinset_eq_degree]

theorem aux_lmcdeg_pair {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (i j : V) (hij : H.Adj i j) : 1 ≤ aux_lmcdeg_h H i j + aux_lmcdeg_h H j i := by
  have hi : (0:ℝ) < H.degree i := by
    exact_mod_cast (H.degree_pos_iff_exists_adj i).mpr ⟨j, hij⟩
  have hj : (0:ℝ) < H.degree j := by
    exact_mod_cast (H.degree_pos_iff_exists_adj j).mpr ⟨i, hij.symm⟩
  unfold aux_lmcdeg_h
  split_ifs with h1 h2 h2
  · rw [div_add_div _ _ (by positivity) (by positivity), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg ((H.degree i : ℝ) - H.degree j)]
  · have : (0:ℝ) ≤ (H.degree i : ℝ) / (2 * (H.degree j : ℝ)) := by positivity
    linarith
  · have : (0:ℝ) ≤ (H.degree j : ℝ) / (2 * (H.degree i : ℝ)) := by positivity
    linarith
  · norm_num

end LubyMIS.MonteCarlo

open LubyMIS.MonteCarlo

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    (∑ i ∈ Finset.univ.filter (fun i => sumInv H i ≤ 2), (H.degree i : ℝ) * sumInv H i / 2) +
        (∑ i ∈ Finset.univ.filter (fun i => 2 < sumInv H i), (H.degree i : ℝ)) ≥
      (H.edgeFinset.card : ℝ) := by
  have hL : (∑ i ∈ Finset.univ.filter (fun i => sumInv H i ≤ 2),
        (H.degree i : ℝ) * sumInv H i / 2) +
        (∑ i ∈ Finset.univ.filter (fun i => 2 < sumInv H i), (H.degree i : ℝ)) =
      ∑ i, ∑ j ∈ H.neighborFinset i, aux_lmcdeg_h H i j := by
    rw [show (∑ i, ∑ j ∈ H.neighborFinset i, aux_lmcdeg_h H i j) =
        ∑ i, (if sumInv H i ≤ 2 then (H.degree i : ℝ) * sumInv H i / 2
          else (H.degree i : ℝ)) from
        Finset.sum_congr rfl (fun i _ => (aux_lmcdeg_f_eq H i).symm)]
    rw [Finset.sum_ite]
    congr 1
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext i
    simp [not_le]
  have hE : 2 * (H.edgeFinset.card : ℝ) = ∑ i, ∑ j ∈ H.neighborFinset i, (1:ℝ) := by
    have := H.sum_degrees_eq_twice_card_edges
    simp only [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul,
      mul_one]
    exact_mod_cast this.symm
  have hsym : ∑ i, ∑ j ∈ H.neighborFinset i, aux_lmcdeg_h H i j =
      ∑ i, ∑ j ∈ H.neighborFinset i, aux_lmcdeg_h H j i := by
    simp only [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    simp [H.adj_comm]
  have hmain : ∑ i, ∑ j ∈ H.neighborFinset i, (1:ℝ) ≤
      ∑ i, ∑ j ∈ H.neighborFinset i, (aux_lmcdeg_h H i j + aux_lmcdeg_h H j i) := by
    refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j hj => ?_))
    exact aux_lmcdeg_pair H i j ((H.mem_neighborFinset i j).mp hj)
  simp only [Finset.sum_add_distrib] at hmain
  rw [ge_iff_le, hL]
  linarith
