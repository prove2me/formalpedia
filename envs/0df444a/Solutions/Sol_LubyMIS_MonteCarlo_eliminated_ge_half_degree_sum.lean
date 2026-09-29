-- Prove2me | solution 1 for LubyMIS.MonteCarlo.eliminated_ge_half_degree_sum
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:21:47.581555+00:00
-- url     : https://prove2.me/submissions/8a110c96-41a1-45d6-939f-055aa0ffea81

import Mathlib
import Definitions.Def_LubyMIS_MonteCarlo_Basic

namespace LubyMIS.MonteCarlo

open Finset

theorem aux_eghd_key {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (Y : Finset V) :
    ∑ i ∈ Y, H.degree i ≤ 2 * (H.edgeFinset.filter (fun e => ∃ v ∈ e, v ∈ Y)).card := by
  classical
  have h1 : ∑ i ∈ Y, H.degree i
      = ∑ e ∈ H.edgeFinset, (Y.filter (fun i => i ∈ e)).card := by
    calc ∑ i ∈ Y, H.degree i
        = ∑ i ∈ Y, ∑ e ∈ H.edgeFinset, (if i ∈ e then 1 else 0) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← H.card_incidenceFinset_eq_degree i, H.incidenceFinset_eq_filter i,
            Finset.card_filter]
      _ = ∑ e ∈ H.edgeFinset, ∑ i ∈ Y, (if i ∈ e then 1 else 0) := Finset.sum_comm
      _ = ∑ e ∈ H.edgeFinset, (Y.filter (fun i => i ∈ e)).card := by
          refine Finset.sum_congr rfl (fun e _ => ?_)
          rw [Finset.card_filter]
  rw [h1, Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_le_sum (fun e _ => ?_)
  split_ifs with h
  · induction e using Sym2.ind with
    | h a b =>
      have hsub : Y.filter (fun i => i ∈ s(a, b)) ⊆ {a, b} := by
        intro x hx
        simp only [Finset.mem_filter, Sym2.mem_iff] at hx
        rcases hx.2 with rfl | rfl <;> simp
      calc (Y.filter (fun i => i ∈ s(a, b))).card ≤ ({a, b} : Finset V).card :=
            Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
        _ = 2 * 1 := by norm_num
  · simp only [mul_zero, Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx hxe
    exact h ⟨x, hxe, hx⟩

theorem aux_eghd_real {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (I : Finset V) :
    1 / 2 * ∑ i, (H.degree i : ℝ) * (if i ∈ I ∪ nbhd H I then (1 : ℝ) else 0)
      ≤ (eliminated H I : ℝ) := by
  have hk := aux_eghd_key H (I ∪ nbhd H I)
  have hk' : ((∑ i ∈ I ∪ nbhd H I, H.degree i : ℕ) : ℝ) ≤ 2 * (eliminated H I : ℝ) := by
    unfold eliminated
    exact_mod_cast (by convert hk using 3)
  have hs : ∑ i, (H.degree i : ℝ) * (if i ∈ I ∪ nbhd H I then (1 : ℝ) else 0)
      = ((∑ i ∈ I ∪ nbhd H I, H.degree i : ℕ) : ℝ) := by
    push_cast
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hs]
  linarith

end LubyMIS.MonteCarlo

open LubyMIS.MonteCarlo

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (hw0 : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1) (S : Ω → Finset V) :
    (∑ ω, w ω * (eliminated H (S ω) : ℝ)) ≥
        1 / 2 * ∑ i, (H.degree i : ℝ) * (∑ ω, if i ∈ S ω ∪ nbhd H (S ω) then w ω else 0) ∧
      1 / 2 * ∑ i, (H.degree i : ℝ) * (∑ ω, if i ∈ S ω ∪ nbhd H (S ω) then w ω else 0) ≥
        1 / 2 * ∑ i, (H.degree i : ℝ) * (∑ ω, if i ∈ nbhd H (S ω) then w ω else 0) := by
  constructor
  · have e : 1 / 2 * ∑ i, (H.degree i : ℝ) * (∑ ω, if i ∈ S ω ∪ nbhd H (S ω) then w ω else 0)
        = ∑ ω, w ω * (1 / 2 * ∑ i, (H.degree i : ℝ) *
            (if i ∈ S ω ∪ nbhd H (S ω) then (1 : ℝ) else 0)) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun ω _ => Finset.sum_congr rfl (fun i _ => ?_))
      split_ifs <;> ring
    rw [ge_iff_le, e]
    exact Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (aux_eghd_real H (S ω)) (hw0 ω))
  · rw [ge_iff_le]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    refine Finset.sum_le_sum (fun ω _ => ?_)
    by_cases h : i ∈ nbhd H (S ω)
    · have : i ∈ S ω ∪ nbhd H (S ω) := Finset.mem_union_right _ h
      simp [h, this]
    · rw [if_neg h]
      split_ifs
      · exact hw0 ω
      · exact le_rfl
