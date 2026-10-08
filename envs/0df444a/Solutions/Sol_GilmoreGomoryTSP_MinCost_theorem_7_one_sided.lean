-- Prove2me | solution 1 for GilmoreGomoryTSP.MinCost.theorem_7_one_sided
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T05:02:54.750981+00:00
-- url     : https://prove2.me/submissions/12fd0af9-11d1-4c3a-9d6b-a6e4ab9b9391

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model

set_option autoImplicit false

open MeasureTheory in
theorem GG7_ii {f : ℝ → ℝ} (hf : LocallyIntegrable f) (x y : ℝ) :
    IntervalIntegrable f volume x y :=
  intervalIntegrable_iff.mpr <|
    (hf.integrableOn_isCompact isCompact_uIcc).mono_set Set.uIoc_subset_uIcc

open MeasureTheory GilmoreGomoryTSP.MinCost in
theorem GG7_c_eq {n : ℕ} (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) :
    c f g A B i j = c (fun x => f x + g x) (fun _ => 0) A B i j
      + ((∫ x in (0:ℝ)..B i, g x) - ∫ x in (0:ℝ)..A j, g x) := by
  have key : ((∫ x in (0:ℝ)..B i, g x) - ∫ x in (0:ℝ)..A j, g x) = ∫ x in A j..B i, g x :=
    intervalIntegral.integral_interval_sub_left (GG7_ii hg _ _) (GG7_ii hg _ _)
  rw [key]
  unfold c
  split_ifs with h
  · rw [intervalIntegral.integral_add (GG7_ii hf _ _) (GG7_ii hg _ _),
      intervalIntegral.integral_symm (B i) (A j)]
    ring
  · simp

open MeasureTheory GilmoreGomoryTSP.MinCost in
theorem GG7_cost_eq {n : ℕ} (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1))) :
    cost f g A B ψ = cost (fun x => f x + g x) (fun _ => 0) A B ψ
      + ((∑ i, ∫ x in (0:ℝ)..B i, g x) - ∑ i, ∫ x in (0:ℝ)..A i, g x) := by
  unfold cost
  simp_rw [GG7_c_eq f g hf hg A B]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Equiv.sum_comp ψ (fun j => ∫ x in (0:ℝ)..A j, g x)]


open GilmoreGomoryTSP.MinCost in
theorem solution {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ)
    (ψs : Equiv.Perm (Fin (n + 1))) (hψs : IsTour ψs)
    (hmin : ∀ ψ : Equiv.Perm (Fin (n + 1)), IsTour ψ → cost f g A B ψs ≤ cost f g A B ψ) :
    ∀ ψ : Equiv.Perm (Fin (n + 1)), IsTour ψ →
      cost (fun x => f x + g x) (fun _ => 0) A B ψs ≤
        cost (fun x => f x + g x) (fun _ => 0) A B ψ := by
  intro ψ hψ
  have h := hmin ψ hψ
  rw [GG7_cost_eq f g hf hg A B ψs, GG7_cost_eq f g hf hg A B ψ] at h
  linarith
