-- Prove2me | solution 1 for GeometryOfGraphs.FlowCut.weak_duality_cut
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:32:46.771977+00:00
-- url     : https://prove2.me/submissions/1bd275fa-f652-44cd-8b51-a4f46d19db4d

import Mathlib
import Definitions.Def_GeometryOfGraphs_FlowCut_Network
import Definitions.Def_GeometryOfGraphs_FlowCut_Maxflow

set_option autoImplicit false
open GeometryOfGraphs.FlowCut

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (N : Network V)
    (f : Fin N.k → V → V → ℝ) (lam : ℝ) (hlam : 0 ≤ lam) (hf : N.IsFeasibleFlow f lam)
    (S : Finset V) :
    lam * N.Dem S ≤ N.Cap S := by
  obtain ⟨hf0, hcons, hcap⟩ := hf
  have hnet : ∀ μ, ∑ i ∈ S, ∑ j ∈ Sᶜ, (f μ i j - f μ j i) =
      lam * N.D μ * ((if N.s μ ∈ S then 1 else 0) - (if N.t μ ∈ S then 1 else 0)) := by
    intro μ
    have h1 : ∑ v ∈ S, (∑ j, f μ v j - ∑ j, f μ j v) =
        lam * N.D μ * ((if N.s μ ∈ S then 1 else 0) - (if N.t μ ∈ S then 1 else 0)) := by
      rw [Finset.sum_congr rfl (fun v _ => hcons μ v)]
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      simp [Finset.sum_ite_eq']
    have h2 : ∑ v ∈ S, (∑ j, f μ v j - ∑ j, f μ j v) =
        ∑ i ∈ S, ∑ j ∈ Sᶜ, (f μ i j - f μ j i) := by
      have a1 : ∀ v : V, ∑ j, f μ v j = ∑ j ∈ S, f μ v j + ∑ j ∈ Sᶜ, f μ v j := fun v =>
        (Finset.sum_add_sum_compl S (fun j => f μ v j)).symm
      have a2 : ∀ v : V, ∑ j, f μ j v = ∑ j ∈ S, f μ j v + ∑ j ∈ Sᶜ, f μ j v := fun v =>
        (Finset.sum_add_sum_compl S (fun j => f μ j v)).symm
      have a3 : ∑ v ∈ S, ∑ j ∈ S, f μ v j = ∑ v ∈ S, ∑ j ∈ S, f μ j v := Finset.sum_comm
      simp only [a1, a2, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      linarith
    rw [← h2, h1]
  have hper : ∀ μ, (if (N.s μ ∈ S ∧ N.t μ ∉ S) ∨ (N.s μ ∉ S ∧ N.t μ ∈ S) then lam * N.D μ else 0)
      ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, (f μ i j + f μ j i) := by
    intro μ
    have hY1 : ∑ i ∈ S, ∑ j ∈ Sᶜ, (f μ i j - f μ j i) ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, (f μ i j + f μ j i) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => by linarith [hf0 μ j i]))
    have hY2 : -∑ i ∈ S, ∑ j ∈ Sᶜ, (f μ i j - f μ j i) ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, (f μ i j + f μ j i) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum (fun j _ => by linarith [hf0 μ i j])
    have hX0 : 0 ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, (f μ i j + f μ j i) :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by linarith [hf0 μ i j, hf0 μ j i]))
    have hn := hnet μ
    have hD := N.D_nonneg μ
    by_cases hs : N.s μ ∈ S <;> by_cases ht : N.t μ ∈ S
    · rw [if_neg (by tauto)]
      exact hX0
    · rw [if_pos (by tauto)]
      rw [if_pos hs, if_neg ht] at hn
      linarith
    · rw [if_pos (by tauto)]
      rw [if_neg hs, if_pos ht] at hn
      linarith
    · rw [if_neg (by tauto)]
      exact hX0
  have h3 : lam * N.Dem S = ∑ μ, (if (N.s μ ∈ S ∧ N.t μ ∉ S) ∨ (N.s μ ∉ S ∧ N.t μ ∈ S)
      then lam * N.D μ else 0) := by
    unfold Network.Dem
    rw [Finset.mul_sum, Finset.sum_filter]
  rw [h3]
  calc _ ≤ ∑ μ, ∑ i ∈ S, ∑ j ∈ Sᶜ, (f μ i j + f μ j i) := Finset.sum_le_sum (fun μ _ => hper μ)
    _ = ∑ i ∈ S, ∑ j ∈ Sᶜ, ∑ μ, (f μ i j + f μ j i) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
    _ ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, N.C i j :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hcap i j))
    _ = N.Cap S := rfl
