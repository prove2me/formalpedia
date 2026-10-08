-- Prove2me | solution 1 for MulticutLShaped.Bound.aggregation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T00:01:35.74926+00:00
-- url     : https://prove2.me/submissions/6dcb2180-c02a-4067-8345-49cd0e7ea7a3

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_MulticutLShaped_Bound_Masters

open StochasticProg.Recourse MulticutLShaped.Bound in
theorem solution {n1 n2 m1 m2 K : ℕ} (inst : Instance n1 n2 m1 m2 K)
    (F : List ((Fin n1 → ℝ) × ℝ)) (C : Fin K → List ((Fin n1 → ℝ) × ℝ))
    (L : List ((Fin n1 → ℝ) × ℝ))
    (hL : ∀ c ∈ L, ∃ sel : Fin K → (Fin n1 → ℝ) × ℝ, (∀ k, sel k ∈ C k) ∧
      c.1 = ∑ k, (sel k).1 ∧ c.2 = ∑ k, (sel k).2) :
    (∀ x θ, MultiFeasible inst F C x θ → LFeasible inst F L x (∑ k, θ k)) ∧
    (L ≠ [] → ∀ x θ y η, IsMultiOptimal inst F C x θ → IsLOptimal inst F L y η →
      LObj inst L y η ≤ multiObj inst C x θ) := by
  have part1 : ∀ x θ, MultiFeasible inst F C x θ → LFeasible inst F L x (∑ k, θ k) := by
    rintro x θ ⟨hK, hF, hC⟩
    refine ⟨hK, hF, ?_⟩
    intro c hc
    obtain ⟨sel, hsel, h1, h2⟩ := hL c hc
    rw [h1, h2, sum_dotProduct, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k _ => hC k (sel k) (hsel k)
  refine ⟨part1, ?_⟩
  intro hne x θ y η hM hLo
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil L hne
  obtain ⟨sel, hsel, -, -⟩ := hL c hc
  have hCne : ∀ k, C k ≠ [] := fun k h => by
    have := hsel k
    rw [h] at this
    simp at this
  have hobj : multiObj inst C x θ = inst.c ⬝ᵥ x + ∑ k, θ k := by
    unfold multiObj
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext k
    simp [hCne k]
  have h := hLo.2 x (∑ k, θ k) (part1 x θ hM.1)
  rw [hobj]
  unfold LObj at h ⊢
  simpa [hne] using h
