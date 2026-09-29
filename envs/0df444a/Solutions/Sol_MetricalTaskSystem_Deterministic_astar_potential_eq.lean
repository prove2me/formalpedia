-- Prove2me | solution 1 for MetricalTaskSystem.Deterministic.astar_potential_eq
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:34:09.543991+00:00
-- url     : https://prove2.me/submissions/f2cab685-41ce-4f85-be48-1820340ea377

import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model
import Definitions.Def_MetricalTaskSystem_Deterministic_AstarD

namespace MetricalTaskSystem.Deterministic

theorem aux_app_sum_step {S : Type} [Fintype S] [DecidableEq S]
    (d : S → S → ℝ) (s : ℕ → S) (k : ℕ) :
    (∑ x, fSeq d s (k + 1) x) =
      (∑ x, fSeq d s k x) + (fSeq d s (k + 1) (s k) - fSeq d s k (s k)) := by
  have h1 := Finset.add_sum_erase Finset.univ (fSeq d s (k + 1)) (Finset.mem_univ (s k))
  have h2 := Finset.add_sum_erase Finset.univ (fSeq d s k) (Finset.mem_univ (s k))
  have h3 : ∑ x ∈ Finset.univ.erase (s k), fSeq d s (k + 1) x =
      ∑ x ∈ Finset.univ.erase (s k), fSeq d s k x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_erase] at hx
    simp [fSeq, hx.1]
  linarith

end MetricalTaskSystem.Deterministic

open MetricalTaskSystem.Deterministic

theorem solution {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S]
    (d : S → S → ℝ) (hd : IsTaskSystem d) (s₀ : S) (s : ℕ → S) (hs : IsAstarSeq d s₀ s)
    (k : ℕ) :
    2 * ∑ x ∈ Finset.univ.erase (s k), fSeq d s k x + fSeq d s k (s k) =
      ∑ i ∈ Finset.range k, cSeq d s i + ∑ i ∈ Finset.range k, d (s (i + 1)) (s i) := by
  have hf : ∀ k, fSeq d s (k + 1) (s (k + 1)) = fSeq d s k (s (k + 1)) := fun k => by
    simp [fSeq, (hs.2 k).1]
  have hfk : ∀ k, fSeq d s (k + 1) (s k) = fSeq d s k (s (k + 1)) + d (s (k + 1)) (s k) :=
    fun k => by simp [fSeq]
  have main : ∀ k, 2 * (∑ x, fSeq d s k x) - fSeq d s k (s k) =
      ∑ i ∈ Finset.range k, cSeq d s i + ∑ i ∈ Finset.range k, d (s (i + 1)) (s i) := by
    intro k
    induction k with
    | zero => simp [fSeq]
    | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, aux_app_sum_step, hf]
      have hc : cSeq d s k = fSeq d s (k + 1) (s k) - fSeq d s k (s k) := rfl
      have := hfk k
      linarith
  have h2 := Finset.add_sum_erase Finset.univ (fSeq d s k) (Finset.mem_univ (s k))
  have := main k
  linarith
