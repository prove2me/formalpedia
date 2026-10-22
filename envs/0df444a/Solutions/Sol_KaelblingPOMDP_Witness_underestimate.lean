-- Prove2me | solution 1 for KaelblingPOMDP.Witness.underestimate
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:31:44.075275+00:00
-- url     : https://prove2.me/submissions/8c4889fb-bca0-499d-9518-731131a651db

import Mathlib
import Definitions.Def_KaelblingPOMDP_Witness_Useful

open Finset KaelblingPOMDP.Witness

universe u

theorem kael_key {S A Ω : Type u} [Fintype S] [DecidableEq S] [Fintype Ω]
    (M : POMDP S A Ω) (hM : M.IsValid) {n : ℕ} (p : PolicyTree A Ω (n + 1)) (b : S → ℝ)
    (hb : b ∈ stdSimplex ℝ S) :
    valueAt M p b = ∑ s, b s * M.R s p.1 +
      M.γ * ∑ o, obsProb M b p.1 o * valueAt M (p.2 o) (stateEstimator M b p.1 o) := by
  have hb0 : ∀ s, 0 ≤ b s := hb.1
  -- per-observation identity
  have hobs : ∀ o, obsProb M b p.1 o * valueAt M (p.2 o) (stateEstimator M b p.1 o)
      = ∑ s', M.O s' p.1 o * (∑ s, M.T s p.1 s' * b s) * value M (p.2 o) s' := by
    intro o
    by_cases h0 : obsProb M b p.1 o = 0
    · rw [h0, zero_mul]
      have hterm : ∀ s' ∈ (univ : Finset S), 0 ≤ M.O s' p.1 o * ∑ s, M.T s p.1 s' * b s := by
        intro s' _
        exact mul_nonneg (hM.O_nonneg _ _ _)
          (Finset.sum_nonneg (fun s _ => mul_nonneg (hM.T_nonneg _ _ _) (hb0 s)))
      have hz := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 h0
      symm
      apply Finset.sum_eq_zero
      intro s' hs'
      rw [hz s' hs', zero_mul]
    · unfold valueAt stateEstimator
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s' _
      field_simp
  rw [Finset.sum_congr rfl (fun o _ => hobs o)]
  unfold valueAt
  simp only [value]
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  have hswap : ∀ f : S → S → Ω → ℝ, ∑ s, ∑ s', ∑ o, f s s' o = ∑ o, ∑ s', ∑ s, f s s' o := by
    intro f
    calc ∑ s, ∑ s', ∑ o, f s s' o = ∑ s, ∑ o, ∑ s', f s s' o :=
          Finset.sum_congr rfl (fun s _ => Finset.sum_comm)
      _ = ∑ o, ∑ s, ∑ s', f s s' o := Finset.sum_comm
      _ = ∑ o, ∑ s', ∑ s, f s s' o := Finset.sum_congr rfl (fun o _ => Finset.sum_comm)
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Eq.trans (hswap _) ?_
  refine Finset.sum_congr rfl (fun o _ => Finset.sum_congr rfl (fun s' _ => Finset.sum_congr rfl (fun s _ => ?_)))
  ring

theorem solution {S A Ω : Type u} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A]
    [Nonempty A] [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (M : POMDP S A Ω) (hM : M.IsValid) (a : A) (n : ℕ)
    (U : Finset (PolicyTree A Ω (n + 1))) (hU : U.Nonempty) (hUC : U ⊆ candidates M a n) :
    ∀ b ∈ stdSimplex ℝ S, upper M U hU b ≤ Qfun M a n b := by
  intro b hb
  unfold upper
  apply Finset.sup'_le
  intro p hp
  have hpc := hUC hp
  simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and] at hpc
  obtain ⟨hpa, -⟩ := hpc
  rw [kael_key M hM p b hb]
  have hpa' : p.1 = a := hpa
  rw [hpa']
  unfold Qfun
  have hobs0 : ∀ o, 0 ≤ obsProb M b a o := fun o =>
    Finset.sum_nonneg (fun s' _ => mul_nonneg (hM.O_nonneg _ _ _)
      (Finset.sum_nonneg (fun s _ => mul_nonneg (hM.T_nonneg _ _ _) (hb.1 s))))
  have hle : ∑ o, obsProb M b a o * valueAt M (p.2 o) (stateEstimator M b a o)
      ≤ ∑ o, obsProb M b a o * optValue M n (stateEstimator M b a o) := by
    apply Finset.sum_le_sum
    intro o _
    exact mul_le_mul_of_nonneg_left
      (Finset.le_sup' (fun q => valueAt M q (stateEstimator M b a o)) (Finset.mem_univ (p.2 o)))
      (hobs0 o)
  have := mul_le_mul_of_nonneg_left hle hM.γ_pos.le
  linarith
