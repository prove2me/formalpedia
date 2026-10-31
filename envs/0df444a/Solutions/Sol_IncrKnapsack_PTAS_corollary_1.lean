-- Prove2me | solution 1 for IncrKnapsack.PTAS.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T03:09:49.256758+00:00
-- url     : https://prove2.me/submissions/860ae797-0af1-4a9d-85eb-7d4dd017be67

import Mathlib
import Definitions.Def_IncrKnapsack_PTAS_Model
import Theorems.Thm_IncrKnapsack_PTAS_representation_1
import Theorems.Thm_IncrKnapsack_PTAS_filtering
import Theorems.Thm_IncrKnapsack_PTAS_lemma_8

open Classical
open Finset BigOperators
open IncrKnapsack.PTAS

theorem solution (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K) (ξ : ℕ) (hξ : ξ < K)
    (Sstar : Sol I) (hopt : IsOptimal I (pr I K) Sstar)
    (hshift : (1 - eps K) * Psi I (pr I K) Sstar ≤ Psi I (pr I K) (restrictGood I K ξ Sstar)) :
    ∀ ϕ : ℝ, ϕ ≤ (1 - 2 * eps K) * Psi I (pr I K) Sstar →
      F I K ξ (Mcl I K ξ) (Lmax I K + 1) ϕ < ⊤ := by
  intro ϕ hϕ
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have he0 : 0 ≤ eps K := by unfold eps; positivity
  have he1 : eps K ≤ 1 := by
    unfold eps; rw [div_le_one hKpos]; exact_mod_cast (by omega : 1 ≤ K)
  have hpr : ∀ i, 0 ≤ pr I K i := fun i => by unfold pr; positivity
  have hΨs0 : 0 ≤ Psi I (pr I K) Sstar := by
    unfold Psi
    exact Finset.sum_nonneg (fun t _ => mul_nonneg (hI.lam_nonneg t)
      (Finset.sum_nonneg (fun i _ => hpr i)))
  set Sg := restrictGood I K ξ Sstar with hSg
  have hSg_some : ∀ i t, Sg i = some t → Sstar i = some t ∧ IsGood I K ξ t := by
    intro i t h
    simp only [hSg, restrictGood, Option.filter_eq_some_iff, decide_eq_true_eq] at h
    exact h
  have hSg_feas : Feasible I Sg := by
    intro t
    refine le_trans ?_ (hopt.1 t)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [Sol.set, mem_filter, mem_univ, true_and] at hi ⊢
      obtain ⟨s, hs, hst⟩ := hi
      exact ⟨s, (hSg_some i s hs).1, hst⟩
    · intro i _ _; exact (hI.w_pos i).le
  have hSg_good : ∀ i t, Sg i = some t → IsGood I K ξ t := fun i t h => (hSg_some i t h).2
  obtain ⟨hfe, hfg, hfp⟩ := filtering I hI K hK ξ hξ Sg hSg_feas hSg_good
  have hus := lemma_8 I hI K hK ξ hξ Sg hSg_good
  set St := filt I K (pr I K) Sg
  have hmf : MultiFeas I K ξ (Mcl I K ξ) (Lmax I K + 1) ϕ St := by
    refine ⟨hfe, hus, ?_, ?_⟩
    · intro i t h
      have hg := hfg i t h
      refine ⟨hg, ?_, ?_⟩
      · exact Finset.le_sup (f := clus I K ξ) (by simp [hg])
      · have : cls I K i ≤ Lmax I K := Finset.le_sup (f := cls I K) (mem_univ i)
        omega
    · rw [← representation_1]
      have h1 : (1 - eps K) * ((1 - eps K) * Psi I (pr I K) Sstar) ≤
          (1 - eps K) * Psi I (pr I K) Sg := mul_le_mul_of_nonneg_left hshift (by linarith)
      have h2 : (1 - 2 * eps K) * Psi I (pr I K) Sstar ≤
          (1 - eps K) * ((1 - eps K) * Psi I (pr I K) Sstar) := by
        nlinarith [mul_nonneg (sq_nonneg (eps K)) hΨs0]
      linarith
  unfold F
  calc (univ.filter (MultiFeas I K ξ (Mcl I K ξ) (Lmax I K + 1) ϕ)).inf
        (fun S => ((weight I S : ℝ) : WithTop ℝ))
      ≤ ((weight I St : ℝ) : WithTop ℝ) := Finset.inf_le (by simp [hmf])
    _ < ⊤ := WithTop.coe_lt_top _
