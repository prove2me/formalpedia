-- Prove2me | solution 1 for IncrKnapsack.PTAS.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T03:05:55.012589+00:00
-- url     : https://prove2.me/submissions/f80bf559-e769-433b-8d62-81d8184dd1e1

import Mathlib
import Definitions.Def_IncrKnapsack_PTAS_Model
import Theorems.Thm_IncrKnapsack_PTAS_corollary_1
import Theorems.Thm_IncrKnapsack_PTAS_claim_3
import Theorems.Thm_IncrKnapsack_PTAS_claim_2

open Classical
open Finset BigOperators
open IncrKnapsack.PTAS

theorem solution (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K) (ξ : ℕ) (hξ : ξ < K)
    (Sstar : Sol I) (hopt : IsOptimal I (pr I K) Sstar)
    (hshift : (1 - eps K) * Psi I (pr I K) Sstar ≤ Psi I (pr I K) (restrictGood I K ξ Sstar))
    (Φ : Finset ℝ) (A : Subroutine I) (jt : ℕ → ℕ) (ϕt : ℕ → ℝ)
    (hΦ : IsProfitGrid I K ξ Φ) (hA : IsSubroutine I K ξ A) (htr : IsTraceback I K ξ Φ A jt ϕt) :
    (1 - 7 * eps K) * Psi I (pr I K) Sstar ≤ Psi I (pr I K) (algOut I K ξ Φ A jt ϕt) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hK5 : (5 : ℝ) ≤ K := by exact_mod_cast (by omega : 5 ≤ K)
  have he0 : 0 < eps K := by unfold eps; positivity
  have he5 : 5 * eps K ≤ 1 := by
    unfold eps; rw [mul_one_div, div_le_one hKpos]; exact hK5
  have hpr : ∀ i, 0 ≤ pr I K i := fun i => by unfold pr; positivity
  have hPsi_nonneg : ∀ S : Sol I, 0 ≤ Psi I (pr I K) S := by
    intro S; unfold Psi
    exact Finset.sum_nonneg (fun t _ => mul_nonneg (hI.lam_nonneg t)
      (Finset.sum_nonneg (fun i _ => hpr i)))
  set Ψs := Psi I (pr I K) Sstar with hΨs
  set Sb := algOut I K ξ Φ A jt ϕt
  have hΨs0 : 0 ≤ Ψs := hPsi_nonneg _
  have hΨb0 : 0 ≤ Psi I (pr I K) Sb := hPsi_nonneg _
  by_cases hM : Mcl I K ξ = 0
  · -- no good period at all
    have hnogood : ∀ t, ¬ IsGood I K ξ t := by
      intro t ht
      have h1 : clus I K ξ t ≤ Mcl I K ξ := Finset.le_sup (f := clus I K ξ) (by simp [ht])
      unfold clus at h1; omega
    have hrg : Psi I (pr I K) (restrictGood I K ξ Sstar) = 0 := by
      unfold Psi
      apply Finset.sum_eq_zero; intro t _
      have : Sol.set (restrictGood I K ξ Sstar) t = ∅ := by
        ext i
        simp only [Sol.set, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        rintro ⟨s, hs, _⟩
        simp only [restrictGood, Option.filter_eq_some_iff, decide_eq_true_eq] at hs
        exact hnogood s hs.2
      simp [this]
    rw [hrg] at hshift
    have : Ψs = 0 := by nlinarith
    rw [this, mul_zero]; exact hΨb0
  have hMpos : 0 < Mcl I K ξ := Nat.pos_of_ne_zero hM
  have hMr : (1 : ℝ) ≤ (Mcl I K ξ : ℝ) := by exact_mod_cast hMpos
  set M : ℝ := (Mcl I K ξ : ℝ) with hMdef
  -- λ_T p_max ≤ Ψ(S*)
  have hne : (univ : Finset (Fin I.n)).Nonempty := ⟨⟨0, hI.n_pos⟩, mem_univ _⟩
  obtain ⟨i0, _, hi0⟩ := Finset.exists_mem_eq_sup' hne (pr I K)
  have hpmax : pmax I K = pr I K i0 := by unfold pmax; rw [dif_pos hne, hi0]
  set tl : Fin I.T := ⟨I.T - 1, by have := hI.T_pos; omega⟩
  have hlamLast : lamLast I = I.lam tl := by unfold lamLast; rw [dif_pos hI.T_pos]
  have hWLast : WLast I = I.W tl := by unfold WLast; rw [dif_pos hI.T_pos]
  let S1 : Sol I := fun i => if i = i0 then some tl else none
  have hS1set : ∀ t, Sol.set S1 t = if t = tl then {i0} else ∅ := by
    intro t
    ext i
    simp only [Sol.set, S1, mem_filter, mem_univ, true_and]
    by_cases ht : t = tl
    · subst ht
      simp only [if_true, mem_singleton]
      constructor
      · rintro ⟨s, hs, _⟩; by_contra h; rw [if_neg h] at hs; simp at hs
      · rintro rfl; exact ⟨tl, by simp, le_rfl⟩
    · rw [if_neg ht]
      simp only [Finset.notMem_empty, iff_false, not_exists, not_and]
      intro s hs hst
      by_cases hi : i = i0
      · rw [if_pos hi] at hs; cases hs
        exact ht (le_antisymm (by have := t.2; simp [tl, Fin.le_def]; omega) hst)
      · rw [if_neg hi] at hs; simp at hs
  have hS1feas : Feasible I S1 := by
    intro t; rw [hS1set t]
    split_ifs with ht
    · rw [Finset.sum_singleton, ht, ← hWLast]; exact hI.fits i0
    · rw [Finset.sum_empty]; exact hI.W_nonneg t
  have hS1psi : Psi I (pr I K) S1 = lamLast I * pmax I K := by
    unfold Psi
    rw [Finset.sum_eq_single tl]
    · rw [hS1set, if_pos rfl, Finset.sum_singleton, hlamLast, hpmax]
    · intro t _ ht; rw [hS1set, if_neg ht]; simp
    · simp
  have hLP : lamLast I * pmax I K ≤ Ψs := by rw [← hS1psi]; exact hopt.2 S1 hS1feas
  have hδ0 : 0 ≤ delta I K ξ := by
    unfold delta
    have : 0 ≤ lamLast I := hI.lam_last_pos.le
    have : 0 ≤ pmax I K := by rw [hpmax]; exact hpr i0
    positivity
  have hMδ : M * delta I K ξ ≤ eps K * Ψs := by
    unfold delta
    rw [← hMdef]
    have : M * (eps K / M * lamLast I * pmax I K) = eps K * (lamLast I * pmax I K) := by
      field_simp
    rw [this]; exact mul_le_mul_of_nonneg_left hLP he0.le
  have hδ : delta I K ξ ≤ eps K * Ψs := by
    have : delta I K ξ ≤ M * delta I K ξ := le_mul_of_one_le_left hδ0 hMr
    linarith
  -- the target profit level
  set ϕ0 := (1 - 2 * eps K) * Ψs with hϕ0
  have hϕ0nn : 0 ≤ ϕ0 := mul_nonneg (by linarith) hΨs0
  have hϕ0le : ϕ0 ≤ lamTotal I * ∑ i, pr I K i := by
    have h1 : ϕ0 ≤ Ψs := by rw [hϕ0]; nlinarith
    have h2 : Ψs ≤ lamTotal I * ∑ i, pr I K i := by
      rw [hΨs]; unfold Psi lamTotal; rw [Finset.sum_mul]
      apply Finset.sum_le_sum; intro t _
      apply mul_le_mul_of_nonneg_left _ (hI.lam_nonneg t)
      exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => hpr i)
    linarith
  obtain ⟨x, hxΦ, hxle, hxge⟩ := hΦ.2.2 hMpos ϕ0 hϕ0nn hϕ0le
  have hx0 : 0 ≤ x := hΦ.2.1 x hxΦ
  have hF := corollary_1 I hI K hK ξ hξ Sstar hopt hshift x hxle
  have hFt := claim_3 I hI K hK ξ hξ Φ A hΦ hA (Mcl I K ξ) le_rfl (Lmax I K + 1) le_rfl x hxΦ
  have hFtfin : Ftil I K ξ Φ A (Mcl I K ξ) (Lmax I K + 1) x < ⊤ := lt_of_le_of_lt hFt hF
  have hxt : x ≤ ϕt (Mcl I K ξ) := htr.2.2.2.1 x hxΦ hFtfin
  have hc2 := claim_2 I hI K hK ξ hξ Φ A jt ϕt hΦ hA htr
  rw [← hMdef] at hc2
  -- x ≥ (1 - ε)(ϕ0 - δ)
  have hx1 : ϕ0 - delta I K ξ ≤ (1 + eps K) * x := by
    have : eps K / M ≤ eps K := div_le_self he0.le hMr
    have := mul_le_mul_of_nonneg_right this hx0
    nlinarith
  have hx2 : (1 - eps K) * (ϕ0 - delta I K ξ) ≤ x := by
    have : (1 - eps K) * (1 + eps K) * x ≤ x := by nlinarith [mul_nonneg (sq_nonneg (eps K)) hx0]
    have h3 : (1 - eps K) * (ϕ0 - delta I K ξ) ≤ (1 - eps K) * ((1 + eps K) * x) :=
      mul_le_mul_of_nonneg_left hx1 (by linarith)
    nlinarith
  have hb1 : (1 - 2 * eps K) * x ≤ (1 - 2 * eps K) * ϕt (Mcl I K ξ) :=
    mul_le_mul_of_nonneg_left hxt (by linarith)
  -- assemble
  have hfin : (1 - 7 * eps K) * Ψs ≤
      (1 - 2 * eps K) * ((1 - eps K) * (ϕ0 - delta I K ξ)) - eps K * Ψs := by
    have hd : (1 - 2 * eps K) * ((1 - eps K) * (ϕ0 - delta I K ξ)) ≥
        (1 - 2 * eps K) * ((1 - eps K) * (ϕ0 - eps K * Ψs)) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      linarith
    have : (1 - 7 * eps K) * Ψs + eps K * Ψs ≤
        (1 - 2 * eps K) * ((1 - eps K) * (ϕ0 - eps K * Ψs)) := by
      rw [hϕ0]
      have hp : 0 ≤ eps K ^ 2 * (11 - 6 * eps K) := by
        apply mul_nonneg (sq_nonneg _); linarith
      nlinarith [mul_nonneg hp hΨs0]
    linarith
  have hc : (1 - 2 * eps K) * ((1 - eps K) * (ϕ0 - delta I K ξ)) ≤
      (1 - 2 * eps K) * x := mul_le_mul_of_nonneg_left hx2 (by linarith)
  linarith
