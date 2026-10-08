-- Prove2me | solution 1 for GilmoreGomoryTSP.MinCost.eq_11_interchange_cost
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:41:11.820535+00:00
-- url     : https://prove2.me/submissions/549a66d8-fb0b-4b28-8b54-15de2c9cde1a

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model
import Definitions.Def_GilmoreGomoryTSP_MinCost_Underestimate



namespace GilmoreGomoryTSP.MinCost

open MeasureTheory

variable {n : ℕ}

lemma e11_ii (f : ℝ → ℝ) (hf : LocallyIntegrable f) (a b : ℝ) :
    IntervalIntegrable f volume a b :=
  (hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable

noncomputable def e11F (φ γ : ℝ → ℝ) (u v : ℝ) : ℝ := if u ≤ v then φ v - φ u else γ u - γ v

lemma e11_c (f g : ℝ → ℝ) (hf : LocallyIntegrable f) (hg : LocallyIntegrable g)
    (A B : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) :
    c f g A B i j = e11F (fun t => ∫ x in (0:ℝ)..t, f x) (fun t => ∫ x in (0:ℝ)..t, g x)
      (B i) (A j) := by
  unfold c e11F
  split_ifs with h
  · rw [← intervalIntegral.integral_interval_sub_left (e11_ii f hf _ _) (e11_ii f hf _ _)]
  · rw [← intervalIntegral.integral_interval_sub_left (e11_ii g hg _ _) (e11_ii g hg _ _)]

lemma e11_alg (φ γ : ℝ → ℝ) (a b p q : ℝ) (hab : a ≤ b) (hpq : p ≤ q) :
    e11F φ γ a q + e11F φ γ b p - e11F φ γ a p - e11F φ γ b q =
      if max a p ≤ min b q then (φ (min b q) + γ (min b q)) - (φ (max a p) + γ (max a p))
      else 0 := by
  unfold e11F
  simp only [max_def, min_def]
  split_ifs <;> first
    | linarith
    | (exfalso; linarith)
    | (have e : b = p := (by linarith); subst e; linarith)
    | (have e : a = q := (by linarith); subst e; linarith)
    | (have e : a = p := (by linarith); subst e; linarith)
    | (have e : b = q := (by linarith); subst e; linarith)

lemma e11_cost (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (ψ : Equiv.Perm (Fin (n + 1)))
    (i j : Fin (n + 1)) :
    interchangeCost f g A B ψ i j =
      c f g A B i (ψ j) + c f g A B j (ψ i) - c f g A B i (ψ i) - c f g A B j (ψ j) := by
  unfold interchangeCost cost
  by_cases hij : i = j
  · subst hij; simp [alpha]
  · rw [← Finset.sum_sub_distrib]
    rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset (Fin (n+1))))]
    · rw [Finset.sum_pair hij]
      simp [alpha, Equiv.swap_apply_left, Equiv.swap_apply_right]
      ring
    · intro x _ hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      simp [alpha, Equiv.swap_apply_of_ne_of_ne hx.1 hx.2]

theorem eq_11_core {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ)
    (ψ : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1))
    (hBij : B i ≤ B j) (hAij : A (ψ i) ≤ A (ψ j)) :
    interchangeCost f g A B ψ i j =
      ∫ x in Set.Icc (B i) (B j) ∩ Set.Icc (A (ψ i)) (A (ψ j)), (f x + g x) := by
  rw [e11_cost, e11_c f g hf hg, e11_c f g hf hg, e11_c f g hf hg, e11_c f g hf hg]
  set φ : ℝ → ℝ := fun t => ∫ x in (0:ℝ)..t, f x
  set γ : ℝ → ℝ := fun t => ∫ x in (0:ℝ)..t, g x
  rw [e11_alg φ γ _ _ _ _ hBij hAij, Set.Icc_inter_Icc]
  split_ifs with h
  · have h1 : φ (min (B j) (A (ψ j))) - φ (max (B i) (A (ψ i))) =
        ∫ x in (max (B i) (A (ψ i)))..(min (B j) (A (ψ j))), f x :=
      intervalIntegral.integral_interval_sub_left (e11_ii f hf _ _) (e11_ii f hf _ _)
    have h2 : γ (min (B j) (A (ψ j))) - γ (max (B i) (A (ψ i))) =
        ∫ x in (max (B i) (A (ψ i)))..(min (B j) (A (ψ j))), g x :=
      intervalIntegral.integral_interval_sub_left (e11_ii g hg _ _) (e11_ii g hg _ _)
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h,
      intervalIntegral.integral_add (e11_ii f hf _ _) (e11_ii g hg _ _)]
    linarith
  · rw [Set.Icc_eq_empty h]; simp

end GilmoreGomoryTSP.MinCost

open GilmoreGomoryTSP.MinCost


theorem solution {n : ℕ}
    (f g : ℝ → ℝ) (hf : MeasureTheory.LocallyIntegrable f) (hg : MeasureTheory.LocallyIntegrable g)
    (hfg : ∀ x, 0 ≤ f x + g x) (A B : Fin (n + 1) → ℝ)
    (ψ : Equiv.Perm (Fin (n + 1))) (i j : Fin (n + 1))
    (hBij : B i ≤ B j) (hAij : A (ψ i) ≤ A (ψ j)) :
    interchangeCost f g A B ψ i j =
      ∫ x in Set.Icc (B i) (B j) ∩ Set.Icc (A (ψ i)) (A (ψ j)), (f x + g x) := by
  exact eq_11_core f g hf hg hfg A B ψ i j hBij hAij
