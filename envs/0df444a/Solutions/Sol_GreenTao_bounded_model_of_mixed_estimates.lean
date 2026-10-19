-- Prove2me | solution 1 for GreenTao.bounded_model_of_mixed_estimates
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T20:54:22.571414+00:00
-- url     : https://prove2.me/submissions/c81fba0f-2895-4ff3-8f10-893948187b42

import Definitions.Def_GreenTao_Uniformity
import Mathlib

open scoped BigOperators
open GreenTao

private lemma avg_mono' {α : Type} [Fintype α] {f g : α → ℝ}
    (h : ∀ x, f x ≤ g x) : avg f ≤ avg g := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => h x) (by positivity)

private lemma avg_const' {α : Type} [Fintype α] [Nonempty α] (c : ℝ) :
    avg (fun _ : α => c) = c := by
  simp [avg, Fintype.card_ne_zero]

private lemma avg_sub' {α : Type} [Fintype α] (f g : α → ℝ) :
    avg (fun x => f x - g x) = avg f - avg g := by
  simp [avg, Finset.sum_sub_distrib, mul_sub]

private lemma avg_sum' {α β : Type} [Fintype α] [Fintype β] (F : β → α → ℝ) :
    avg (fun x => ∑ i, F i x) = ∑ i, avg (F i) := by
  simp only [avg, Finset.mul_sum]
  rw [Finset.sum_comm]

private lemma apAvg_mono' (k : ℕ) {m : ℕ+} {f g : ZMod (m : ℕ) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfg : ∀ x, f x ≤ g x) : apAvg k f ≤ apAvg k g := by
  apply avg_mono'
  intro x
  apply avg_mono'
  intro r
  exact Finset.prod_le_prod (fun j _ => hf _) (fun j _ => hfg _)

theorem solution (k : ℕ) (m : ℕ+) (f s u : ZMod (m : ℕ) → ℝ)
    (ε ξ : ℝ) (hε : 0 ≤ ε) (hξ : 0 ≤ ξ)
    (hs : ∀ x, 0 ≤ s x ∧ s x ≤ 1 + ε)
    (htu : ∀ x, 0 ≤ s x + u x ∧ s x + u x ≤ f x)
    (hmean : avg f - ε ≤ avg s)
    (hmixed : ∀ S : Finset (Fin k), S.Nonempty →
      |mixedAPAvg k (fun j x => if j ∈ S then u x else s x)| ≤ ξ) :
    ∃ g : ZMod (m : ℕ) → ℝ,
      (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧
      avg f - 2 * ε ≤ avg g ∧
      apAvg k g - (2 : ℝ) ^ k * ξ ≤ apAvg k f := by
  classical
  let g : ZMod (m : ℕ) → ℝ := fun x => s x / (1 + ε)
  have hden : 0 < 1 + ε := by linarith
  have hg (x) : 0 ≤ g x ∧ g x ≤ 1 := by
    constructor
    · exact div_nonneg (hs x).1 hden.le
    · exact (div_le_one hden).2 (hs x).2
  have hgs (x) : g x ≤ s x := by
    apply (div_le_iff₀ hden).2
    nlinarith [(hs x).1]
  have hsg (x) : s x - ε ≤ g x := by
    apply (le_div_iff₀ hden).2
    nlinarith [mul_nonneg hε (sub_nonneg.mpr (hs x).2)]
  refine ⟨g, hg, ?_, ?_⟩
  · have h := avg_mono' hsg
    rw [avg_sub', avg_const'] at h
    linarith
  · let A : Finset (Fin k) → ℝ := fun S =>
      mixedAPAvg k (fun j x => if j ∈ S then u x else s x)
    have hexpand : apAvg k (fun x => s x + u x) = ∑ S, A S := by
      have hp (x r : ZMod (m : ℕ)) :
          (∏ j : Fin k, (s (x + (j.val : ZMod (m : ℕ)) * r) +
            u (x + (j.val : ZMod (m : ℕ)) * r))) =
          ∑ S : Finset (Fin k), ∏ j : Fin k,
            (if j ∈ S then u (x + (j.val : ZMod (m : ℕ)) * r)
             else s (x + (j.val : ZMod (m : ℕ)) * r)) := by
        simp_rw [Finset.prod_ite]
        simpa [add_comm, Finset.compl_eq_univ_sdiff, Finset.sdiff_eq_filter] using Fintype.prod_add
          (fun j : Fin k => u (x + (j.val : ZMod (m : ℕ)) * r))
          (fun j : Fin k => s (x + (j.val : ZMod (m : ℕ)) * r))
      unfold apAvg
      simp_rw [hp, avg_sum']
      rfl
    have hempty : A ∅ = apAvg k s := by simp [A, mixedAPAvg, apAvg]
    have hsumlower : -(2 : ℝ) ^ k * ξ ≤
        ∑ S ∈ (Finset.univ : Finset (Finset (Fin k))).erase ∅, A S := by
      calc
        -(2 : ℝ) ^ k * ξ ≤
            -(((Finset.univ : Finset (Finset (Fin k))).erase ∅).card : ℝ) * ξ := by
          have hc : (((Finset.univ : Finset (Finset (Fin k))).erase ∅).card : ℝ)
              ≤ (2 : ℝ) ^ k := by
            have hc := Finset.card_erase_le (s := Finset.univ) (a := (∅ : Finset (Fin k)))
            simp only [Finset.card_univ, Fintype.card_finset, Fintype.card_fin] at hc
            exact_mod_cast hc
          nlinarith
        _ = ∑ _S ∈ (Finset.univ : Finset (Finset (Fin k))).erase ∅, -ξ := by
          simp
          ring
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro S hS
          have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hS)
          exact (abs_le.mp (hmixed S hSne)).1
    have hcount : apAvg k s - (2 : ℝ) ^ k * ξ ≤ apAvg k (fun x => s x + u x) := by
      rw [hexpand, ← Finset.sum_erase_add _ _ (Finset.mem_univ (∅ : Finset (Fin k))), hempty]
      linarith
    have hmono := apAvg_mono' k (fun x => (htu x).1) (fun x => (htu x).2)
    have hnorm := apAvg_mono' k (fun x => (hg x).1) hgs
    linarith
