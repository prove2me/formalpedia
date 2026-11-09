-- Prove2me | solution 1 for LinearZeroSumMG.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T09:28:04.954106+00:00
-- url     : https://prove2.me/submissions/0d8b3246-6f2d-4c59-a7f2-95d039ae43e5

import Mathlib
import Definitions.Def_LinearZeroSumMG_omni

namespace Aux_LZSMG_lemma4

open LinearZeroSumMG

theorem wavg {ι : Type*} [Fintype ι] (w f g : ι → ℝ) (ε : ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hfg : ∀ i, |f i - g i| ≤ ε) :
    ∑ i, w i * f i ≤ ∑ i, w i * g i + ε := by
  have h : ∑ i, w i * f i - ∑ i, w i * g i ≤ ∑ i, w i * ε := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [← mul_sub]
    exact mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hfg i)) (hw0 i)
  rw [← Finset.sum_mul, hw1, one_mul] at h
  linarith

theorem approx {A : Type*} [Fintype A] (ε : ℝ) (σ : A × A → ℝ) (u₁ u₂ Q₁ Q₂ : A → A → ℝ)
    (hc : IsCCE u₁ u₂ σ) (h1 : ∀ a b, |u₁ a b - Q₁ a b| ≤ ε)
    (h2 : ∀ a b, |u₂ a b - Q₂ a b| ≤ ε) : IsApproxCCE (2 * ε) Q₁ Q₂ σ := by
  obtain ⟨hσ, hc1, hc2⟩ := hc
  have hσ0 : ∀ ab, 0 ≤ σ ab := hσ.1
  have hσ1 : ∑ ab, σ ab = 1 := hσ.2
  have hm20 : ∀ b, 0 ≤ marg2 σ b := fun b => Finset.sum_nonneg (fun a _ => hσ0 (a, b))
  have hm10 : ∀ a, 0 ≤ marg1 σ a := fun a => Finset.sum_nonneg (fun b _ => hσ0 (a, b))
  have hm11 : ∑ a, marg1 σ a = 1 := by
    unfold marg1; rw [← hσ1, Fintype.sum_prod_type]
  have hm21 : ∑ b, marg2 σ b = 1 := by
    unfold marg2; rw [← hσ1, Fintype.sum_prod_type, Finset.sum_comm]
  have h1' : ∀ a b, |Q₁ a b - u₁ a b| ≤ ε := fun a b => by rw [abs_sub_comm]; exact h1 a b
  have h2' : ∀ a b, |Q₂ a b - u₂ a b| ≤ ε := fun a b => by rw [abs_sub_comm]; exact h2 a b
  refine ⟨hσ, fun a' => ?_, fun b' => ?_⟩
  · have e1 := wavg σ (fun ab => u₁ ab.1 ab.2) (fun ab => Q₁ ab.1 ab.2) ε hσ0 hσ1
      (fun ab => h1 ab.1 ab.2)
    have e2 := wavg (marg2 σ) (fun b => Q₁ a' b) (fun b => u₁ a' b) ε hm20 hm21
      (fun b => h1' a' b)
    have e3 := hc1 a'
    try simp only at e1 e2
    linarith
  · have e1 := wavg σ (fun ab => Q₂ ab.1 ab.2) (fun ab => u₂ ab.1 ab.2) ε hσ0 hσ1
      (fun ab => h2' ab.1 ab.2)
    have e2 := wavg (marg1 σ) (fun a => u₂ a b') (fun a => Q₂ a b') ε hm10 hm11
      (fun a => h2 a b')
    have e3 := hc2 b'
    try simp only at e1 e2
    linarith

end Aux_LZSMG_lemma4

open LinearZeroSumMG in
theorem solution {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] [Fintype A] {d : ℕ}
    (G : MarkovGame S A) (P : OmniParams S A d)
    (hcce : ∀ u₁ u₂ : A → A → ℝ, IsCCE u₁ u₂ (P.cce u₁ u₂))
    (xs : ℕ → ℕ → S) (as bs : ℕ → ℕ → A) (k h : ℕ) (x : S) (ε : ℝ)
    (hclose : ∀ a b,
      |(omni G P xs as bs k h).pick.1 x a b - (omni G P xs as bs k h).QUp x a b| ≤ ε ∧
      |(omni G P xs as bs k h).pick.2 x a b - (omni G P xs as bs k h).QLo x a b| ≤ ε) :
    IsApproxCCE (2 * ε) ((omni G P xs as bs k h).QUp x) ((omni G P xs as bs k h).QLo x)
      ((omni G P xs as bs k h).sigma x) := by
  have hc : IsCCE ((omni G P xs as bs k h).pick.1 x) ((omni G P xs as bs k h).pick.2 x)
      ((omni G P xs as bs k h).sigma x) :=
    hcce ((omni G P xs as bs k h).pick.1 x) ((omni G P xs as bs k h).pick.2 x)
  exact Aux_LZSMG_lemma4.approx ε _ _ _ _ _ hc (fun a b => (hclose a b).1)
    (fun a b => (hclose a b).2)
