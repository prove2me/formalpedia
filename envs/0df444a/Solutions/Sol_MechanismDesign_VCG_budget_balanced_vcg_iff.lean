-- Prove2me | solution 1 for MechanismDesign.VCG.budget_balanced_vcg_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:06:18.132746+00:00
-- url     : https://prove2.me/submissions/abbbd345-8afe-4915-a3d5-db4eb2e9f09b

import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model



namespace MechanismDesign.VCG

lemma bb_double_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, x j = ((Fintype.card ι : ℝ) - 1) * ∑ j, x j := by
  have : ∀ i, ∑ j ∈ Finset.univ.erase i, x j = ∑ j, x j - x i := by
    intro i
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  simp only [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem budget_balanced_vcg_iff_core {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι]
    (u : ∀ i, A → Θ i → ℝ) (hN : 2 ≤ Fintype.card ι) (q : (∀ i, Θ i) → A)
    (hq : IsEfficient u q) :
    (∃ t : ι → (∀ i, Θ i) → ℝ,
        IsVCG u (⟨q, t⟩ : DirectMechanism Θ A) ∧ BudgetBalanced (⟨q, t⟩ : DirectMechanism Θ A)) ↔
      ∃ f : ∀ i, Others Θ i → ℝ, ∀ θ : ∀ j, Θ j,
        ∑ i, u i (q θ) (θ i) = ∑ i, f i (restrict θ i) := by
  have hN' : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hN
  have hpos : (0 : ℝ) < (Fintype.card ι : ℝ) - 1 := by linarith
  constructor
  · rintro ⟨t, ⟨_, hτ⟩, hbb⟩
    choose τ hτ using hτ
    refine ⟨fun i r => τ i r / ((Fintype.card ι : ℝ) - 1), fun θ => ?_⟩
    have h0 := hbb θ
    simp only at h0 hτ
    rw [Finset.sum_congr rfl (fun i _ => hτ i θ)] at h0
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, bb_double_sum (fun j => u j (q θ) (θ j))] at h0
    rw [← Finset.sum_div]
    field_simp
    linarith
  · rintro ⟨f, hf⟩
    refine ⟨fun i θ => -(∑ j ∈ Finset.univ.erase i, u j (q θ) (θ j))
      + ((Fintype.card ι : ℝ) - 1) * f i (restrict θ i), ⟨hq, fun i => ⟨fun r => ((Fintype.card ι : ℝ) - 1) * f i r, fun θ => rfl⟩⟩, fun θ => ?_⟩
    simp only
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, bb_double_sum (fun j => u j (q θ) (θ j)),
      ← Finset.mul_sum, hf θ]
    ring

end MechanismDesign.VCG

open MechanismDesign.VCG


theorem solution {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι]
    (u : ∀ i, A → Θ i → ℝ) (hN : 2 ≤ Fintype.card ι) (q : (∀ i, Θ i) → A)
    (hq : IsEfficient u q) :
    (∃ t : ι → (∀ i, Θ i) → ℝ,
        IsVCG u (⟨q, t⟩ : DirectMechanism Θ A) ∧ BudgetBalanced (⟨q, t⟩ : DirectMechanism Θ A)) ↔
      ∃ f : ∀ i, Others Θ i → ℝ, ∀ θ : ∀ j, Θ j,
        ∑ i, u i (q θ) (θ i) = ∑ i, f i (restrict θ i) := by
  exact budget_balanced_vcg_iff_core u hN q hq
