-- Prove2me | solution 1 for MultiItemRev.BundlingOpt.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:41:18.274224+00:00
-- url     : https://prove2.me/submissions/c6777bb3-9e5e-45ca-9ad9-10158f2723a9

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model

set_option autoImplicit false
open MeasureTheory
open scoped NNReal ENNReal
open MultiItemRev.BundlingOpt

theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] (M : Mechanism ι) :
    IsIC M ↔
      ((∀ (x y : ι → ℝ≥0) (t : ℝ≥0), t ≤ 1 →
          buyerPayoff M (t • x + (1 - t) • y) ≤
            (t : ℝ) * buyerPayoff M x + (1 - (t : ℝ)) * buyerPayoff M y) ∧
        ∀ x x' : ι → ℝ≥0,
          ∑ i, M.q x i * ((x' i : ℝ) - (x i : ℝ)) ≤ buyerPayoff M x' - buyerPayoff M x) := by
  constructor
  · intro hIC
    refine ⟨?_, ?_⟩
    · intro x y t ht
      have ht0 : (0 : ℝ) ≤ t := t.coe_nonneg
      have h1t : (0 : ℝ) ≤ 1 - t := by
        have : (t : ℝ) ≤ 1 := by exact_mod_cast ht
        linarith
      set z : ι → ℝ≥0 := t • x + (1 - t) • y with hzdef
      have hz : ∀ i, ((z i : ℝ≥0) : ℝ) = (t : ℝ) * (x i : ℝ) + (1 - (t : ℝ)) * (y i : ℝ) := by
        intro i
        simp [hzdef, Pi.add_apply, Pi.smul_apply, NNReal.coe_add, NNReal.coe_mul,
          NNReal.coe_sub ht]
      have e : ∑ i, M.q z i * ((z i : ℝ≥0) : ℝ)
          = (t : ℝ) * ∑ i, M.q z i * (x i : ℝ) + (1 - (t : ℝ)) * ∑ i, M.q z i * (y i : ℝ) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hz i]
        ring
      have hz' : buyerPayoff M z = (t : ℝ) * (∑ i, M.q z i * (x i : ℝ) - M.s z)
          + (1 - (t : ℝ)) * (∑ i, M.q z i * (y i : ℝ) - M.s z) := by
        unfold buyerPayoff
        rw [e]
        ring
      rw [hz']
      nlinarith [mul_le_mul_of_nonneg_left (hIC x z) ht0,
        mul_le_mul_of_nonneg_left (hIC y z) h1t]
    · intro x x'
      have h := hIC x' x
      unfold buyerPayoff at h ⊢
      simp only [mul_sub, Finset.sum_sub_distrib]
      linarith
  · rintro ⟨-, h⟩ x x'
    have h' := h x' x
    unfold buyerPayoff at h' ⊢
    simp only [mul_sub, Finset.sum_sub_distrib] at h'
    linarith
