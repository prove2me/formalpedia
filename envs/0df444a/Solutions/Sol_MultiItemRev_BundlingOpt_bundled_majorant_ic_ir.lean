-- Prove2me | solution 1 for MultiItemRev.BundlingOpt.bundled_majorant_ic_ir
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:08:13.831072+00:00
-- url     : https://prove2.me/submissions/f1f8919f-fc8a-48f8-96c6-0b4266b16d18

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
import Definitions.Def_MultiItemRev_BundlingOpt_Bundling
open MeasureTheory
open scoped NNReal ENNReal

open MultiItemRev.BundlingOpt in
theorem solution (M : Mechanism (Fin 2)) (hM : IsAdmissible M)
    (hsym : IsSymmetric M) (a : ℝ≥0) :
    IsFeasible (bundledMajorant M a) ∧
      (∀ x x' : Fin 2 → ℝ≥0, (∀ i, a ≤ x i) → (∀ i, a ≤ x' i) →
        ∑ i, (bundledMajorant M a).q x' i * (x i : ℝ) - (bundledMajorant M a).s x' ≤
          buyerPayoff (bundledMajorant M a) x) ∧
      (∀ x : Fin 2 → ℝ≥0, (∀ i, a ≤ x i) → 0 ≤ buyerPayoff (bundledMajorant M a) x) ∧
      (∀ x x' : Fin 2 → ℝ≥0, x 0 + x 1 = x' 0 + x' 1 →
        (bundledMajorant M a).q x = (bundledMajorant M a).q x' ∧
          (bundledMajorant M a).s x = (bundledMajorant M a).s x') := by
  obtain ⟨hF, hIC, hIR, _⟩ := hM
  have hpay : ∀ x, buyerPayoff (bundledMajorant M a) x = buyerPayoff M ![x 0 + x 1 - a, a] := by
    intro x
    simp only [buyerPayoff, bundledMajorant]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x i
    exact hF _ 0
  · intro x x' hx hx'
    rw [hpay]
    have h := hIC ![x 0 + x 1 - a, a] ![x' 0 + x' 1 - a, a]
    have ha1 : a ≤ x 0 + x 1 := le_trans (hx 0) le_self_add
    have ha2 : a ≤ x' 0 + x' 1 := le_trans (hx' 0) le_self_add
    simp only [buyerPayoff, bundledMajorant, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons] at h ⊢
    have c1 : ((x 0 + x 1 - a : ℝ≥0) : ℝ) = (x 0 : ℝ) + x 1 - a := by
      rw [NNReal.coe_sub ha1, NNReal.coe_add]
    have c2 : ((x' 0 + x' 1 - a : ℝ≥0) : ℝ) = (x' 0 : ℝ) + x' 1 - a := by
      rw [NNReal.coe_sub ha2, NNReal.coe_add]
    simp only [c1, c2] at h ⊢
    linarith
  · intro x _
    rw [hpay]
    exact hIR _
  · intro x x' h
    have hy : (![x 0 + x 1 - a, a] : Fin 2 → ℝ≥0) = ![x' 0 + x' 1 - a, a] := by rw [h]
    have hr : ((x 0 : ℝ) + x 1) = x' 0 + x' 1 := by exact_mod_cast h
    constructor
    · funext i
      simp only [bundledMajorant]
      rw [hy]
    · simp only [bundledMajorant, Fin.sum_univ_two]
      rw [hy, ← mul_add, ← mul_add, hr]
