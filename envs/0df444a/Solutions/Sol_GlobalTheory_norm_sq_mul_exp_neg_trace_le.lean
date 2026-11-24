-- Prove2me | solution 1 for GlobalTheory.norm_sq_mul_exp_neg_trace_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:28:10.458938+00:00
-- url     : https://prove2.me/submissions/905b6680-edc6-499f-a4d0-2d762754b5c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormSqMulExpNegTraceLe
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_prod_emb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : ℝ), 0 < δ →
    ∃ C : ℝ, ∀ x : F, (∀ τ : Emb F, 0 < τ x) →
      |(Algebra.norm ℚ x : ℝ)| ^ 2 * Real.exp (-δ * ∑ τ : Emb F, τ x) ≤
        C * Real.exp (-(δ / 2) * ∑ τ : Emb F, τ x) := by
  intro F _ _ _ δ hδ
  set n := 2 * Fintype.card (Emb F) with hn
  refine ⟨(n.factorial : ℝ) * (2 / δ) ^ n, fun x hx => ?_⟩
  set T := ∑ τ : Emb F, τ x with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun τ _ => (hx τ).le
  have hnorm : ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ τ : Emb F, τ x := by
    have h := prod_emb x
    have h' : ((∏ τ : Emb F, τ x : ℝ) : ℂ) = (((Algebra.norm ℚ x : ℚ) : ℝ) : ℂ) := by
      rw [ofReal_prod, h]; simp
    exact_mod_cast h'.symm
  have hprod : |((Algebra.norm ℚ x : ℚ) : ℝ)| ≤ T ^ Fintype.card (Emb F) := by
    rw [hnorm, abs_of_nonneg (Finset.prod_nonneg fun τ _ => (hx τ).le)]
    calc ∏ τ : Emb F, τ x ≤ ∏ _τ : Emb F, T :=
          Finset.prod_le_prod (fun τ _ => (hx τ).le) (fun τ _ =>
            Finset.single_le_sum (f := fun σ : Emb F => σ x) (fun σ _ => (hx σ).le) (Finset.mem_univ τ))
      _ = T ^ Fintype.card (Emb F) := by rw [Finset.prod_const, Finset.card_univ]
  have hsq : |((Algebra.norm ℚ x : ℚ) : ℝ)| ^ 2 ≤ T ^ n := by
    calc _ ≤ (T ^ Fintype.card (Emb F)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hprod 2
      _ = T ^ n := by rw [← pow_mul, mul_comm]
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hexp : (δ * T / 2) ^ n / n.factorial ≤ Real.exp (δ * T / 2) :=
    Real.pow_div_factorial_le_exp _ (by positivity) n
  have e2 : (δ * T / 2) ^ n ≤ Real.exp (δ * T / 2) * n.factorial := (div_le_iff₀ hf).1 hexp
  have e1 : T ^ n = (2 / δ) ^ n * (δ * T / 2) ^ n := by
    rw [← mul_pow]; congr 1; field_simp
  have hTn : T ^ n ≤ (n.factorial : ℝ) * (2 / δ) ^ n * Real.exp (δ * T / 2) := by
    rw [e1]
    calc _ ≤ (2 / δ) ^ n * (Real.exp (δ * T / 2) * n.factorial) :=
          mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = _ := by ring
  calc |((Algebra.norm ℚ x : ℚ) : ℝ)| ^ 2 * Real.exp (-δ * T)
        ≤ T ^ n * Real.exp (-δ * T) := mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    _ ≤ (n.factorial : ℝ) * (2 / δ) ^ n * Real.exp (δ * T / 2) * Real.exp (-δ * T) :=
          mul_le_mul_of_nonneg_right hTn (Real.exp_pos _).le
    _ = (n.factorial : ℝ) * (2 / δ) ^ n * Real.exp (-(δ / 2) * T) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
end GlobalTheory
